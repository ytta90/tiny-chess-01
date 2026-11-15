# Tiny chess engine: 0x88 board, alpha-beta + quiescence, transposition table,
# null-move pruning, LMR, killer/history ordering, procedural piece-square
# tables. Fixed node budget per move (deterministic: same nodes, same move).
import json, os, random, sys
import urllib.error, urllib.request

ENV_URL = os.environ.get("MAKEFUN_ENV_URL") or sys.exit("no URL")

V = [0, 100, 320, 330, 500, 900, 0]          # piece values by type
ND = (-33, -31, -18, -14, 14, 18, 31, 33)    # knight offsets (0x88)
KD = (-17, -16, -15, -1, 1, 15, 16, 17)      # king offsets
RD = (-16, -1, 1, 16)
BD = (-17, -15, 15, 17)
MATE = 100000
INF = 1000000

# ---------------- board state ----------------
B = [0] * 128          # 0x88 board, signed piece codes (+ white, - black)
P = [[], []]           # piece lists per side: P[0] white squares, P[1] black
IX = [-1] * 128        # IX[sq] = index of sq in its side's piece list
KS = [4, 116]          # king squares
S = 0                  # side to move: 0 white, 1 black
CA = 0                 # castling rights: 1 K, 2 Q, 4 k, 8 q
EP = -1                # en passant target square, or -1
MAT = [0, 0]           # material per side (excl. kings)
NM = [0, 0]            # non-pawn piece counts per side
BC = [0, 0]            # bishop counts per side
KEY = 0                # zobrist key
N = 0                  # nodes searched this move
BDG = 150000           # node budget per move (tuned by benchmark)
TT = {}                # transposition table: key -> (depth, flag, value, move)
KILL = [[0, 0] for _ in range(256)]   # killer moves per ply
HIST = [[0] * 128 for _ in range(128)]  # history [from][to]

# zobrist keys, deterministic
_rng = random.Random(987654321)
Z = [[_rng.getrandbits(64) for _ in range(128)] for _ in range(13)]
ZS = _rng.getrandbits(64)
ZC = [_rng.getrandbits(64) for _ in range(16)]
ZE = [_rng.getrandbits(64) for _ in range(8)]

# castling-rights mask per square: moving from/to a corner clears a right
CM = [15] * 128
CM[0] = 13; CM[7] = 14; CM[112] = 7; CM[119] = 11; CM[4] = 12; CM[116] = 3

# ---------------- piece-square tables (procedural, white perspective) ----------------
def _pst():
    T = [[0] * 128 for _ in range(8)]  # T[piece][sq]; index 6 king-mid, 7 king-end
    for sq in range(128):
        if sq & 0x88:
            continue
        f = sq & 7
        r = sq >> 4
        c = (3 - abs(f - 3.5)) + (3 - abs(r - 3.5))  # centrality 0..7
        T[1][sq] = r * 10 + int((3 - abs(f - 3.5)) * 3)          # pawn: advance + centre
        T[2][sq] = int(c * 6) - (10 if r == 0 else 0)            # knight
        T[3][sq] = int(c * 5)                                     # bishop
        T[4][sq] = (25 if r == 6 else 0) + int(c * 2)             # rook: 7th rank
        T[5][sq] = int(c * 3)                                     # queen
        T[6][sq] = -r * 8                                         # king mid: stay home
        T[7][sq] = int(c * 8)                                     # king end: centralise
    return T

T = _pst()

def ev():
    """Static eval from the side-to-move's perspective."""
    eg = MAT[0] + MAT[1] < 2600
    k = 7 if eg else 6
    s = MAT[0] - MAT[1]
    for sq in P[0]:
        p = B[sq]
        s += T[k][sq] if p == 6 else T[p][sq]
    for sq in P[1]:
        p = -B[sq]
        s -= T[k][sq ^ 0x70] if p == 6 else T[p][sq ^ 0x70]
    if BC[0] == 2:
        s += 30
    if BC[1] == 2:
        s -= 30
    # king safety: friendly pawns shielding the 3 squares in front of the king
    for sd in (0, 1):
        ksq = KS[sd]
        dd = 16 if sd == 0 else -16
        sh = 0
        for o in (dd - 1, dd, dd + 1):
            q = ksq + o
            if not (q & 0x88) and B[q] == (1 if sd == 0 else -1):
                sh += 1
        s += (sh - 2) * 25 if sd == 0 else -(sh - 2) * 25
    sc = s if S == 0 else -s
    return sc + 10  # tempo

# ---------------- attack test ----------------
def attacked(sq, by):
    """Is sq attacked by side `by` (0 white, 1 black)?"""
    c = 1 if by == 0 else -1
    # pawns: a white pawn on sq-15/sq-17 attacks sq; black on sq+15/sq+17
    for o in ((-15, -17) if by == 0 else (15, 17)):
        t = sq + o
        if not (t & 0x88) and B[t] == c:
            return True
    for o in ND:
        t = sq + o
        if not (t & 0x88) and B[t] == 2 * c:
            return True
    for o in KD:
        t = sq + o
        if not (t & 0x88) and B[t] == 6 * c:
            return True
    for o in RD:
        t = sq + o
        while not (t & 0x88):
            p = B[t]
            if p:
                if p == 4 * c or p == 5 * c:
                    return True
                break
            t += o
    for o in BD:
        t = sq + o
        while not (t & 0x88):
            p = B[t]
            if p:
                if p == 3 * c or p == 5 * c:
                    return True
                break
            t += o
    return False

# ---------------- move make / unmake ----------------
# move int: from | to<<7 | promo<<14 ; undo stack entries:
# (move, captured, cap_sq, old_CA, old_EP, old_KEY)
UNDO = []

def make(m):
    global S, CA, EP, KEY
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 15
    mover = B[f]
    cap = B[t]
    capsq = t
    # en passant capture
    if mover == (1 if S == 0 else -1) and t == EP and cap == 0:
        capsq = t - 16 if S == 0 else t + 16
        cap = B[capsq]
    old_ca, old_ep, old_key = CA, EP, KEY
    KEY ^= Z[mover + 6][f]
    if cap:
        KEY ^= Z[cap + 6][capsq]
        B[capsq] = 0  # clear the captured piece (en passant: capsq != t)
        MAT[1 - S] -= V[abs(cap)]
        if abs(cap) > 1:
            NM[1 - S] -= 1
        if abs(cap) == 3:
            BC[1 - S] -= 1
        # remove captured from its list
        j = IX[capsq]
        lst = P[1 - S]
        last = lst.pop()
        if j < len(lst):
            lst[j] = last
            IX[last] = j
        IX[capsq] = -1
    # move the piece in its list
    P[S][IX[f]] = t
    IX[t] = IX[f]
    IX[f] = -1
    B[t] = p * (1 if S == 0 else -1) if p else mover
    B[f] = 0
    KEY ^= Z[B[t] + 6][t]
    if p:
        MAT[S] += V[p] - 100
        if p > 1:
            NM[S] += 1
        if p == 3:
            BC[S] += 1
    if abs(mover) == 6:
        KS[S] = t
        # castling: move the rook too
        if t - f == 2:
            _rook_move(f + 3, f + 1)
        elif f - t == 2:
            _rook_move(f - 4, f - 1)
    CA &= CM[f] & CM[t]
    KEY ^= ZC[old_ca] ^ ZC[CA]
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    # new en passant square on a double pawn push
    if abs(mover) == 1 and abs(t - f) == 32:
        EP = f + 16 if S == 0 else f - 16
        KEY ^= ZE[EP & 7]
    else:
        EP = -1
    KEY ^= ZS
    S ^= 1
    UNDO.append((m, cap, capsq, old_ca, old_ep, old_key))

def _rook_move(f, t):
    """Move a rook (castling) on the board; updates lists and key."""
    global KEY
    r = B[f]
    KEY ^= Z[r + 6][f] ^ Z[r + 6][t]
    P[S][IX[f]] = t
    IX[t] = IX[f]
    IX[f] = -1
    B[t] = r
    B[f] = 0

def unmake():
    global S, CA, EP, KEY
    m, cap, capsq, old_ca, old_ep, old_key = UNDO.pop()
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 15
    S ^= 1
    mover = B[t]
    if p:
        MAT[S] -= V[p] - 100
        if p > 1:
            NM[S] -= 1
        if p == 3:
            BC[S] -= 1
        mover = 1 if S == 0 else -1
    if abs(mover) == 6:
        KS[S] = f
        if t - f == 2:
            _rook_move(f + 1, f + 3)
        elif f - t == 2:
            _rook_move(f - 1, f - 4)
    P[S][IX[t]] = f
    IX[f] = IX[t]
    IX[t] = -1
    B[f] = mover
    B[t] = 0
    if cap:
        B[capsq] = cap
        P[1 - S].append(capsq)
        IX[capsq] = len(P[1 - S]) - 1
        MAT[1 - S] += V[abs(cap)]
        if abs(cap) > 1:
            NM[1 - S] += 1
        if abs(cap) == 3:
            BC[1 - S] += 1
    CA, EP, KEY = old_ca, old_ep, old_key

def do_null():
    global S, EP, KEY
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    EP = -1
    KEY ^= ZS
    S ^= 1

def undo_null(old_ep, old_key):
    global S, EP, KEY
    S ^= 1
    EP, KEY = old_ep, old_key

# ---------------- move generation (pseudo-legal) ----------------
def gen(caps_only=False):
    ms = []
    c = 1 if S == 0 else -1
    d = 16 if S == 0 else -16
    start_rank = 1 if S == 0 else 6
    promo_rank = 7 if S == 0 else 0
    for sq in P[S]:
        p = B[sq]
        a = abs(p)
        if a == 1:
            t = sq + d
            if not (t & 0x88) and B[t] == 0:
                if (t >> 4) == promo_rank:
                    for pr in (5, 4, 3, 2):
                        ms.append(sq | (t << 7) | (pr << 14))
                else:
                    if not caps_only:
                        ms.append(sq | (t << 7))
                    if (sq >> 4) == start_rank:
                        t2 = t + d
                        if B[t2] == 0 and not caps_only:
                            ms.append(sq | (t2 << 7))
            for o in (d - 1, d + 1):
                t = sq + o
                if t & 0x88:
                    continue
                q = B[t]
                if q and q * c < 0:
                    if (t >> 4) == promo_rank:
                        for pr in (5, 4, 3, 2):
                            ms.append(sq | (t << 7) | (pr << 14))
                    else:
                        ms.append(sq | (t << 7))
                elif t == EP:
                    ms.append(sq | (t << 7))
        elif a == 2 or a == 6:
            for o in ND if a == 2 else KD:
                t = sq + o
                if t & 0x88:
                    continue
                q = B[t]
                if q == 0:
                    if not caps_only:
                        ms.append(sq | (t << 7))
                elif q * c < 0:
                    ms.append(sq | (t << 7))
        else:
            for o in (RD if a == 4 else BD if a == 3 else RD + BD):
                t = sq + o
                while not (t & 0x88):
                    q = B[t]
                    if q == 0:
                        if not caps_only:
                            ms.append(sq | (t << 7))
                    else:
                        if q * c < 0:
                            ms.append(sq | (t << 7))
                        break
                    t += o
    if not caps_only and abs(B[KS[S]]) == 6:
        _castle(ms, c)
    return ms

def _castle(ms, c):
    """Add castling moves if legal (king not in check, transit safe)."""
    k = KS[S]
    if S == 0:
        if CA & 1 and B[5] == 0 and B[6] == 0 and B[7] == 4 and not attacked(4, 1) and not attacked(5, 1) and not attacked(6, 1):
            ms.append(4 | (6 << 7))
        if CA & 2 and B[3] == 0 and B[2] == 0 and B[1] == 0 and B[0] == 4 and not attacked(4, 1) and not attacked(3, 1) and not attacked(2, 1):
            ms.append(4 | (2 << 7))
    else:
        if CA & 4 and B[117] == 0 and B[118] == 0 and B[119] == -4 and not attacked(116, 0) and not attacked(117, 0) and not attacked(118, 0):
            ms.append(116 | (118 << 7))
        if CA & 8 and B[115] == 0 and B[114] == 0 and B[113] == 0 and B[112] == -4 and not attacked(116, 0) and not attacked(115, 0) and not attacked(114, 0):
            ms.append(116 | (114 << 7))

# ---------------- search ----------------
class Abort(Exception):
    pass

def qs(a, b, ply):
    global N
    N += 1
    if N > BDG:
        raise Abort
    if attacked(KS[S], 1 - S):
        # in check: search all evasions, no stand pat
        best = -MATE + ply
        for m in gen():
            make(m)
            if attacked(KS[S ^ 1], S):
                unmake()
                continue
            s = -qs(-b, -a, ply + 1)
            unmake()
            if s > best:
                best = s
            if s > a:
                a = s
            if a >= b:
                return b
        return best if best > -MATE + ply else -MATE + ply
    s = ev()
    if s >= b:
        return b
    if s > a:
        a = s
    for m in _order_caps(gen(True)):
        make(m)
        if attacked(KS[S ^ 1], S):
            unmake()
            continue
        s = -qs(-b, -a, ply + 1)
        unmake()
        if s > a:
            a = s
        if a >= b:
            return b
    return a

def _order_caps(ms):
    def sc(m):
        t = (m >> 7) & 127
        v = B[t]
        if v == 0 and (m >> 14) & 15 == 0:
            # en passant
            v = 1
        return -(10 * V[abs(v)] - V[abs(B[m & 127])] // 10)
    ms.sort(key=sc)
    return ms

def sr(d, a, b, ply):
    global N
    N += 1
    if N > BDG:
        raise Abort
    if len(P[0]) + len(P[1]) <= 4:
        # insufficient material: K v K, K+minor v K, K+B v K+B
        pcs = [abs(B[s]) for s in P[0] if s != KS[0]] + [abs(B[s]) for s in P[1] if s != KS[1]]
        if not pcs or (len(pcs) == 1 and pcs[0] in (2, 3)) or pcs == [3, 3]:
            return 0
    # transposition table probe
    e = TT.get(KEY)
    if e is not None and e[0] >= d:
        v = e[2]
        if v > 90000:
            v -= ply
        elif v < -90000:
            v += ply
        if e[1] == 0:
            return v
        if e[1] == 1 and v >= b:
            return v
        if e[1] == 2 and v <= a:
            return v
    ck = attacked(KS[S], 1 - S)
    if d <= 0:
        if ck:
            d = 1
        else:
            return qs(a, b, ply)
    ao = a  # alpha on entry, for the TT flag
    # null-move pruning
    if d >= 3 and not ck and NM[S] > 0:
        oep, okey = EP, KEY
        do_null()
        s = -sr(d - 3, -b, -a, ply + 1)
        undo_null(oep, okey)
        if s >= b:
            return b
    tt_move = e[3] if e is not None else 0
    ms = _order(gen(), tt_move, ply)
    best = -INF
    bestm = 0
    flag = 2
    cnt = 0
    for m in ms:
        tgt = B[(m >> 7) & 127]
        make(m)
        if attacked(KS[S ^ 1], S):
            unmake()
            continue
        cnt += 1
        if cnt == 1:
            s = -sr(d - 1, -b, -a, ply + 1)
        elif d >= 3 and cnt > 3 and tgt == 0 and ((m >> 14) & 15) == 0 and not ck:
            s = -sr(d - 2, -b, -a, ply + 1)  # LMR
            if s > a:
                s = -sr(d - 1, -b, -a, ply + 1)
        else:
            s = -sr(d - 1, -b, -a, ply + 1)
        unmake()
        if s > best:
            best = s
            bestm = m
        if s > a:
            a = s
        if a >= b:
            flag = 1
            if ply < 128 and tgt == 0 and ((m >> 14) & 15) == 0:
                KILL[ply][1] = KILL[ply][0]
                KILL[ply][0] = m
                HIST[m & 127][(m >> 7) & 127] += d * d
            break
    if cnt == 0:
        return -MATE + ply if ck else 0
    # store in TT (mate scores adjusted by ply)
    v = best
    if v > 90000:
        v += ply
    elif v < -90000:
        v -= ply
    if len(TT) > 300000:
        TT.clear()
    fl = flag if flag == 1 else (0 if best > ao else 2)
    TT[KEY] = (d, fl, v, bestm)
    return best

def _order(ms, tt_move, ply):
    def sc(m):
        f = m & 127
        t = (m >> 7) & 127
        if m == tt_move:
            return -1000000
        v = B[t]
        if v:
            return -(10 * V[abs(v)] - V[abs(B[f])] // 10)
        if m == KILL[ply][0]:
            return -9000
        if m == KILL[ply][1]:
            return -8000
        return -HIST[f][t]
    ms.sort(key=sc)
    return ms

def root_search(moves, depth):
    """Search root moves (int list) at depth; returns ordered [(score, move)]."""
    out = []
    a = -INF
    for m in moves:
        make(m)
        s = -sr(depth - 1, -INF, -a, 1)
        unmake()
        out.append((s, m))
        if s > a:
            a = s
    out.sort(key=lambda x: -x[0])
    return out

# ---------------- FEN / UCI helpers ----------------
def parse_fen(fen):
    global S, CA, EP, KEY, MAT, NM, BC
    parts = fen.split()
    for i in range(128):
        B[i] = 0
    P[0] = []
    P[1] = []
    for i in range(128):
        IX[i] = -1
    MAT[0] = MAT[1] = 0
    NM[0] = NM[1] = 0
    BC[0] = BC[1] = 0
    code = {"p": 1, "n": 2, "b": 3, "r": 4, "q": 5, "k": 6}
    for i, row in enumerate(parts[0].split("/")):
        f = 0
        for ch in row:
            if ch.isdigit():
                f += int(ch)
            else:
                sq = (7 - i) * 16 + f
                v = code[ch.lower()] * (1 if ch.isupper() else -1)
                B[sq] = v
                side = 0 if v > 0 else 1
                IX[sq] = len(P[side])
                P[side].append(sq)
                if abs(v) == 6:
                    KS[side] = sq
                else:
                    MAT[side] += V[abs(v)]
                    if abs(v) > 1:
                        NM[side] += 1
                    if abs(v) == 3:
                        BC[side] += 1
                f += 1
    S = 0 if parts[1] == "w" else 1
    CA = 0
    if len(parts) > 2:
        for ch in parts[2]:
            CA |= {"K": 1, "Q": 2, "k": 4, "q": 8}.get(ch, 0)
    EP = -1
    if len(parts) > 3 and parts[3] != "-":
        EP = (ord(parts[3][0]) - 97) + (int(parts[3][1]) - 1) * 16
    UNDO.clear()
    TT.clear()
    KEY = 0
    for sq in P[0]:
        KEY ^= Z[B[sq] + 6][sq]
    for sq in P[1]:
        KEY ^= Z[B[sq] + 6][sq]
    KEY ^= ZC[CA]
    if EP >= 0:
        KEY ^= ZE[EP & 7]
    if S == 1:
        KEY ^= ZS

def uci_to_move(u):
    f = (ord(u[0]) - 97) + (int(u[1]) - 1) * 16
    t = (ord(u[2]) - 97) + (int(u[3]) - 1) * 16
    p = {"q": 5, "r": 4, "b": 3, "n": 2}.get(u[4], 0) if len(u) == 5 else 0
    return f | (t << 7) | (p << 14)

def move_to_uci(m):
    f = m & 127
    t = (m >> 7) & 127
    p = (m >> 14) & 15
    s = "abcdefgh"[f & 7] + str((f >> 4) + 1) + "abcdefgh"[t & 7] + str((t >> 4) + 1)
    if p:
        s += "qrbn"[5 - p] if p in (5, 4, 3, 2) else ""
    return s

def choose(fen, legal_uci):
    """Pick the best move for this position within the node budget."""
    global N, BDG
    parse_fen(fen)
    moves = [uci_to_move(u) for u in legal_uci]
    if len(moves) == 1:
        return move_to_uci(moves[0])
    N = 0
    # order root moves by capture value first
    moves.sort(key=lambda m: -(10 * V[abs(B[(m >> 7) & 127])] if B[(m >> 7) & 127] else 0))
    best = moves[0]
    d = 1
    while True:
        try:
            scored = root_search(moves, d)
        except Abort:
            break
        best = scored[0][1]
        # next iteration: search best-first
        moves = [m for _, m in scored]
        if N > BDG * 0.75:
            break
        # stop early on a forced mate found
        if scored[0][0] > MATE - 1000:
            break
        d += 1
        if d > 64:
            break
    return move_to_uci(best)

# ---------------- driver ----------------
def post(path, body):
    try:
        req = urllib.request.Request(ENV_URL + path, data=json.dumps(body).encode(), headers={"content-type": "application/json"})
        with urllib.request.urlopen(req) as res:
            return json.load(res)
    except Exception:
        return {"status": "error"}

def main():
    while True:
        g = post("/game", {})
        if g.get("status") == "done":
            break
        while g.get("status") == "your_move":
            try:
                mv = choose(g["fen"], g["legal_moves"])
            except Exception as e:
                print("fail", e, file=sys.stderr)
                mv = g["legal_moves"][0]
            r = {"status": "error"}
            for m in [mv] + [x for x in g["legal_moves"] if x != mv]:
                r = post("/move", {"game": g["game"], "move": m})
                if r.get("status") != "error":
                    break
            if r.get("status") == "error":
                r = post("/resign", {"game": g["game"]})
            g = r
    print(f"done: {g.get('wins')} won, {g.get('draws')} drawn, {g.get('losses')} lost", file=sys.stderr)

if __name__ == "__main__":
    main()
