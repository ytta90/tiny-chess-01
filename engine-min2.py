import json,os,random,sys
import urllib.error,urllib.request
dc =os.environ.get ("MAKEFUN_ENV_URL")or sys.exit ("no URL")
af =[0,100,320,330,500,900,0]
cs =(-33,-31,-18,-14,14,18,31,33)
cr =(-17,-16,-15,-1,1,15,16,17)
ca =(-16,-1,1,16)
bz =(-17,-15,15,17)
ba =100000
bu =1000000
b =[0]*128
p =[[],[]]
t =[-1]*128
y =[4,116]
d =0
ad =0
s =-1
ac =[0,0]
am =[0,0]
ah =[0,0]
m =0
av =0
bt =150000
bb ={}
az =[[0,0]for aq in range (256)]
co =[[0]*128 for aq in range (128)]
bg =random.Random (987654321)
ap =[[bg.getrandbits (64)for aq in range (128)]for aq in range (13)]
cc =bg.getrandbits (64)
cb =[bg.getrandbits (64)for aq in range (16)]
bk =[bg.getrandbits (64)for aq in range (8)]
al =[15]*128
al [0]=13 ;al [7]=14 ;al [112]=7 ;al [119]=11 ;al [4]=12 ;al [116]=3
def di ():
    z =[[0]*128 for aq in range (8)]
    for c in range (128):
        if c &0x88:
            continue
        e =c &7
        v =c >>4
        r =(3 -abs (e -3.5))+(3 -abs (v -3.5))
        z [1][c]=v *10 +int ((3 -abs (e -3.5))*3)
        z [2][c]=int (r *6)-(10 if v ==0 else 0)
        z [3][c]=int (r *5)
        z [4][c]=(25 if v ==6 else 0)+int (r *2)
        z [5][c]=int (r *3)
        z [6][c]=-v *8
        z [7][c]=int (r *8)
    return z
z =di ()
def dv ():
    du =ac [0]+ac [1]<2600
    cj =7 if du else 6
    g =ac [0]-ac [1]
    for c in p [0]:
        i =b [c]
        g +=z [cj][c]if i ==6 else z [i][c]
    for c in p [1]:
        i =-b [c]
        g -=z [cj][c ^0x70]if i ==6 else z [i][c ^0x70]
    if ah [0]==2:
        g +=30
    if ah [1]==2:
        g -=30
    for bm in (0,1):
        do =y [bm]
        cd =16 if bm ==0 else -16
        ch =0
        for o in (cd -1,cd,cd +1):
            ae =do +o
            if not (ae &0x88)and b [ae]==(1 if bm ==0 else -1):
                ch +=1
        g +=(ch -2)*25 if bm ==0 else -(ch -2)*25
    bc =g if d ==0 else -g
    return bc +10
def u (c,ct):
    r =1 if ct ==0 else -1
    for o in ((-15,-17)if ct ==0 else (15,17)):
        a =c +o
        if not (a &0x88)and b [a]==r:
            return True
    for o in cs:
        a =c +o
        if not (a &0x88)and b [a]==2 *r:
            return True
    for o in cr:
        a =c +o
        if not (a &0x88)and b [a]==6 *r:
            return True
    for o in ca:
        a =c +o
        while not (a &0x88):
            i =b [a]
            if i:
                if i ==4 *r or i ==5 *r:
                    return True
                break
            a +=o
    for o in bz:
        a =c +o
        while not (a &0x88):
            i =b [a]
            if i:
                if i ==3 *r or i ==5 *r:
                    return True
                break
            a +=o
    return False
bq =[]
def bh (f):
    global d,ad,s,m
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    ag =b [e]
    w =b [a]
    ab =a
    if ag ==(1 if d ==0 else -1)and a ==s and w ==0:
        ab =a -16 if d ==0 else a +16
        w =b [ab]
    bf,ay,ax =ad,s,m
    m ^=ap [ag +6][e]
    if w:
        m ^=ap [w +6][ab]
        b [ab]=0
        ac [1 -d]-=af [abs (w)]
        if abs (w)>1:
            am [1 -d]-=1
        if abs (w)==3:
            ah [1 -d]-=1
        ci =t [ab]
        bx =p [1 -d]
        cp =bx.pop ()
        if ci <len (bx):
            bx [ci]=cp
            t [cp]=ci
        t [ab]=-1
    p [d][t [e]]=a
    t [a]=t [e]
    t [e]=-1
    b [a]=i *(1 if d ==0 else -1)if i else ag
    b [e]=0
    m ^=ap [b [a]+6][a]
    if i:
        ac [d]+=af [i]-100
        if i >1:
            am [d]+=1
        if i ==3:
            ah [d]+=1
    if abs (ag)==6:
        y [d]=a
        if a -e ==2:
            be (e +3,e +1)
        elif e -a ==2:
            be (e -4,e -1)
    ad &=al [e]&al [a]
    m ^=cb [bf]^cb [ad]
    if s >=0:
        m ^=bk [s &7]
    if abs (ag)==1 and abs (a -e)==32:
        s =e +16 if d ==0 else e -16
        m ^=bk [s &7]
    else:
        s =-1
    m ^=cc
    d ^=1
    bq.append ((f,w,ab,bf,ay,ax))
def be (e,a):
    global m
    v =b [e]
    m ^=ap [v +6][e]^ap [v +6][a]
    p [d][t [e]]=a
    t [a]=t [e]
    t [e]=-1
    b [a]=v
    b [e]=0
def ao ():
    global d,ad,s,m
    f,w,ab,bf,ay,ax =bq.pop ()
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    d ^=1
    ag =b [a]
    if i:
        ac [d]-=af [i]-100
        if i >1:
            am [d]-=1
        if i ==3:
            ah [d]-=1
        ag =1 if d ==0 else -1
    if abs (ag)==6:
        y [d]=e
        if a -e ==2:
            be (e +1,e +3)
        elif e -a ==2:
            be (e -1,e -4)
    p [d][t [a]]=e
    t [e]=t [a]
    t [a]=-1
    b [e]=ag
    b [a]=0
    if w:
        b [ab]=w
        p [1 -d].append (ab)
        t [ab]=len (p [1 -d])-1
        ac [1 -d]+=af [abs (w)]
        if abs (w)>1:
            am [1 -d]+=1
        if abs (w)==3:
            ah [1 -d]+=1
    ad,s,m =bf,ay,ax
def de ():
    global d,s,m
    if s >=0:
        m ^=bk [s &7]
    s =-1
    m ^=cc
    d ^=1
def db (ay,ax):
    global d,s,m
    d ^=1
    s,m =ay,ax
def bw (aw =False):
    l =[]
    r =1 if d ==0 else -1
    n =16 if d ==0 else -16
    cy =1 if d ==0 else 6
    cl =7 if d ==0 else 0
    for c in p [d]:
        i =b [c]
        h =abs (i)
        if h ==1:
            a =c +n
            if not (a &0x88)and b [a]==0:
                if (a >>4)==cl:
                    for cf in (5,4,3,2):
                        l.append (c |(a <<7)|(cf <<14))
                else:
                    if not aw:
                        l.append (c |(a <<7))
                    if (c >>4)==cy:
                        cu =a +n
                        if b [cu]==0 and not aw:
                            l.append (c |(cu <<7))
            for o in (n -1,n +1):
                a =c +o
                if a &0x88:
                    continue
                ae =b [a]
                if ae and ae *r <0:
                    if (a >>4)==cl:
                        for cf in (5,4,3,2):
                            l.append (c |(a <<7)|(cf <<14))
                    else:
                        l.append (c |(a <<7))
                elif a ==s:
                    l.append (c |(a <<7))
        elif h ==2 or h ==6:
            for o in cs if h ==2 else cr:
                a =c +o
                if a &0x88:
                    continue
                ae =b [a]
                if ae ==0:
                    if not aw:
                        l.append (c |(a <<7))
                elif ae *r <0:
                    l.append (c |(a <<7))
        else:
            for o in (ca if h ==4 else bz if h ==3 else ca +bz):
                a =c +o
                while not (a &0x88):
                    ae =b [a]
                    if ae ==0:
                        if not aw:
                            l.append (c |(a <<7))
                    else:
                        if ae *r <0:
                            l.append (c |(a <<7))
                        break
                    a +=o
    if not aw and abs (b [y [d]])==6:
        dd (l,r)
    return l
def dd (l,r):
    cj =y [d]
    if d ==0:
        if ad &1 and b [5]==0 and b [6]==0 and b [7]==4 and not u (4,1)and not u (5,1)and not u (6,1):
            l.append (4 |(6 <<7))
        if ad &2 and b [3]==0 and b [2]==0 and b [1]==0 and b [0]==4 and not u (4,1)and not u (3,1)and not u (2,1):
            l.append (4 |(2 <<7))
    else:
        if ad &4 and b [117]==0 and b [118]==0 and b [119]==-4 and not u (116,0)and not u (117,0)and not u (118,0):
            l.append (116 |(118 <<7))
        if ad &8 and b [115]==0 and b [114]==0 and b [113]==0 and b [112]==-4 and not u (116,0)and not u (115,0)and not u (114,0):
            l.append (116 |(114 <<7))
class cm (Exception):
    pass
def cg (h,q,k):
    global av
    av +=1
    if av >bt:
        raise cm
    if u (y [d],1 -d):
        x =-ba +k
        for f in bw ():
            bh (f)
            if u (y [d ^1],d):
                ao ()
                continue
            g =-cg (-q,-h,k +1)
            ao ()
            if g >x:
                x =g
            if g >h:
                h =g
            if h >=q:
                return q
        return x if x >-ba +k else -ba +k
    g =dv ()
    if g >=q:
        return q
    if g >h:
        h =g
    for f in cv (bw (True)):
        bh (f)
        if u (y [d ^1],d):
            ao ()
            continue
        g =-cg (-q,-h,k +1)
        ao ()
        if g >h:
            h =g
        if h >=q:
            return q
    return h
def cv (l):
    def bc (f):
        a =(f >>7)&127
        j =b [a]
        if j ==0 and (f >>14)&15 ==0:
            j =1
        return -(10 *af [abs (j)]-af [abs (b [f &127])]//10)
    l.sort (key =bc)
    return l
def au (n,h,q,k):
    global av
    av +=1
    if av >bt:
        raise cm
    if len (p [0])+len (p [1])<=4:
        bj =[abs (b [g])for g in p [0]if g !=y [0]]+[abs (b [g])for g in p [1]if g !=y [1]]
        if not bj or (len (bj)==1 and bj [0]in (2,3))or bj ==[3,3]:
            return 0
    ai =bb.get (m)
    if ai is not None and ai [0]>=n:
        j =ai [2]
        if j >90000:
            j -=k
        elif j <-90000:
            j +=k
        if ai [1]==0:
            return j
        if ai [1]==1 and j >=q:
            return j
        if ai [1]==2 and j <=h:
            return j
    bl =u (y [d],1 -d)
    if n <=0:
        if bl:
            n =1
        else:
            return cg (h,q,k)
    dt =h
    if n >=3 and not bl and am [d]>0:
        dp,dm =s,m
        de ()
        g =-au (n -3,-q,-h,k +1)
        db (dp,dm)
        if g >=q:
            return q
    bo =ai [3]if ai is not None else 0
    l =df (bw (),bo,k)
    x =-bu
    cn =0
    br =2
    bi =0
    for f in l:
        cq =b [(f >>7)&127]
        bh (f)
        if u (y [d ^1],d):
            ao ()
            continue
        bi +=1
        if bi ==1:
            g =-au (n -1,-q,-h,k +1)
        elif n >=3 and bi >3 and cq ==0 and ((f >>14)&15)==0 and not bl:
            g =-au (n -2,-q,-h,k +1)
            if g >h:
                g =-au (n -1,-q,-h,k +1)
        else:
            g =-au (n -1,-q,-h,k +1)
        ao ()
        if g >x:
            x =g
            cn =f
        if g >h:
            h =g
        if h >=q:
            br =1
            if k <128 and cq ==0 and ((f >>14)&15)==0:
                az [k][1]=az [k][0]
                az [k][0]=f
                co [f &127][(f >>7)&127]+=n *n
            break
    if bi ==0:
        return -ba +k if bl else 0
    j =x
    if j >90000:
        j +=k
    elif j <-90000:
        j -=k
    if len (bb)>300000:
        bb.clear ()
    dw =br if br ==1 else (0 if x >dt else 2)
    bb [m]=(n,dw,j,cn)
    return x
def df (l,bo,k):
    def bc (f):
        e =f &127
        a =(f >>7)&127
        if f ==bo:
            return -1000000
        j =b [a]
        if j:
            return -(10 *af [abs (j)]-af [abs (b [e])]//10)
        if f ==az [k][0]:
            return -9000
        if f ==az [k][1]:
            return -8000
        return -co [e][a]
    l.sort (key =bc)
    return l
def cw (aj,dh):
    by =[]
    h =-bu
    for f in aj:
        bh (f)
        g =-au (dh -1,-bu,-h,1)
        ao ()
        by.append ((g,f))
        if g >h:
            h =g
    by.sort (key =lambda bn:-bn [0])
    return by
def da (bv):
    global d,ad,s,m,ac,am,ah
    ak =bv.split ()
    for bd in range (128):
        b [bd]=0
    p [0]=[]
    p [1]=[]
    for bd in range (128):
        t [bd]=-1
    ac [0]=ac [1]=0
    am [0]=am [1]=0
    ah [0]=ah [1]=0
    dk ={"p":1,"n":2,"b":3,"r":4,"q":5,"k":6 }
    for bd,ds in enumerate (ak [0].split ("/")):
        e =0
        for at in ds:
            if at.isdigit ():
                e +=int (at)
            else:
                c =(7 -bd)*16 +e
                j =dk [at.lower ()]*(1 if at.isupper ()else -1)
                b [c]=j
                ar =0 if j >0 else 1
                t [c]=len (p [ar])
                p [ar].append (c)
                if abs (j)==6:
                    y [ar]=c
                else:
                    ac [ar]+=af [abs (j)]
                    if abs (j)>1:
                        am [ar]+=1
                    if abs (j)==3:
                        ah [ar]+=1
                e +=1
    d =0 if ak [1]=="w"else 1
    ad =0
    if len (ak)>2:
        for at in ak [2]:
            ad |={"K":1,"Q":2,"k":4,"q":8 }.get (at,0)
    s =-1
    if len (ak)>3 and ak [3]!="-":
        s =(ord (ak [3][0])-97)+(int (ak [3][1])-1)*16
    bq.clear ()
    bb.clear ()
    m =0
    for c in p [0]:
        m ^=ap [b [c]+6][c]
    for c in p [1]:
        m ^=ap [b [c]+6][c]
    m ^=cb [ad]
    if s >=0:
        m ^=bk [s &7]
    if d ==1:
        m ^=cc
def cx (an):
    e =(ord (an [0])-97)+(int (an [1])-1)*16
    a =(ord (an [2])-97)+(int (an [3])-1)*16
    i ={"q":5,"r":4,"b":3,"n":2 }.get (an [4],0)if len (an)==5 else 0
    return e |(a <<7)|(i <<14)
def ck (f):
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    g ="abcdefgh"[e &7]+str ((e >>4)+1)+"abcdefgh"[a &7]+str ((a >>4)+1)
    if i:
        g +="qrbn"[5 -i]if i in (5,4,3,2)else ""
    return g
def dg (bv,cz):
    global av,bt
    da (bv)
    aj =[cx (an)for an in cz]
    if len (aj)==1:
        return ck (aj [0])
    av =0
    aj.sort (key =lambda f:-(10 *af [abs (b [(f >>7)&127])]if b [(f >>7)&127]else 0))
    x =aj [0]
    n =1
    while True:
        try:
            bp =cw (aj,n)
        except cm:
            break
        x =bp [0][1]
        aj =[f for aq,f in bp]
        if av >bt *0.75:
            break
        if bp [0][0]>ba -1000:
            break
        n +=1
        if n >64:
            break
    return ck (x)
def bs (dn,dj):
    try:
        dq =urllib.request.Request (dc +dn,data =json.dumps (dj).encode (),headers ={"content-type":"application/json"})
        with urllib.request.urlopen (dq)as dr:
            return json.load (dr)
    except Exception:
        return {"status":"error"}
def dl ():
    while True:
        aa =bs ("/game",{})
        if aa.get ("status")=="done":
            break
        while aa.get ("status")=="your_move":
            try:
                ce =dg (aa ["fen"],aa ["legal_moves"])
            except Exception as ai:
                print ("fail",ai,file =sys.stderr)
                ce =aa ["legal_moves"][0]
            v ={"status":"error"}
            for f in [ce]+[bn for bn in aa ["legal_moves"]if bn !=ce]:
                v =bs ("/move",{"game":aa ["game"],"move":f })
                if v.get ("status")!="error":
                    break
            if v.get ("status")=="error":
                v =bs ("/resign",{"game":aa ["game"]})
            aa =v
    print (f"done: {aa.get ('wins')} won,{aa.get ('draws')} drawn,{aa.get ('losses')} lost",file =sys.stderr)
dl()
