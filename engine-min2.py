import json,os,random,sys
import urllib.error,urllib.request
dc =os.environ.get ("MAKEFUN_ENV_URL")or sys.exit ("no URL")
af =[0,100,320,330,500,900,0]
cs =(-33,-31,-18,-14,14,18,31,33)
cr =(-17,-16,-15,-1,1,15,16,17)
cb =(-16,-1,1,16)
ca =(-17,-15,15,17)
bc =100000
bv =1000000
c =[0]*128
p =[[],[]]
t =[-1]*128
y =[4,116]
d =0
ad =0
s =-1
ac =[0,0]
an =[0,0]
ah =[0,0]
n =0
ax =0
bu =120000
bd ={}
bb =[[0,0]for at in range (256)]
co =[[0]*128 for at in range (128)]
bi =random.Random (987654321)
ar =[[bi.getrandbits (64)for at in range (128)]for at in range (13)]
cd =bi.getrandbits (64)
cc =[bi.getrandbits (64)for at in range (16)]
bm =[bi.getrandbits (64)for at in range (8)]
am =[15]*128
am [0]=13 ;am [7]=14 ;am [112]=7 ;am [119]=11 ;am [4]=12 ;am [116]=3
def di ():
    z =[[0]*128 for at in range (8)]
    for b in range (128):
        if b &0x88:
            continue
        e =b &7
        v =b >>4
        r =(3 -abs (e -3.5))+(3 -abs (v -3.5))
        z [1][b]=v *10 +int ((3 -abs (e -3.5))*3)
        z [2][b]=int (r *6)-(10 if v ==0 else 0)
        z [3][b]=int (r *5)
        z [4][b]=(25 if v ==6 else 0)+int (r *2)
        z [5][b]=int (r *3)
        z [6][b]=-v *8
        z [7][b]=int (r *8)
    return z
z =di ()
def dv ():
    du =ac [0]+ac [1]<2600
    cj =7 if du else 6
    g =ac [0]-ac [1]
    for b in p [0]:
        i =c [b]
        g +=z [cj][b]if i ==6 else z [i][b]
    for b in p [1]:
        i =-c [b]
        g -=z [cj][b ^0x70]if i ==6 else z [i][b ^0x70]
    if ah [0]==2:
        g +=30
    if ah [1]==2:
        g -=30
    for ai in (0,1):
        do =y [ai]
        aq =16 if ai ==0 else -16
        ch =0
        for m in (aq -1,aq,aq +1):
            ae =do +m
            if not (ae &0x88)and c [ae]==(1 if ai ==0 else -1):
                ch +=1
        g +=(ch -2)*25 if ai ==0 else -(ch -2)*25
    for ai in (0,1):
        for b in p [ai]:
            if abs (c [b])==1:
                aq =16 if ai ==0 else -16
                if all ((b +m)&0x88 or c [b +m]!=-c [b]for m in (aq -1,aq,aq +1)):
                    dx =b >>4 if ai ==0 else 7 -(b >>4)
                    g +=(12 +dx *8)*(1 if ai ==0 else -1)
    be =g if d ==0 else -g
    return be +10
def u (b,ct):
    r =1 if ct ==0 else -1
    for m in ((-15,-17)if ct ==0 else (15,17)):
        a =b +m
        if not (a &0x88)and c [a]==r:
            return True
    for m in cs:
        a =b +m
        if not (a &0x88)and c [a]==2 *r:
            return True
    for m in cr:
        a =b +m
        if not (a &0x88)and c [a]==6 *r:
            return True
    for m in cb:
        a =b +m
        while not (a &0x88):
            i =c [a]
            if i:
                if i ==4 *r or i ==5 *r:
                    return True
                break
            a +=m
    for m in ca:
        a =b +m
        while not (a &0x88):
            i =c [a]
            if i:
                if i ==3 *r or i ==5 *r:
                    return True
                break
            a +=m
    return False
br =[]
def bj (f):
    global d,ad,s,n
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    ag =c [e]
    w =c [a]
    ab =a
    if ag ==(1 if d ==0 else -1)and a ==s and w ==0:
        ab =a -16 if d ==0 else a +16
        w =c [ab]
    bh,ba,az =ad,s,n
    n ^=ar [ag +6][e]
    if w:
        n ^=ar [w +6][ab]
        c [ab]=0
        ac [1 -d]-=af [abs (w)]
        if abs (w)>1:
            an [1 -d]-=1
        if abs (w)==3:
            ah [1 -d]-=1
        ci =t [ab]
        by =p [1 -d]
        cp =by.pop ()
        if ci <len (by):
            by [ci]=cp
            t [cp]=ci
        t [ab]=-1
    p [d][t [e]]=a
    t [a]=t [e]
    t [e]=-1
    c [a]=i *(1 if d ==0 else -1)if i else ag
    c [e]=0
    n ^=ar [c [a]+6][a]
    if i:
        ac [d]+=af [i]-100
        if i >1:
            an [d]+=1
        if i ==3:
            ah [d]+=1
    if abs (ag)==6:
        y [d]=a
        if a -e ==2:
            bg (e +3,e +1)
        elif e -a ==2:
            bg (e -4,e -1)
    ad &=am [e]&am [a]
    n ^=cc [bh]^cc [ad]
    if s >=0:
        n ^=bm [s &7]
    if abs (ag)==1 and abs (a -e)==32:
        s =e +16 if d ==0 else e -16
        n ^=bm [s &7]
    else:
        s =-1
    n ^=cd
    d ^=1
    br.append ((f,w,ab,bh,ba,az))
def bg (e,a):
    global n
    v =c [e]
    n ^=ar [v +6][e]^ar [v +6][a]
    p [d][t [e]]=a
    t [a]=t [e]
    t [e]=-1
    c [a]=v
    c [e]=0
def ap ():
    global d,ad,s,n
    f,w,ab,bh,ba,az =br.pop ()
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    d ^=1
    ag =c [a]
    if i:
        ac [d]-=af [i]-100
        if i >1:
            an [d]-=1
        if i ==3:
            ah [d]-=1
        ag =1 if d ==0 else -1
    if abs (ag)==6:
        y [d]=e
        if a -e ==2:
            bg (e +1,e +3)
        elif e -a ==2:
            bg (e -1,e -4)
    p [d][t [a]]=e
    t [e]=t [a]
    t [a]=-1
    c [e]=ag
    c [a]=0
    if w:
        c [ab]=w
        p [1 -d].append (ab)
        t [ab]=len (p [1 -d])-1
        ac [1 -d]+=af [abs (w)]
        if abs (w)>1:
            an [1 -d]+=1
        if abs (w)==3:
            ah [1 -d]+=1
    ad,s,n =bh,ba,az
def de ():
    global d,s,n
    if s >=0:
        n ^=bm [s &7]
    s =-1
    n ^=cd
    d ^=1
def db (ba,az):
    global d,s,n
    d ^=1
    s,n =ba,az
def bx (ay =False):
    l =[]
    r =1 if d ==0 else -1
    o =16 if d ==0 else -16
    cy =1 if d ==0 else 6
    cl =7 if d ==0 else 0
    for b in p [d]:
        i =c [b]
        h =abs (i)
        if h ==1:
            a =b +o
            if not (a &0x88)and c [a]==0:
                if (a >>4)==cl:
                    for cf in (5,4,3,2):
                        l.append (b |(a <<7)|(cf <<14))
                else:
                    if not ay:
                        l.append (b |(a <<7))
                    if (b >>4)==cy:
                        cu =a +o
                        if c [cu]==0 and not ay:
                            l.append (b |(cu <<7))
            for m in (o -1,o +1):
                a =b +m
                if a &0x88:
                    continue
                ae =c [a]
                if ae and ae *r <0:
                    if (a >>4)==cl:
                        for cf in (5,4,3,2):
                            l.append (b |(a <<7)|(cf <<14))
                    else:
                        l.append (b |(a <<7))
                elif a ==s:
                    l.append (b |(a <<7))
        elif h ==2 or h ==6:
            for m in cs if h ==2 else cr:
                a =b +m
                if a &0x88:
                    continue
                ae =c [a]
                if ae ==0:
                    if not ay:
                        l.append (b |(a <<7))
                elif ae *r <0:
                    l.append (b |(a <<7))
        else:
            for m in (cb if h ==4 else ca if h ==3 else cb +ca):
                a =b +m
                while not (a &0x88):
                    ae =c [a]
                    if ae ==0:
                        if not ay:
                            l.append (b |(a <<7))
                    else:
                        if ae *r <0:
                            l.append (b |(a <<7))
                        break
                    a +=m
    if not ay and abs (c [y [d]])==6:
        dd (l,r)
    return l
def dd (l,r):
    cj =y [d]
    if d ==0:
        if ad &1 and c [5]==0 and c [6]==0 and c [7]==4 and not u (4,1)and not u (5,1)and not u (6,1):
            l.append (4 |(6 <<7))
        if ad &2 and c [3]==0 and c [2]==0 and c [1]==0 and c [0]==4 and not u (4,1)and not u (3,1)and not u (2,1):
            l.append (4 |(2 <<7))
    else:
        if ad &4 and c [117]==0 and c [118]==0 and c [119]==-4 and not u (116,0)and not u (117,0)and not u (118,0):
            l.append (116 |(118 <<7))
        if ad &8 and c [115]==0 and c [114]==0 and c [113]==0 and c [112]==-4 and not u (116,0)and not u (115,0)and not u (114,0):
            l.append (116 |(114 <<7))
class cm (Exception):
    pass
def cg (h,q,k):
    global ax
    ax +=1
    if ax >bu:
        raise cm
    if u (y [d],1 -d):
        x =-bc +k
        for f in bx ():
            bj (f)
            if u (y [d ^1],d):
                ap ()
                continue
            g =-cg (-q,-h,k +1)
            ap ()
            if g >x:
                x =g
            if g >h:
                h =g
            if h >=q:
                return q
        return x if x >-bc +k else -bc +k
    g =dv ()
    if g >=q:
        return q
    if g >h:
        h =g
    for f in cv (bx (True)):
        bj (f)
        if u (y [d ^1],d):
            ap ()
            continue
        g =-cg (-q,-h,k +1)
        ap ()
        if g >h:
            h =g
        if h >=q:
            return q
    return h
def cv (l):
    def be (f):
        a =(f >>7)&127
        j =c [a]
        if j ==0 and (f >>14)&15 ==0:
            j =1
        return -(10 *af [abs (j)]-af [abs (c [f &127])]//10)
    l.sort (key =be)
    return l
def aw (o,h,q,k):
    global ax
    ax +=1
    if ax >bu:
        raise cm
    if len (p [0])+len (p [1])<=4:
        bl =[abs (c [g])for g in p [0]if g !=y [0]]+[abs (c [g])for g in p [1]if g !=y [1]]
        if not bl or (len (bl)==1 and bl [0]in (2,3))or bl ==[3,3]:
            return 0
    aj =bd.get (n)
    if aj is not None and aj [0]>=o:
        j =aj [2]
        if j >90000:
            j -=k
        elif j <-90000:
            j +=k
        if aj [1]==0:
            return j
        if aj [1]==1 and j >=q:
            return j
        if aj [1]==2 and j <=h:
            return j
    bn =u (y [d],1 -d)
    if o <=0:
        if bn:
            o =1
        else:
            return cg (h,q,k)
    dt =h
    if o >=3 and not bn and an [d]>0:
        dp,dm =s,n
        de ()
        g =-aw (o -3,-q,-h,k +1)
        db (dp,dm)
        if g >=q:
            return q
    bp =aj [3]if aj is not None else 0
    l =df (bx (),bp,k)
    x =-bv
    cn =0
    bs =2
    bk =0
    for f in l:
        cq =c [(f >>7)&127]
        bj (f)
        if u (y [d ^1],d):
            ap ()
            continue
        bk +=1
        if bk ==1:
            g =-aw (o -1,-q,-h,k +1)
        elif o >=3 and bk >3 and cq ==0 and ((f >>14)&15)==0 and not bn:
            g =-aw (o -2,-q,-h,k +1)
            if g >h:
                g =-aw (o -1,-q,-h,k +1)
        else:
            g =-aw (o -1,-q,-h,k +1)
        ap ()
        if g >x:
            x =g
            cn =f
        if g >h:
            h =g
        if h >=q:
            bs =1
            if k <128 and cq ==0 and ((f >>14)&15)==0:
                bb [k][1]=bb [k][0]
                bb [k][0]=f
                co [f &127][(f >>7)&127]+=o *o
            break
    if bk ==0:
        return -bc +k if bn else 0
    j =x
    if j >90000:
        j +=k
    elif j <-90000:
        j -=k
    if len (bd)>300000:
        bd.clear ()
    dw =bs if bs ==1 else (0 if x >dt else 2)
    bd [n]=(o,dw,j,cn)
    return x
def df (l,bp,k):
    def be (f):
        e =f &127
        a =(f >>7)&127
        if f ==bp:
            return -1000000
        j =c [a]
        if j:
            return -(10 *af [abs (j)]-af [abs (c [e])]//10)
        if f ==bb [k][0]:
            return -9000
        if f ==bb [k][1]:
            return -8000
        return -co [e][a]
    l.sort (key =be)
    return l
def cw (ak,dh):
    bz =[]
    h =-bv
    for f in ak:
        bj (f)
        g =-aw (dh -1,-bv,-h,1)
        ap ()
        bz.append ((g,f))
        if g >h:
            h =g
    bz.sort (key =lambda bo:-bo [0])
    return bz
def da (bw):
    global d,ad,s,n,ac,an,ah
    al =bw.split ()
    for bf in range (128):
        c [bf]=0
    p [0]=[]
    p [1]=[]
    for bf in range (128):
        t [bf]=-1
    ac [0]=ac [1]=0
    an [0]=an [1]=0
    ah [0]=ah [1]=0
    dk ={"p":1,"n":2,"b":3,"r":4,"q":5,"k":6 }
    for bf,ds in enumerate (al [0].split ("/")):
        e =0
        for av in ds:
            if av.isdigit ():
                e +=int (av)
            else:
                b =(7 -bf)*16 +e
                j =dk [av.lower ()]*(1 if av.isupper ()else -1)
                c [b]=j
                au =0 if j >0 else 1
                t [b]=len (p [au])
                p [au].append (b)
                if abs (j)==6:
                    y [au]=b
                else:
                    ac [au]+=af [abs (j)]
                    if abs (j)>1:
                        an [au]+=1
                    if abs (j)==3:
                        ah [au]+=1
                e +=1
    d =0 if al [1]=="w"else 1
    ad =0
    if len (al)>2:
        for av in al [2]:
            ad |={"K":1,"Q":2,"k":4,"q":8 }.get (av,0)
    s =-1
    if len (al)>3 and al [3]!="-":
        s =(ord (al [3][0])-97)+(int (al [3][1])-1)*16
    br.clear ()
    bd.clear ()
    n =0
    for b in p [0]:
        n ^=ar [c [b]+6][b]
    for b in p [1]:
        n ^=ar [c [b]+6][b]
    n ^=cc [ad]
    if s >=0:
        n ^=bm [s &7]
    if d ==1:
        n ^=cd
def cx (ao):
    e =(ord (ao [0])-97)+(int (ao [1])-1)*16
    a =(ord (ao [2])-97)+(int (ao [3])-1)*16
    i ={"q":5,"r":4,"b":3,"n":2 }.get (ao [4],0)if len (ao)==5 else 0
    return e |(a <<7)|(i <<14)
def ck (f):
    e =f &127
    a =(f >>7)&127
    i =(f >>14)&15
    g ="abcdefgh"[e &7]+str ((e >>4)+1)+"abcdefgh"[a &7]+str ((a >>4)+1)
    if i:
        g +="qrbn"[5 -i]if i in (5,4,3,2)else ""
    return g
def dg (bw,cz):
    global ax,bu
    da (bw)
    ak =[cx (ao)for ao in cz]
    if len (ak)==1:
        return ck (ak [0])
    ax =0
    ak.sort (key =lambda f:-(10 *af [abs (c [(f >>7)&127])]if c [(f >>7)&127]else 0))
    x =ak [0]
    o =1
    while True:
        try:
            bq =cw (ak,o)
        except cm:
            break
        x =bq [0][1]
        ak =[f for at,f in bq]
        if ax >bu *0.75:
            break
        if bq [0][0]>bc -1000:
            break
        o +=1
        if o >64:
            break
    return ck (x)
def bt (dn,dj):
    try:
        dq =urllib.request.Request (dc +dn,data =json.dumps (dj).encode (),headers ={"content-type":"application/json"})
        with urllib.request.urlopen (dq)as dr:
            return json.load (dr)
    except Exception:
        return {"status":"error"}
def dl ():
    while True:
        aa =bt ("/game",{})
        if aa.get ("status")=="done":
            break
        while aa.get ("status")=="your_move":
            try:
                ce =dg (aa ["fen"],aa ["legal_moves"])
            except Exception as aj:
                print ("fail",aj,file =sys.stderr)
                ce =aa ["legal_moves"][0]
            v ={"status":"error"}
            for f in [ce]+[bo for bo in aa ["legal_moves"]if bo !=ce]:
                v =bt ("/move",{"game":aa ["game"],"move":f })
                if v.get ("status")!="error":
                    break
            if v.get ("status")=="error":
                v =bt ("/resign",{"game":aa ["game"]})
            aa =v
    print (f"done: {aa.get ('wins')} won,{aa.get ('draws')} drawn,{aa.get ('losses')} lost",file =sys.stderr)
dl()
