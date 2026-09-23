from fractions import Fraction as Fr
import math, sys
sys.setrecursionlimit(10000)
exec(open('table.py').read().split("# compare with paper")[0])
lo,hi=Fr(3),Fr(20)
cands=set([lo,hi])
for den in [Fr(1,2),Fr(20,3),Fr(20,37),Fr(40,37),Fr(40,43)]:
    k=math.ceil(lo/den)
    while k*den<=hi:
        cands.add(k*den); k+=1
cands=sorted(c for c in cands if lo<=c<=hi)
pieces=[]
def lin(x0,x1,k):
    # linear coefficients of Ein(.,k) on (x0,x1): check at 3 interior points
    xs=[x0+(x1-x0)*Fr(i,4) for i in (1,2,3)]
    ys=[Ein(x,k) for x in xs]
    a=(ys[1]-ys[0])/(xs[1]-xs[0]); b=ys[0]-a*xs[0]
    assert ys[2]==a*xs[2]+b, "not linear"
    return a,b
for x0,x1 in zip(cands,cands[1:]):
    mid=(x0+x1)/2
    ks=sorted(range(-20,80),key=lambda k:Ein(mid,k))[:4]
    # candidate k's: those minimal somewhere on the piece: check endpoints-ish
    cand=set()
    for t in [Fr(i,20) for i in range(1,20)]:
        x=x0+(x1-x0)*t
        cand.add(min(range(-20,80),key=lambda k:Ein(x,k)))
    lines={k:lin(x0,x1,k) for k in cand}
    # lower envelope on [x0,x1]
    cur=x0
    while cur<x1:
        eps=(x1-cur)/1000
        xm=cur+eps
        kbest=min(lines,key=lambda k:(lines[k][0]*xm+lines[k][1], lines[k][0]))
        a,b=lines[kbest]
        nxt=x1
        for k,(a2,b2) in lines.items():
            if a2<a:  # line k becomes lower later
                xc=(b2-b)/(a-a2)
                if cur<xc<nxt: nxt=xc
        pieces.append((cur,nxt,kbest,a,b))
        cur=nxt
# merge consecutive pieces with same k,a,b
merged=[]
for p in pieces:
    if merged and merged[-1][2:]==p[2:] and merged[-1][1]==p[0]:
        merged[-1]=(merged[-1][0],p[1])+p[2:]
    else: merged.append(p)
print("elementary",len(cands)-1,"pieces",len(pieces),"merged",len(merged))
tot=Fr(0)
for (x0,x1,k,a,b) in merged:
    tot+=a*(1/x0-1/x1)+b/2*(1/x0**2-1/x1**2)
print("integral",tot,float(tot))
print("paper   ",float(Fr(322437603634266857629,7535670527041937280000)))
import pickle; pickle.dump(merged,open('pieces.pkl','wb'))
