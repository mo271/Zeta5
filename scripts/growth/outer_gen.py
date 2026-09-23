from fractions import Fraction as Fr
import math
exec(open('table.py').read().split("def Ein")[0])
lam=Fr(37,40); al=Fr(3,40)
def GO(q,a,d):
    L=2*q+a-2
    if L<=0: return Fr(0)
    return sum(min(Fr(0), i+3*d-Fr(2*q+a+4,2)) for i in range(L))
def Eout(x):
    q=math.floor(x); f=x-q; g=al*x-math.floor(al*x)
    u=lam*x
    s=Fr(0)
    for i in range(3):
        for j in range(3):
            c=bcoef(lambda a: bcoef(lambda b: GO(q,a,b))[j])[i]
            s+=c*ccount(f,g,i,j)
    return -2*u*q+2*Jc_fast(u)-2*s+max(Fr(0),Fr(13,10)*x-2)
lo,hi=Fr(20,37),Fr(3)
cands=set([lo,hi])
for den in [Fr(1,2),Fr(20,3),Fr(20,37),Fr(40,37),Fr(40,43),Fr(20,13)]:
    k=math.ceil(lo/den)
    while k*den<=hi:
        cands.add(k*den); k+=1
cands=sorted(c for c in cands if lo<=c<=hi)
pieces=[]
for x0,x1 in zip(cands,cands[1:]):
    xs=[x0+(x1-x0)*Fr(i,4) for i in (1,2,3)]
    ys=[Eout(x) for x in xs]
    a=(ys[1]-ys[0])/(xs[1]-xs[0]); b=ys[0]-a*xs[0]
    assert ys[2]==a*xs[2]+b
    pieces.append((x0,x1,a,b))
tot=sum(a*(1/x0-1/x1)+b/2*(1/x0**2-1/x1**2) for x0,x1,a,b in pieces)
print(len(pieces), tot, float(tot), "expected", float(Fr(127751,96000)+Fr(9,640)))
import pickle; pickle.dump(pieces,open('outer_pieces.pkl','wb'))
