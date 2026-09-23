import math
lam=37/40; al=3/40
def F(x):
    f=x-math.floor(x); g=al*x-math.floor(al*x)
    return 4*lam+2*lam*f-12*lam*g
def integ(fun,a,b,N):
    h=(b-a)/N; s=0
    for i in range(N):
        x=a+(i+0.5)*h; s+=fun(x)
    return s*h
M=400
for Q0 in (1.51,1.6,2.0):
  tail=integ(lambda x:(x*F(x)+Q0)/x**3,20,M,2000000)
  T=322437603634266857629/7535670527041937280000
  outer=127751/96000+9/640
  small=6*lam/M
  A=outer+T+tail+small
  print(Q0, "tail",tail,"A_eff",A,"margin to 1.3669955:",1.3669955-A)
