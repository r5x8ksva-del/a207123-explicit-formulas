# Section 6.1 numerical checks: residues, norms, fibres
import math, cmath
import numpy as np
from fractions import Fraction

def pmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): r[i+j]+=x*y
    return r
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def b(i): return [1,-1] if i==0 else [1,-1,0,-i]
def P(m):
    r=[1]
    for i in range(m+1): r=pmul(r,b(i))
    return r
def W(m):
    r=[1]
    for j in range(1,m+1): r=padd(r,[0,0]+[j*c for c in P(j-1)])
    return r
def ev(a,x): return sum(c*x**i for i,c in enumerate(a))
def der(a): return [i*a[i] for i in range(1,len(a))]
def roots_b(i): return [complex(r) for r in np.roots([-i,0,-1,1])]  # -i x^3 - x + 1
up=lambda x: x**2*(3-2*x)/(1-x)**2
# Thm S residue formula
err=0
for m in range(1,7):
    for xi in roots_b(1):
        res=ev(W(m),xi)/ev(der(P(m)),xi)
        lhs=res*up(xi)
        rhs=(-1)**m*(1+xi)*xi**(-3*m-2)/math.factorial(m-1)
        err=max(err,abs(lhs-rhs)/abs(rhs))
print("Thm S residue formula max rel err (m<=6):",err)
xs=roots_b(1)
print("Nm(xi)=",np.prod(xs),"Nm(1+xi)=",np.prod([1+x for x in xs]))
# check theta takes different values at the three roots for some g (sanity: it cannot be constant)
# Thm Spart residue formula
def Gup(m):  # (W_m - 1)/P_m
    w=W(m); w[0]-=1; return w
err=0
for m in range(2,7):
    for i in range(1,m+1):
        for eta in roots_b(i):
            res=ev(Gup(m),eta)/ev(der(P(m)),eta)
            lhs=res*eta**2*(3-2*eta)/(1-eta)**2
            Wt=1+sum(j*math.perm(i,j)*eta**(3*j+2) for j in range(1,i+1))
            rhs=(-1)**(m-i+1)*(Wt-1)*eta**(-3*m-3)/(math.factorial(m-i)*math.factorial(i)*i*i)
            err=max(err,abs(lhs-rhs)/abs(rhs))
print("Thm Spart residue formula max rel err (m<=6):",err)
es=roots_b(2)
print("Nm(eta) for b_2:",np.prod(es)," Nm(4-2eta):",np.prod([4-2*e for e in es]))
print("W~_2(eta)-1 vs eta^5(4-2eta):",max(abs(2*e**5+4*e**8-e**5*(4-2*e)) for e in es))
# m=1 sharpness: U^up_k(1) = sum_{s>=-1} C(k-4-2s, 1+s)
import sys
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import good
def binom(a,bb): return math.comb(a,bb) if 0<=bb<=a else 0
def goodseqs(k,m):
    out=[]
    def rec(seq):
        if len(seq)==k: out.append(tuple(seq)); return
        for v in range(m+1):
            if len(seq)>=2 and not good(seq[-2],seq[-1],v): continue
            seq.append(v); rec(seq); seq.pop()
    rec([]); return out
ok=all(sum(1 for h in goodseqs(k,1) if k>=2 and h[-2]<h[-1])==sum(binom(k-4-2*s,1+s) for s in range(-1,k)) for k in range(0,14))
print("m=1 U^up formula:",ok)
# Prop shapes: xi > 0.68, v0 = xi^-3 < 6; fibres for (1,2),(2,3)
xi=[x.real for x in roots_b(1) if abs(x.imag)<1e-12][0]
print("xi=",xi," b_1(0.68)=",1-0.68-0.68**3," v0=xi^-3=",xi**-3)
for (al,be) in [(1,2),(2,3),(3,0)]:
    v0=xi**(al+be)*(1-xi)**(-be)
    # h(x)= x^{al+be} - v0 (1-x)^be
    hp=[0]*(al+be+1); hp[al+be]=1
    one_minus=[1]
    for _ in range(be): one_minus=pmul(one_minus,[1,-1])
    for i,c in enumerate(one_minus): hp[i]-=v0*c
    rts=np.roots(hp[::-1])
    nreal=sum(1 for r in rts if abs(r.imag)<1e-9)
    # are fibre points roots of some b_w (w<=50)?
    hits=[(r,w) for r in rts for w in range(1,51) if abs(ev(b(w),r))<1e-8]
    vprime=[abs(r**(al+be-1)*(1-r)**(-be-1)*(al+be-al*r)) for r in rts]
    print("shape",(al,be),"v0=%.5f"%v0,"#real fibre pts",nreal,"of",len(rts),"fibre pts that are roots of b_w (w<=50):",[(np.round(r,6),w) for r,w in hits], "min|v'|=%.3g"%min(vprime), "min|r|,min|1-r|=%.3g,%.3g"%(min(abs(r) for r in rts),min(abs(1-r) for r in rts)))
