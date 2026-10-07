# Section 3 checks: G_m = W_m/P_m, gcd, asymptotics, constants, columns
import sys, math, cmath
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table, U_fast_column
from fractions import Fraction
import numpy as np

# integer polynomial helpers (lists, low degree first)
def pmul(a,b):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]+=x*y
    return r
def padd(a,b):
    n=max(len(a),len(b)); return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n)]
def pscale(a,c): return [c*x for x in a]
def b(i): return [1,-1] if i==0 else [1,-1,0,-i]
def P(m):
    r=[1]
    for i in range(m+1): r=pmul(r,b(i))
    return r
def W(m):
    r=[1]
    for j in range(1,m+1): r=padd(r, [0,0]+pscale(P(j-1),j))
    return r
def series_div(num,den,N):
    # power series num/den up to x^N, den[0]=1
    out=[0]*(N+1)
    for n in range(N+1):
        s=num[n] if n<len(num) else 0
        for i in range(1,min(n,len(den)-1)+1): s-=den[i]*out[n-i]
        out[n]=s  # den[0]==1
    return out
Kmax=60
for m in range(0,8):
    col=U_fast_column(m,Kmax)
    ser=series_div(W(m),P(m),Kmax)
    assert ser==col, m
    def deg(a):
        a=list(a)
        while a and a[-1]==0: a.pop()
        return len(a)-1
    assert deg(W(m))==3*m and deg(P(m))==3*m+1, (m,deg(W(m)),deg(P(m)))
print("G_m = W_m/P_m verified for m<=7, k<=60; deg W=3m, deg P=3m+1")

# W_4(1/2)
def peval(a,x): return sum(c*x**i for i,c in enumerate(a))
print("W_4(1/2) =", peval(W(4),Fraction(1,2)))

# gcd over Q via Euclid with Fractions
def pdivmod(a,bb):
    a=[Fraction(x) for x in a]; bb=[Fraction(x) for x in bb]
    while bb and bb[-1]==0: bb.pop()
    q=[Fraction(0)]*max(1,len(a)-len(bb)+1)
    while len(a)>=len(bb) and any(a):
        while a and a[-1]==0: a.pop()
        if len(a)<len(bb): break
        c=a[-1]/bb[-1]; d=len(a)-len(bb); q[d]=c
        for i,y in enumerate(bb): a[i+d]-=c*y
        a.pop()
    return q,a
def pgcd(a,bb):
    a=[Fraction(x) for x in a]; bb=[Fraction(x) for x in bb]
    while any(bb):
        _,r=pdivmod(a,bb)
        while r and r[-1]==0: r.pop()
        a,bb=bb,r
    return a
for m in range(0,13):
    g=pgcd(W(m),P(m))
    while g and g[-1]==0: g.pop()
    assert len(g)==1, (m,g)
print("gcd(W_m,P_m)=1 for m<=12")

# Asymptotics: roots, alpha_m(sigma) = -sigma*W(1/sigma)/P'(1/sigma)
def pder(a): return [i*a[i] for i in range(1,len(a))]
def roots_of(i):
    if i==0: return [1.0+0j]
    return list(np.roots([1,-1,0,-i]).astype(complex))
def alpha(m,sig):
    x=1/sig
    return -sig*peval(W(m),x)/peval(pder(P(m)),x)
rho={0:1.0}
for m in range(1,12):
    rr=[r for r in roots_of(m) if abs(r.imag)<1e-12]
    rho[m]=rr[0].real
print("rho_1..4:", [rho[m] for m in range(1,5)])
# check |sigma|^2 = rho(rho-1) < rho_{m-1}^2
for m in range(1,11):
    nr=[r for r in roots_of(m) if abs(r.imag)>1e-9]
    assert abs(abs(nr[0])**2-rho[m]*(rho[m]-1))<1e-9 and abs(nr[0])**2<rho[m-1]**2
print("|sigma|^2 = rho(rho-1) < rho_{m-1}^2 ok for m<=10")
# propagation rule
maxerr=0
for m in range(1,8):
    for j in range(0,m):
        for sig in roots_of(j):
            lhs=alpha(m,sig); rhs=alpha(j,sig)*(-sig**3)**(m-j)/math.factorial(m-j)
            maxerr=max(maxerr,abs(lhs-rhs)/abs(rhs))
print("propagation rule max rel err:", maxerr)
# nonzero alphas and representation for k>=0
for m in range(0,6):
    allr=[s for i in range(m+1) for s in roots_of(i)]
    col=U_fast_column(m,30)
    for k in range(31):
        v=sum(alpha(m,s)*s**k for s in allr)
        assert abs(v-col[k])<1e-6*max(1,col[k]), (m,k,v,col[k])
    assert min(abs(alpha(m,s)) for s in allr)>1e-9
print("exponential-polynomial representation ok for m<=5, k<=30, all alpha nonzero")
# c_m two expressions
def c_expr1(m):
    x=1/rho[m]
    Gm1=peval(W(m-1),x)/peval(P(m-1),x)
    return (Gm1+m*x*x)/(x*(1+3*m*x*x))
def c_expr2(m):
    r=rho[m]
    s=1+sum(j*math.perm(m,j)*r**(-3*j-2) for j in range(1,m+1))
    return r**(3*m+3)/(math.factorial(m)*(r*r+3*m))*s
for m in range(1,7):
    print("m",m,"c_m expr1 %.6f expr2 %.6f alpha %.6f"%(c_expr1(m),c_expr2(m),alpha(m,complex(rho[m])).real))
r1=rho[1]
print("c_1 closed form:", (10+15*r1+17*r1*r1)/31)
# c_4 exact: x=1/2
x=Fraction(1,2)
c4=(peval(W(3),x)/peval(P(3),x)+4*x*x)/(x*(1+12*x*x))
print("c_4 exact:", c4)
# asymptotic check U_k(m) - c_m rho^k + c_{m-1} rho_{m-1}^{k+3} vs tau^k
cm={0:1.0}
for m in range(1,8): cm[m]=c_expr1(m)
for m in range(1,6):
    col=U_fast_column(m,200)
    tau = math.sqrt(rho[1]*(rho[1]-1)) if m==1 else max(rho[m-2], math.sqrt(rho[m]*(rho[m]-1)))
    ratios=[]
    for k in (100,150,200):
        # use exact representation subtract numerically with high precision via Fraction? use float on difference relative
        approx=cm[m]*rho[m]**k - cm[m-1]*rho[m-1]**(k+3)
        diff=col[k]-approx
        ratios.append(diff/tau**k if tau**k>0 else None)
    print("m",m,"tau=%.5f"%tau,"(U - two terms)/tau^k at k=100,150,200:", ["%.3g"%r for r in ratios])
