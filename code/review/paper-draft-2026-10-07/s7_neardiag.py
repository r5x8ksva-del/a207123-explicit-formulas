# Section 7: near-diagonal polynomials p_d, defects, Newton coefficients, final paragraph claims
import sys, math, time
from fractions import Fraction
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table, N_from_U
t0=time.time()
DMAX=101
KMAX=4*DMAX+3
# D(k,d)=N(k,k-d) via (eq:Drec); base: D(k,d)=0 if d<0 or d>k; D(k,k)=[k==0]; k<=2 direct
Dt={}
def D(k,d):
    if d<0 or d>k or k<0: return 0
    return Dt[(k,d)]
base={(0,0):1,(1,0):1,(1,1):0,(2,0):2,(2,1):1,(2,2):0}
for k in range(0,KMAX+1):
    for d in range(0,min(k,DMAX)+1):
        if k<=2: Dt[(k,d)]=base[(k,d)]; continue
        if k-d<1: Dt[(k,d)]=0; continue
        Dt[(k,d)]=D(k-1,d)+D(k-1,d-1)+(k-d-1)*(D(k-3,d-1)+2*D(k-3,d-2)+D(k-3,d-3))
# cross-check with N from U for small k
T=U_fast_table(14,14)
ok=all(D(k,d)==N_from_U(T,k,k-d) for k in range(0,15) for d in range(0,k+1))
print("band recurrence matches N from U (k<=14):",ok, "time %.1fs"%(time.time()-t0))

def newton(d):
    vals=[D(2*d+2+j,d) for j in range(2*d+1)]
    coeffs=[]; row=vals[:]
    for i in range(2*d+1):
        coeffs.append(row[0]); row=[row[j+1]-row[j] for j in range(len(row)-1)]
    return coeffs
def peval_newton(c, n):  # p(2d+2+n) = sum c_i C(n,i), n integer possibly negative
    s=0
    for i,ci in enumerate(c):
        # generalized binomial C(n,i) for integer n
        num=1
        for t in range(i): num*= (n-t)
        s+=ci*num//math.factorial(i)
    return s
bad_threshold=[]; bad_lc=[]; bad_e1=[]; bad_e0=[]; bad_pos=[]; neg2d1=[]
for d in range(0,DMAX+1):
    c=newton(d)
    # polynomial degree <=2d holds beyond interpolation window: check k=4d+3
    if peval_newton(c,2*d+1)!=D(4*d+3,d): bad_threshold.append(d)
    if c[-1]!=2*math.prod(range(1,2*d,2)): bad_lc.append(d)
    p2d1=peval_newton(c,-1); p2d=peval_newton(c,-2)
    if D(2*d+1,d)-p2d1!=(-1)**(d+1)*math.factorial(d+1): bad_e1.append(d)
    if 2*(D(2*d,d)-p2d)!=(-1)**(d+1)*math.factorial(d+2): bad_e0.append(d)
    if not all(x>0 for x in c): bad_pos.append(d)
    if p2d1<0: neg2d1.append(d)
print("polynomiality check at k=4d+3 failures:",bad_threshold)
print("last Newton coeff = 2(2d-1)!! failures:",bad_lc)
print("e_d(2d+1) formula failures:",bad_e1," e_d(2d) formula failures:",bad_e0)
print("Newton coeffs at 2d+2 all positive, failures:",bad_pos)
print("d with p_d(2d+1)<0 (d<=101):",neg2d1)
print("d=2 Newton coefficients:",newton(2))
# explicit polynomials p_d in k for small d; leading and second coefficients
def mono_from_newton(c,shift):  # p(shift + t) monomial coeffs in t, Fractions; c Newton coeffs at x0 = 2d+2 -> p(x0+n)
    # we want p(k) coefficients: n = k - x0
    pass
def p_monomial_in_k(d):
    c=newton(d); x0=2*d+2
    # p(k)=sum c_i C(k-x0,i)
    poly=[Fraction(0)]*(2*d+1)
    for i,ci in enumerate(c):
        term=[Fraction(1)]
        for t in range(i):  # multiply by (k - x0 - t)
            new=[Fraction(0)]*(len(term)+1)
            for j,a in enumerate(term):
                new[j+1]+=a; new[j]+=a*(-(x0+t))
            term=new
        for j,a in enumerate(term): poly[j]+=ci*a/math.factorial(i)
    return poly
for d in range(0,4):
    pm=p_monomial_in_k(d)
    print("p_%d(k) * %d ="%(d, 2**d*math.factorial(d)//2 if d>0 else 1), [x*(2**d*math.factorial(d)//2 if d>0 else 1) for x in pm[::-1]])
okr=True
for d in range(1,16):
    pm=p_monomial_in_k(d)
    lc=pm[2*d]; sc=pm[2*d-1]
    if lc!=Fraction(2,2**d*math.factorial(d)) or sc/lc!=-(4*d*d-3*d): okr=False; print("coef fail",d,lc,sc/lc)
print("leading coeff 2/(2^d d!) and r_d=-(4d^2-3d) for d<=15:",okr)
# table exc
for d in range(0,4):
    pm=p_monomial_in_k(d)
    for k in range(d+1,2*d+2):
        pk=sum(a*k**j for j,a in enumerate(pm))
        print("  d=%d k=%d D=%d p=%s e=%s"%(d,k,D(k,d),pk,D(k,d)-pk))
# monomial coefficients of p_d(2d+1+t) via integer Horner: H_i = c_i*(2d)!/i! + (t-(i+1))*H_{i+1}
def coeffs_shift_2d1(d):
    c=newton(d); F=math.factorial(2*d)
    H=[c[2*d]]  # low-first poly in t
    for i in range(2*d-1,-1,-1):
        # multiply H by (t-(i+1))
        new=[0]*(len(H)+1)
        for j,a in enumerate(H):
            new[j+1]+=a; new[j]-=(i+1)*a
        new[0]+=c[i]*(F//math.factorial(i))
        H=new
    return H
negs=[]
for d in range(0,61):
    H=coeffs_shift_2d1(d)
    if any(x<0 for x in H): negs.append(d)
    # sanity: H(0) == (2d)! * p_d(2d+1)
    if d<=101:
        assert H[0]==math.factorial(2*d)*peval_newton(newton(d),-1)
print("d<=60 with a negative coefficient of p_d(2d+1+t):",negs)
print("total time %.1fs"%(time.time()-t0))
