# Corollary cor:columns and Remark rem:oeis checks
import sys, math, re
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table
from fractions import Fraction
NMAX=120
T=U_fast_table(10, NMAX//2+1)
def a(k,n): return T[k][(n+1)//2]*T[k][n//2]

def pmul(p,q):
    r=[0]*(len(p)+len(q)-1)
    for i,x in enumerate(p):
        for j,y in enumerate(q): r[i+j]+=x*y
    return r
def ppow(p,e):
    r=[1]
    for _ in range(e): r=pmul(r,p)
    return r
def interp_poly(xs, ys):
    # return monomial coefficients (Fractions) of interpolating polynomial
    n=len(xs); coeffs=[Fraction(0)]*n
    for i in range(n):
        num=[Fraction(1)]; den=Fraction(1)
        for j in range(n):
            if j!=i:
                num=[Fraction(0)]+num
                for t in range(len(num)-1): num[t]-=xs[j]*num[t+1]
                den*= (xs[i]-xs[j])
        for t in range(n): coeffs[t]+=ys[i]*num[t]/den
    return coeffs
def deg(c):
    d=len(c)-1
    while d>=0 and c[d]==0: d-=1
    return d
for k in range(1,8):
    # p_k=(E+O)/2, q_k=(E-O)/2 where E interpolates even n, O odd n (each degree <= 2k)
    ev=[n for n in range(0,2*(2*k+3),2)][:2*k+3]
    od=[n for n in range(1,2*(2*k+3),2)][:2*k+3]
    Ec=interp_poly([Fraction(n) for n in ev],[Fraction(a(k,n)) for n in ev])
    Oc=interp_poly([Fraction(n) for n in od],[Fraction(a(k,n)) for n in od])
    pk=[(x+y)/2 for x,y in zip(Ec,Oc)]; qk=[(x-y)/2 for x,y in zip(Ec,Oc)]
    # verify representation for all n<=NMAX
    def ev_(c,x): return sum(ci*x**i for i,ci in enumerate(c))
    okrep=all(ev_(pk,n)+(-1)**n*ev_(qk,n)==a(k,n) for n in range(0,NMAX+1))
    # generating function numerator: multiply series by (1-x)^{2k+1}(1+x)^{2k-1}
    den=pmul(ppow([1,-1],2*k+1),ppow([1,1],2*k-1))
    ser=[a(k,n) for n in range(NMAX+1)]
    num=[sum(den[i]*ser[n-i] for i in range(min(n,len(den)-1)+1)) for n in range(NMAX+1)]
    dnum=deg(num)
    numpoly=num[:dnum+1]
    at1=sum(numpoly); atm1=sum(c*(-1)**i for i,c in enumerate(numpoly))
    print("k",k,"deg p",deg(pk),"deg q",deg(qk),"rep ok",okrep,"deg numerator",dnum,"(<4k=%d)"%(4*k),"num(1)",at1,"num(-1)",atm1)

# OEIS empirical column recurrences: check char poly = (y-1)^{2k+1}(y+1)^{2k-1}
base=r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\data\oeis"
for k,A in zip(range(3,8),["A207118","A207119","A207120","A207121","A207122"]):
    txt=open(base+"\\"+A+".txt",encoding="utf-8").read()
    line=[l for l in txt.splitlines() if l.startswith("%F") and "Empirical" in l][0]
    terms=re.findall(r"([+-]?\s*\d*)\*?a\(n-(\d+)\)", line.split(":",1)[1])
    coef={}
    for c,i in terms:
        c=c.replace(" ","")
        if c in ("","+"): c=1
        elif c=="-": c=-1
        coef[int(i)]=int(c)
    order=max(coef)
    # char poly y^order - sum coef[i] y^{order-i}; low-degree-first list
    cp=[0]*(order+1); cp[order]=1
    for i,c in coef.items(): cp[order-i]-=c
    target=pmul(ppow([-1,1],2*k+1),ppow([1,1],2*k-1))
    print(A,"order",order,"char poly == (y-1)^{2k+1}(y+1)^{2k-1}:", cp==target)
    # also check recurrence on b-file data vs our a_k(n)
    bf=open(base+"\\b"+A[1:]+".txt").read().split("\n")
    vals={int(l.split()[0]):int(l.split()[1]) for l in bf if l.strip() and not l.startswith("#")}
    print("   b-file agrees with a_k(n) for n<=",max(vals), all(vals[n]==a(k,n) for n in vals if n<=NMAX))
