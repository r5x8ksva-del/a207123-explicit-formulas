# Section 1-2 checks: tables, reduction, multichains, N triangle, recurrences
import sys, math
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table, U_multichain, a_direct, N_from_U, N_brute, good, binom
from fractions import Fraction

K, M = 16, 10
T = U_fast_table(K, M)
U = lambda k, m: T[k][m]

# Table U in paper
tabU = {0:[1,1,1,1,1,1],1:[1,2,3,4,5,6],2:[1,4,9,16,25,36],3:[1,6,17,36,65,106],
        4:[1,9,32,80,165,301],5:[1,14,64,192,457,938],6:[1,21,119,419,1136,2604],
        7:[1,31,214,873,2669,6778],8:[1,46,388,1837,6334,17802]}
ok = all(T[k][m]==tabU[k][m] for k in tabU for m in range(6))
print("Table U matches:", ok)

# Table N in paper
tabN = {0:[1],1:[0,1],2:[0,1,2],3:[0,1,4,2],4:[0,1,7,8,2],5:[0,1,12,25,16,2],
        6:[0,1,19,59,65,26,2],7:[0,1,29,124,199,139,38,2],8:[0,1,44,253,557,574,277,52,2]}
okN = True
for k in tabN:
    nb = N_brute(k)
    for q,v in enumerate(tabN[k]):
        if nb.get(q,0)!=v or N_from_U(T,k,q)!=v: okN=False; print("N mismatch",k,q,v,nb.get(q,0),N_from_U(T,k,q))
print("Table N matches (brute and inversion):", okN)

# N via inversion for k<=K, q<=M+1
def N(k,q):
    if q<0 or q>k: return 0
    return N_from_U(T,k,q)
# Nbasis first formula
okb = all(U(k,m)==sum(N(k,q)*binom(m+1,q) for q in range(k+1)) for k in range(K+1) for m in range(M+1) if k<=M+1)
print("Nbasis formula:", okb)
# Ntri recurrence for k>=3, q>=1 (q <= M+1 available)
bad=[]
for k in range(3,K+1):
    for q in range(1,min(k,M+1)+1):
        rhs = N(k-1,q-1)+N(k-1,q)+(q-1)*(N(k-3,q-2)+2*N(k-3,q-1)+N(k-3,q))
        if rhs!=N(k,q): bad.append((k,q))
print("Ntri failures k>=3:", bad)
k,q=2,2
print("k=2,q=2 rhs:", N(1,1)+N(1,2)+(q-1)*0, "actual", N(2,2))
# k=2,q=1
print("k=2,q=1 rhs:", N(1,0)+N(1,1), "actual", N(2,1))
# cor diag
print("N(k,k)=2:", all(N(k,k)==2 for k in range(2,M+2)), " N(k,k-1)=k^2-k-4:", [(k,N(k,k-1),k*k-k-4) for k in range(3,M+2)])

# cor poly: leading coeff 2/k! and u_k(-1)=0 -- check via Lagrange interpolation in m
def interp_eval(vals, x):  # vals at m=0..n
    n=len(vals)-1; s=Fraction(0)
    for i in range(n+1):
        term=Fraction(vals[i])
        for j in range(n+1):
            if j!=i: term*=Fraction(x-j, i-j)
        s+=term
    return s
for k in range(0,9):
    vals=[U(k,m) for m in range(k+1)]
    # check degree k: k+2 points prediction
    pred=interp_eval(vals,k+1)
    assert pred==U(k,k+1), ("degree",k)
    # leading coefficient = k-th difference / k!
    d=sum((-1)**(k-i)*math.comb(k,i)*vals[i] for i in range(k+1))
    lc=Fraction(d, math.factorial(k))
    print("k",k,"lc",lc,"expected", Fraction(2,math.factorial(k)) if k>=2 else 1, "u(-1)=", interp_eval(vals,-1))

# Reduction
okr = all(a_direct(n,k)==U(k,(n+1)//2)*U(k,n//2) for n in range(0,7) for k in range(0,6))
print("Reduction a_direct n<=6,k<=5:", okr)
print("a_4(5) =", a_direct(5,4))
# multichain
okm = all(U_multichain(k,m)==U(k,m) for k in range(0,8) for m in range(0,5))
print("Multichain:", okm)
# Example matrix
Mx=[[1,1,1,1],[1,1,1,0],[1,0,1,1],[0,1,1,0],[1,0,1,1]]
def rowok(r): return all(tuple(r[i:i+3]) not in [(0,0,1),(0,1,0)] for i in range(len(r)-2))
def colok(c): return all(tuple(c[i:i+3]) not in [(0,0,1),(0,1,1)] for i in range(len(c)-2))
print("example rows ok", all(rowok(r) for r in Mx), "cols ok", all(colok([Mx[i][j] for i in range(5)]) for j in range(4)))
print("heights odd rows", [sum(Mx[i][j] for i in (0,2,4)) for j in range(4)], "even rows", [sum(Mx[i][j] for i in (1,3)) for j in range(4)])
# U_k(1) = words avoiding 001,010
from itertools import product
print("U_k(1) = |Lambda_k|:", all(U(k,1)==sum(1 for w in product((0,1),repeat=k) if rowok(list(w))) for k in range(0,12)))
# lemma rec with conventions
def Uc(k,m):
    if k==-2: return 0
    if k in (-1,0): return 1
    if m==-1: return 0
    return U(k,m)
print("Lemma rec:", all(Uc(k,m)==Uc(k,m-1)+Uc(k-1,m)+m*Uc(k-3,m) for k in range(1,K+1) for m in range(0,M+1)))
