# Open problems section quick checks: zeros of u_k at negative integers, h_k degree and values
import sys, math
from fractions import Fraction
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
KM=30
# N via triangular recurrence (verified earlier against brute force)
N=[[0]*(KM+2) for _ in range(KM+1)]
N[0][0]=1
if KM>=1: N[1][1]=1
if KM>=2: N[2][1]=1; N[2][2]=2
def g(k,q):
    if k<0 or q<0 or q>k: return 0
    return N[k][q]
for k in range(3,KM+1):
    for q in range(1,k+1):
        N[k][q]=g(k-1,q-1)+g(k-1,q)+(q-1)*(g(k-3,q-2)+2*g(k-3,q-1)+g(k-3,q))
def pbinom(x,q):  # polynomial binomial C(x,q) at integer x
    num=1
    for t in range(q): num*=(x-t)
    return Fraction(num, math.factorial(q))
def u(k,m): return sum(N[k][q]*pbinom(m+1,q) for q in range(k+1))
bad=[]
for k in range(1,KM+1):
    zeros=[m for m in range(-1,-(k+40),-1) if u(k,m)==0]
    exp=list(range(-1,-((k+2)//3)-1,-1))
    if zeros!=exp: bad.append((k,zeros,exp))
print("negative-integer zeros exactly -1..-floor((k+2)/3) for k<=30 (searched down to -(k+39)):", bad==[], bad[:3])
# h_k: sum_m U_k(m) t^m = h_k(t)/(1-t)^{k+1}; h_k(t) = sum_q N(k,q) t^{q-1} (1-t)^{k-q} for k>=1
def hk(k):
    h=[0]*(k+1)
    for q in range(1,k+1):
        # t^{q-1}(1-t)^{k-q}
        for i in range(k-q+1):
            h[q-1+i]+=N[k][q]*math.comb(k-q,i)*(-1)**i
    while h and h[-1]==0: h.pop()
    return h
okh=all(len(hk(k))-1==(2*k)//3 and hk(k)[0]==1 and (k<2 or sum(hk(k))==2) for k in range(1,KM+1))
print("deg h_k = floor(2k/3), h_k(0)=1, h_k(1)=2 (k>=2), k<=30:", okh)
# sanity of h_k vs U: series check for k=7
k=7
import itertools
h=hk(k)
ser=[sum(h[i]*math.comb(m-i+k,k) for i in range(len(h)) if m-i>=0) for m in range(10)]
print("series check k=7:", ser==[int(u(k,m)) for m in range(10)])
