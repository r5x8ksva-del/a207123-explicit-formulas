# floating-point sanity check of open problem 1: real roots of h_k, (non-)interlacing
import math
import numpy as np
KM=30
N=[[0]*(KM+2) for _ in range(KM+1)]
N[0][0]=1; N[1][1]=1; N[2][1]=1; N[2][2]=2
def g(k,q):
    if k<0 or q<0 or q>k: return 0
    return N[k][q]
for k in range(3,KM+1):
    for q in range(1,k+1):
        N[k][q]=g(k-1,q-1)+g(k-1,q)+(q-1)*(g(k-3,q-2)+2*g(k-3,q-1)+g(k-3,q))
def hk(k):
    h=[0]*(k+1)
    for q in range(1,k+1):
        for i in range(k-q+1):
            h[q-1+i]+=N[k][q]*math.comb(k-q,i)*(-1)**i
    while h and h[-1]==0: h.pop()
    return h
allreal=True; roots={}
for k in range(2,KM+1):
    h=hk(k)
    r=np.roots([float(c) for c in h[::-1]])
    if max(abs(r.imag))>1e-6: allreal=False; print("nonreal?",k,max(abs(r.imag)))
    roots[k]=np.sort(r.real)
print("h_k real-rooted (float) for 2<=k<=30:",allreal)
def interlace(a,b):
    # b has len(a) or len(a)+1 roots; check alternation of merged sorted list
    merged=sorted([(x,0) for x in a]+[(x,1) for x in b])
    labs=[l for _,l in merged]
    return all(labs[i]!=labs[i+1] for i in range(len(labs)-1))
print("k with interlacing h_k,h_{k+1} (2<=k<=29):",[k for k in range(2,KM) if interlace(roots[k],roots[k+1])])
print("signs of roots of h_10:",np.round(roots[10],3))
