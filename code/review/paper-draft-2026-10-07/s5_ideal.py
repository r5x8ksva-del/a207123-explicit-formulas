# Section 5: dimension of box spaces of annihilating operators, mod-p linear algebra on a window
import sys, math
import numpy as np
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table, N_from_U
p=2147483647
K=M=40
T=U_fast_table(K,M)
Umod=[[T[k][m]%p for m in range(M+1)] for k in range(K+1)]
def rank_mod(A):
    A=A.copy()%p; r=0; rows,cols=A.shape
    for c in range(cols):
        piv=None
        for i in range(r,rows):
            if A[i,c]!=0: piv=i; break
        if piv is None: continue
        A[[r,piv]]=A[[piv,r]]
        inv=pow(int(A[r,c]),p-2,p)
        A[r]=(A[r]*inv)%p
        col=A[:,c].copy(); col[r]=0
        nz=np.nonzero(col)[0]
        if len(nz):
            A[nz]=(A[nz]-(col[nz,None]*A[r][None,:])%p)%p
        r+=1
        if r==rows: break
    return r
def kernel_dim(F, A,B,mons, kmin,mmin):
    cols=[(a,b,i,j) for a in range(A+1) for b in range(B+1) for (i,j) in mons]
    rowsl=[]
    for k in range(kmin,K+1):
        for m in range(mmin,M+1):
            rowsl.append([ (pow(k,i,p)*pow(m,j,p)%p)*(F[k-a][m-b] if k>=a and m>=b else 0)%p for (a,b,i,j) in cols])
    Amat=np.array(rowsl,dtype=np.int64)
    return len(cols)-rank_mod(Amat)
def tot(D): return [(i,j) for i in range(D+1) for j in range(D+1-i)]
def sep(Dk,Dm): return [(i,j) for i in range(Dk+1) for j in range(Dm+1)]
print("U, total degree:")
for (A,B,D) in [(3,1,1),(3,1,0),(2,3,3),(4,2,2),(5,1,2),(4,3,1),(6,2,1),(3,2,3)]:
    pred=(A-2)*B*D*(D+1)//2 if (A>=3 and B>=1 and D>=1) else 0
    kd=kernel_dim(Umod,A,B,tot(D),A+3,B+1)
    print(" (A,B,D)=",(A,B,D),"kernel dim mod p:",kd,"predicted:",pred)
print("U, separate degrees:")
for (A,B,Dk,Dm) in [(4,2,1,2),(3,1,0,1),(3,2,2,1),(4,1,1,0),(5,2,0,2)]:
    pred=(A-2)*B*(Dk+1)*Dm if (A>=3 and B>=1 and Dm>=1) else 0
    kd=kernel_dim(Umod,A,B,sep(Dk,Dm),A+3,B+1)
    print(" (A,B,Dk,Dm)=",(A,B,Dk,Dm),"kernel dim mod p:",kd,"predicted:",pred)
# Triangle N: box dims (A-2)(B-1)D(D+1)/2
Nmod=[[ (N_from_U(T,k,q) if q<=k else 0)%p for q in range(M+1)] for k in range(K+1)]
print("N, total degree:")
for (A,B,D) in [(3,2,1),(4,2,2),(3,3,1),(4,3,2),(3,1,2),(2,3,2)]:
    pred=(A-2)*(B-1)*D*(D+1)//2 if (A>=3 and B>=2 and D>=1) else 0
    kd=kernel_dim(Nmod,A,B,tot(D),A+3,B+1)
    print(" (A,B,D)=",(A,B,D),"kernel dim mod p:",kd,"predicted:",pred)
