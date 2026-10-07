# High-precision check of U_k(m) = c_m rho_m^k - c_{m-1} rho_{m-1}^{k+3} + O(tau_m^k)
import sys, math
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_column
from decimal import Decimal as D, getcontext
getcontext().prec = 400

def rho(m):
    if m==0: return D(1)
    y=D(2)
    for _ in range(200):
        y = y - (y**3-y**2-m)/(3*y**2-2*y)
    return y
def c(m):
    if m==0: return D(1)
    r=rho(m)
    s=D(1)+sum(D(j*math.perm(m,j))*r**(-3*j-2) for j in range(1,m+1))
    return r**(3*m+3)/(D(math.factorial(m))*(r*r+3*m))*s
for m in range(1,7):
    col=U_fast_column(m,400)
    rm,rm1=rho(m),rho(m-1)
    tau = (rho(1)*(rho(1)-1)).sqrt() if m==1 else max(rho(m-2),(rm*(rm-1)).sqrt())
    out=[]
    for k in (100,200,300,400):
        diff=D(col[k]) - c(m)*rm**k + c(m-1)*rm1**(k+3)
        out.append("%.4g"%(diff/tau**k))
    print("m",m,"tau=%.6f rho_{m-1}=%.6f"%(tau,rm1),"ratio (U-2 terms)/tau^k:",out)
print("c1..c3:", ["%.6f"%c(m) for m in (1,2,3)], "rho1=%.6f"%rho(1))
r=rho(1); print("c1 closed:", (10+15*r+17*r*r)/31 - c(1))
