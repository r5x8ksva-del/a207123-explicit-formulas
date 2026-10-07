# Section 4 checks: block factorization, explicit formulas, r-Stirling, bijection, F3, F4, 1F1
import sys, math
from itertools import product, combinations
sys.path.insert(0, r"C:\Users\Michael Song\Desktop\私人办公\A207123-任务C-显式公式与母函数\code")
from core import U_fast_table, good, stirling2_table, h_complete
from fractions import Fraction

def binom(a,b):
    return math.comb(a,b) if 0<=b<=a else 0
def goodseqs(k,m):
    out=[]
    def rec(seq):
        if len(seq)==k: out.append(tuple(seq)); return
        for v in range(m+1):
            if len(seq)>=2 and not good(seq[-2],seq[-1],v): continue
            seq.append(v); rec(seq); seq.pop()
    rec([]); return out
T=U_fast_table(14,7)
S2=stirling2_table(40)
def H(m,s,j):
    if s<0: return 0
    return h_complete(s,j,m)
def asc(h): return sum(1 for i in range(len(h)-1) if h[i]<h[i+1])

# --- unique factorization (Thm blocks) ---
def factor(h):
    blocks=[]; i=0; h=list(h)
    while i<len(h):
        M=max(h[i:])
        if h[i]==M: blocks.append(('S',M,None)); i+=1
        elif i+1==len(h)-1: blocks.append(('E',h[i+1],h[i])); i+=2
        else:
            assert h[i+1]==M and h[i+2]==M
            blocks.append(('T',M,h[i])); i+=3
    return blocks
def concat(blocks):
    out=[]
    for t,v,a in blocks:
        out+= [v] if t=='S' else ([a,v,v] if t=='T' else [a,v])
    return out
def all_block_seqs(k,m):
    # enumerate block sequences of total length k with weakly decreasing levels, only last may be E
    res=[]
    def rec(rem, maxlev, cur):
        if rem==0: res.append(tuple(cur)); return
        for v in range(maxlev,-1,-1):
            # S
            cur.append(('S',v,None)); rec(rem-1,v,cur); cur.pop()
            for a in range(v):
                if rem>=3: cur.append(('T',v,a)); rec(rem-3,v,cur); cur.pop()
                if rem==2: cur.append(('E',v,a)); rec(0,v,cur); cur.pop()
    rec(k,m,[]); return res
okf=True
for k in range(0,9):
    for m in range(0,4):
        gs=goodseqs(k,m)
        bs=all_block_seqs(k,m)
        cs=[tuple(concat(b)) for b in bs]
        if len(set(cs))!=len(cs) or set(cs)!=set(gs) or len(gs)!=T[k][m]: okf=False; print("blocks fail",k,m)
        for h in gs:
            if tuple(concat(factor(h)))!=h: okf=False
print("Unique factorization (k<=8,m<=3):", okf)
print("Example factorization:", factor((3,1,3,3,2,0,2,2,1,0,1)))

# --- explicit formulas ---
def Uformula(k,m):
    s1=sum(S2[m+s][m]*binom(k+m-2*s,k-3*s) for s in range(0,k//3+1))
    s2=sum(j*sum(H(m,s,j)*binom(k-2+m-j-2*s,k-2-3*s) for s in range(0,k//3+1)) for j in range(1,m+1))
    return s1+s2
def Usformula(k,m,s):
    t1=S2[m+s][m]*binom(k+m-2*s,k-3*s) if s>=0 else 0
    t2=sum(j*H(m,s-1,j)*binom(k+m-j-2*s,k+1-3*s) for j in range(1,m+1))
    return t1+t2
oke=all(Uformula(k,m)==T[k][m] for k in range(0,15) for m in range(0,8))
print("Thm explicit (first formula) k<=14,m<=7:", oke)
okes=True
for k in range(0,11):
    for m in range(0,5):
        gs=goodseqs(k,m)
        for s in range(0,k+1):
            cnt=sum(1 for h in gs if asc(h)==s)
            if cnt!=Usformula(k,m,s): okes=False; print("Us fail",k,m,s,cnt,Usformula(k,m,s))
print("Thm explicit (ascent refinement) k<=10,m<=4:", okes)

# --- lemma coef: coefficients of prod_{v=j}^m 1/(1-x-v y x^3) ---
def series2(j,m,N):
    # dict (n,s)->coef, truncated at x^N
    cur={(0,0):1}
    for v in range(j,m+1):
        # multiply by 1/(1-x-v y x^3): new[n,s] = cur[n,s] + new[n-1,s] + v*new[n-3,s-1]
        new={}
        for n in range(N+1):
            for s in range(0,n//3+1):
                val=cur.get((n,s),0)+new.get((n-1,s),0)+v*new.get((n-3,s-1),0)
                if val: new[(n,s)]=val
        cur=new
    return cur
okc=True
for m in range(0,5):
    for j in range(0,m+1):
        ser=series2(j,m,15)
        for n in range(16):
            for s in range(0,n//3+2):
                if ser.get((n,s),0)!=H(m,s,j)*binom(n+m-j-2*s,n-3*s): okc=False; print("coef fail",m,j,n,s)
print("Lemma coef series identity (m<=4,n<=15):", okc)
print("H(m,s,0)=H(m,s,1)=S(m+s,m):", all(H(m,s,0)==H(m,s,1)==S2[m+s][m] for m in range(1,7) for s in range(0,7)))

# r-Stirling via brute force set partitions
def set_partitions(n):
    if n==0: yield []; return
    for p in set_partitions(n-1):
        for i in range(len(p)):
            yield p[:i]+[p[i]+[n]]+p[i+1:]
        yield p+[[n]]
okr=True
for m in range(1,5):
    for s in range(0,4):
        parts=[p for p in set_partitions(m+s) if len(p)==m]
        for j in range(1,m+1):
            cnt=sum(1 for p in parts if len({next(bi for bi,B in enumerate(p) if e in B) for e in range(1,j+1)})==j)
            if cnt!=H(m,s,j): okr=False; print("rStirling fail",m,s,j,cnt,H(m,s,j))
print("r-Stirling identification (m<=4,s<=3):", okr)

# --- Prop bijection ---
def forward(h,m):
    blocks=factor(h)
    assert all(t!='E' for t,_,_ in blocks)
    # word: start at level m; bar when level drops by one; bars at the end down to 0
    word=[]; lev=m; info=[]
    for t,v,a in blocks:
        while lev>v: word.append(('|',None)); lev-=1
        word.append((t,a))
    while lev>0: word.append(('|',None)); lev-=1
    Spos=frozenset(i+1 for i,(t,_) in enumerate(word) if t=='S')
    tb=[w for w in word if w[0]!='S']  # T and | letters, left to right
    L=len(tb)
    num=lambda idx: L-idx  # right-to-left numbering 1..L
    bars=[idx for idx,w in enumerate(tb) if w[0]=='|']
    bars_from_right=sorted(bars, key=lambda idx: -idx)  # first = rightmost
    blocks_part={num(b):{num(b)} for b in bars}
    for idx,w in enumerate(tb):
        if w[0]=='T':
            a=w[1]; opener=bars_from_right[a]   # (a+1)-st bar from the right
            assert opener>idx
            blocks_part[num(opener)].add(num(idx))
    part=frozenset(frozenset(B) for B in blocks_part.values())
    return (Spos,part)
def backward(Spos,part,k,m,s):
    n=k+m-2*s
    L=m+s
    mins=sorted(min(B) for B in part)
    rank={}
    for B in part:
        r=mins.index(min(B))+1
        for e in B: rank[e]=r
    # T/| letters numbered right to left 1..L; build left-to-right list
    tb=[]
    for idx in range(L):
        e=L-idx
        if e in mins: tb.append(('|',None))
        else: tb.append(('T',rank[e]-1))
    word=[]; it=iter(tb)
    for pos in range(1,n+1):
        word.append(('S',None) if pos in Spos else next(it))
    # levels = number of bars to the right
    seq=[]
    for i,(t,a) in enumerate(word):
        if t=='|': continue
        v=sum(1 for w in word[i+1:] if w[0]=='|')
        if t=='S': seq.append(v)
        else:
            assert a<v
            seq+= [a,v,v]
    return tuple(seq)
okb=True; tested=0
for k in range(0,10):
    for m in range(4,5):
        gs=[h for h in goodseqs(k,m) if not (len(h)>=2 and h[-2]<h[-1])]
        for s in range(0,k//3+1):
            src=[h for h in gs if asc(h)==s]
            imgs=[forward(h,m) for h in src]
            # target set size
            tgt=binom(k+m-2*s,k-3*s)*S2[m+s][m]
            if len(set(imgs))!=len(src) or len(src)!=tgt: okb=False; print("bij size fail",k,m,s,len(src),len(set(imgs)),tgt)
            for h,(Sp,pa) in zip(src,imgs):
                tested+=1
                if len(Sp)!=k-3*s or any(not(1<=x<=k+m-2*s) for x in Sp) or len(pa)!=m or set().union(*pa)!=set(range(1,m+s+1)) if m+s>0 else False:
                    okb=False; print("bad image",h)
                if backward(Sp,pa,k,m,s)!=h: okb=False; print("inverse fail",h)
        # surjectivity check for small: all pairs map back to valid good sequences
        for s in range(0,k//3+1):
            parts=[frozenset(frozenset(B) for B in p) for p in set_partitions(m+s) if len(p)==m] if m+s>0 else ([frozenset()] if m==0 else [])
            for Sp in combinations(range(1,k+m-2*s+1),k-3*s):
                for pa in parts:
                    h=backward(frozenset(Sp),pa,k,m,s)
                    if forward(h,m)!=(frozenset(Sp),pa) or len(h)!=k or asc(h)!=s or any(not good(*h[i:i+3]) for i in range(len(h)-2)) or max(h,default=0)>m:
                        okb=False; print("surj fail",k,m,s,Sp,pa); break
print("Prop bijection: forward injective, inverse correct, surjective (k<=9,m=4); tested",tested, okb)

# --- Example m1, Remark forms F3, F4 ---
print("Example m=1, U_5(1):", sum(binom(5+1-2*s,s+1) for s in range(0,5)), sum(binom(5-2-2*s,s) for s in range(0,5)))
def F3(k,m):
    t1=sum(S2[m+s][m]*binom(k+1+m-2*s,m+s) for s in range(0,k+3))
    t2=sum(H(m,s,j)*binom(k+m-j-2*s,m-j+s) for j in range(1,m+1) for s in range(0,k+3))
    return t1-t2
def ci(i,n):
    if n<0: return 0
    return sum(binom(n-2*l,l)*i**l for l in range(0,n//3+1))
def F4(k,m):
    tot=0
    for i in range(0,m+1):
        inner=ci(i,k+3*m)+sum(j*math.perm(i,j)*ci(i,k+3*m-3*j-2) for j in range(1,i+1))
        tot+=(-1)**(m-i)*math.comb(m,i)*inner
    return Fraction(tot,math.factorial(m))
print("F3:", all(F3(k,m)==T[k][m] for k in range(0,15) for m in range(0,8)))
print("F4:", all(F4(k,m)==T[k][m] for k in range(0,15) for m in range(0,8)))
# 1F1: coefficient of t^n: (1/(1-x)) (-1/x^3)^n/(1-lambda)_n  vs 1/P_n, test at x=1/3, 2/7
for x in (Fraction(1,3),Fraction(2,7)):
    lam=(1-x)/x**3
    ok=True
    for n in range(0,7):
        poch=Fraction(1)
        for i in range(n): poch*=(1-lam+i)
        lhs=Fraction(1)/(1-x)*(Fraction(-1)/x**3)**n/poch
        Pn=Fraction(1)
        for i in range(0,n+1): Pn*=(1-x-i*x**3)
        ok&= (lhs==1/Pn)
    print("1F1 identity at x=",x,ok)
