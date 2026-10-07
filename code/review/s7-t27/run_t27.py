import sys, time, itertools, random
from fractions import Fraction
from math import comb, factorial
from t27lib import *

# ---------------- examples (variables ordered (k, m, j1, ..., jr)) ----------------
def E1():
    return Term("E1 C(m,j)C(k,j)",
                num=[((0, 1, 0), 0), ((1, 0, 0), 0)],
                den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0)])

def E2():
    return Term("E2 C(k+j,2j)C(m,j)",
                num=[((1, 0, 1), 0), ((0, 1, 0), 0)],
                den=[((0, 0, 2), 0), ((1, 0, -1), 0), ((0, 0, 1), 0), ((0, 1, -1), 0)])

def E5():   # P = k+2j+1, z = (-1, 3, 2)
    return Term("E5 (k+2j+1)(-1)^k 3^m 2^j C(m,j)C(k,j)",
                num=[((0, 1, 0), 0), ((1, 0, 0), 0)],
                den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0)],
                P={(1, 0, 0): 1, (0, 0, 1): 2, (0, 0, 0): 1}, z=(-1, 3, 2))

def E6():   # r=2: C(k,j1)C(j1,j2)C(m,j2) with j1! cancelled
    return Term("E6 C(k,j1)C(j1,j2)C(m,j2) [r=2]",
                num=[((1, 0, 0, 0), 0), ((0, 1, 0, 0), 0)],
                den=[((1, 0, -1, 0), 0), ((0, 0, 1, -1), 0), ((0, 0, 0, 1), 0), ((0, 0, 0, 1), 0),
                     ((0, 1, 0, -1), 0)], r=2)

def E3():   # violates (N2): (2j)! numerator; Gamma-continuation has zeros
    return Term("E3 C(2j,j)C(k,j)C(m,j) [no N2]",
                num=[((0, 0, 2), 0), ((1, 0, 0), 0), ((0, 1, 0), 0)],
                den=[((0, 0, 1), 0)] * 4 + [((1, 0, -1), 0), ((0, 1, -1), 0)])

def E4():   # violates (N2): (j-1)! numerator; Gamma-continuation has a pole at j=0
    return Term("E4 C(k,j)C(m,j)*(j-1)!/j! [no N2]",
                num=[((1, 0, 0), 0), ((0, 1, 0), 0), ((0, 0, 1), -1)],
                den=[((0, 0, 1), 0)] * 3 + [((1, 0, -1), 0), ((0, 1, -1), 0)])

def E7u():  # note's scope example, unreduced: C(m,j)C(k,j) j!/(j+1)!
    return Term("E7u C(m,j)C(k,j)*j!/(j+1)! [no N2]",
                num=[((0, 1, 0), 0), ((1, 0, 0), 0), ((0, 0, 1), 0)],
                den=[((0, 0, 1), 0), ((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 1)])

def E7r():  # reduced: j! cancelled
    return Term("E7r C(m,j)C(k,j)/(j+1) reduced",
                num=[((0, 1, 0), 0), ((1, 0, 0), 0)],
                den=[((0, 1, -1), 0), ((0, 0, 1), 0), ((1, 0, -1), 0), ((0, 0, 1), 1)])

def E8():   # C(2j,j) C(m, j-k): contains C(2j,j) with integer constants, yet satisfies (N2)
    return Term("E8 C(2j,j)C(m,j-k)",
                num=[((0, 0, 2), 0), ((0, 1, 0), 0)],
                den=[((0, 0, 1), 0), ((0, 0, 1), 0), ((-1, 0, 1), 0), ((1, 1, -1), 0)])

WINDOWS = [(1, 1, 0), (1, 1, 1), (2, 1, 0), (1, 2, 0), (2, 1, 1), (1, 2, 1), (2, 2, 0), (2, 2, 1),
           (1, 2, 2), (2, 2, 2), (3, 2, 1), (2, 3, 1), (3, 2, 2), (2, 3, 2), (3, 3, 2)]


def counting_report(T):
    beta, gamma, degP = T.beta_gamma()
    r = T.r
    J0 = 0
    while not (J0 + 1) * factorial(r + 1) > beta ** (r + 1):
        J0 += 1
    I = 0
    while True:
        D = degP + beta * I + gamma * J0
        if (J0 + 1) * (I + 1) ** (r + 1) > comb(D + r + 1, r + 1):
            break
        I += 1
    D = degP + beta * I + gamma * J0
    return (f"beta={beta} gamma={gamma} degP={degP}; J0={J0} (J0+1>{beta**(r+1)}/{factorial(r+1)}); "
            f"first I with unknowns>equations: I={I}: {(J0+1)*(I+1)**(r+1)} > C({D+r+1},{r+1})={comb(D+r+1,r+1)}; "
            f"at I-1: {(J0+1)*I**(r+1)} vs {comb(degP+beta*(I-1)+gamma*J0+r+1,r+1)}")


def jbox(r, lo, hi):
    return list(itertools.product(range(lo, hi + 1), repeat=r))


def check_F(LA, sol, pts):
    T = LA.T
    st = dict(points=0, allwd=0, pairs=0, id_fail=0, rec_fail=0, boundary=0, Tstar0=0,
              case=[0, 0, 0], case2_nonzero_nb=0)
    zero = LA.Om.index((0,) * T.n)
    for p in pts:
        st['points'] += 1
        vals = [T.val(sub(p, w)) for w in LA.Om]
        if any(v is None for v in vals):
            continue
        st['allwd'] += 1
        ts = LA.Tstar(p)
        assert ts is not None, "T*(p) numerator negative at an all-well-defined point"
        if ts == 0:
            st['Tstar0'] += 1
        for iw in range(len(LA.Om)):
            st['pairs'] += 1
            if vals[iw] != ts * LA.Q_prod(iw, p):
                st['id_fail'] += 1
            for s, B in enumerate(T.den):
                b = lin(B, p)
                if b - LA.e[s][iw] >= 0:
                    st['case'][0] += 1
                elif b - LA.emin[s] >= 0:
                    st['case'][1] += 1
                    if any(v != 0 for v in vals):
                        st['case2_nonzero_nb'] += 1
                else:
                    st['case'][2] += 1
        rec = sum(uni_eval(sol[iw], p[0]) * vals[iw] for iw in sol)
        if rec != 0:
            st['rec_fail'] += 1
        if vals[zero] == 0 and any(v != 0 for v in vals):
            st['boundary'] += 1
    return st


def tilde_rec(LA, sol, kms, jb):
    T = LA.T
    fails, nall, ntriv, nmixed = [], 0, 0, 0
    for (k, m) in kms:
        for jv in jb:
            p = (k, m) + jv
            vals = [T.val(sub(p, w)) for w in LA.Om]
            tv = [Fraction(0) if v is None else v for v in vals]
            rec = sum(uni_eval(sol[iw], k) * tv[iw] for iw in sol)
            if all(v is not None for v in vals):
                nall += 1
            elif all(x == 0 for x in tv):
                ntriv += 1
            else:
                nmixed += 1
            if rec != 0:
                fails.append((p, rec))
    return fails, nall, ntriv, nmixed


def make_S(T, jb):
    cache = {}
    def S(k, m):
        if (k, m) not in cache:
            tot = Fraction(0)
            for jv in jb:
                v = T.tilde((k, m) + jv)
                if v != 0:
                    assert all(jb[0][i] + 2 < jv[i] < jb[-1][i] - 2 for i in range(len(jv))), "support touches j-box edge"
                tot += v
            cache[(k, m)] = tot
        return cache[(k, m)]
    return S


def apply_C(Cal, S, k, m):
    return sum(uni_eval(pol, k) * S(k - jk, m - mu) for (jk, mu), pol in Cal.items())


def moment_check(T, C, astar, kms, jb):
    """sum_j C(j,a*) ((sigma-1)^al Tt)(k,m,j) == sum_j C(j,a*-al) Tt (al<=a*), else 0"""
    r = T.r
    bad = 0
    nchk = 0
    for al in C:
        for (k, m) in kms:
            f = lambda jv, k=k, m=m: T.tilde((k, m) + jv)
            lhs = sum(prod_binom(jv, astar) * sigma_minus_1_pow(f, al, jv) for jv in jb)
            if all(a <= b for a, b in zip(al, astar)):
                rhs = sum(prod_binom(jv, tuple(b - a for a, b in zip(al, astar))) * f(jv) for jv in jb)
            else:
                rhs = 0
            nchk += 1
            if lhs != rhs:
                bad += 1
    return nchk, bad


def prod_binom(jv, al):
    v = Fraction(1)
    for x, b in zip(jv, al):
        v *= binom_poly(x, b)
    return v


def n2_check(T, R, kR, mR, kmax, mmax, jb, brute=True):
    """(N2) on [kR..kmax]x[mR..mmax]: every wd & nonzero point has all sup-R neighbours wd."""
    fails = []
    for k in range(kR, kmax + 1):
        for m in range(mR, mmax + 1):
            for jv in jb:
                p = (k, m) + jv
                v = T.val(p)
                if v is None or v == 0:
                    continue
                if brute:
                    for d in itertools.product(range(-R, R + 1), repeat=T.n):
                        if not T.wd(tuple(a + b for a, b in zip(p, d))):
                            fails.append(p)
                            break
                else:
                    if any(lin(A, p) - R * sum(abs(c) for c in A[0]) < 0 for A in T.num):
                        fails.append(p)
                if len(fails) > 3:
                    return fails
    return fails


def show_sol(LA, sol, maxterms=40):
    parts = []
    for iw in sorted(sol):
        pol = sol[iw]
        if any(pol):
            parts.append(f"{LA.Om[iw]}:{pol}")
    s = "; ".join(parts)
    return s if len(parts) <= maxterms else s[:400] + " ..."


def full_run(T, n2corner, box_k=(-2, 11), box_m=(-2, 11), jlo=-5, jhi=13, deep=(0, 14), extra_C0=False,
             windows=WINDOWS, label=""):
    t0 = time.time()
    r = T.r
    print(f"\n===== {T.name} {label}=====")
    print("  counting:", counting_report(T))
    res = find_recurrence(T, windows, extra_C0=extra_C0)
    if res is None:
        print("  Lemma A: no solution found in searched windows")
        return None
    LA, sol, nullity, (J, I, dk), nrows, ncols = res
    print(f"  Lemma A: window (J,I)=({J},{I}), deg_k<= {dk}: system {nrows} eqs x {ncols} unknowns, "
          f"nullity found={nullity}; exact polynomial identity verified; "
          f"max deg_(m,j) Q_w={LA.mj_degree()} <= D={LA.D_bound()}: {LA.mj_degree() <= LA.D_bound()}")
    print("    a_w(k) (nonzero):", show_sol(LA, sol))
    # Q_poly vs Q_prod spot check
    rnd = random.Random(5)
    mism = 0
    for _ in range(30):
        p = tuple(rnd.randint(-6, 12) for _ in range(T.n))
        for iw in range(len(LA.Om)):
            if LA.Q_poly(iw, p) != LA.Q_prod(iw, p):
                mism += 1
    print(f"    expanded Q_w == product-form Q_w at 30 random points: {mism == 0}")
    # Lemma F
    pts = [(k, m) + jv for k in range(*box_k) for m in range(*box_m) for jv in jbox(r, jlo, jhi)]
    st = check_F(LA, sol, pts)
    print(f"  Lemma F on {st['points']} points: all-window-wd points={st['allwd']}, (p,w) identity checks={st['pairs']}, "
          f"identity failures={st['id_fail']}, recurrence failures={st['rec_fail']}, boundary points (T(p)=0, window nonzero)={st['boundary']}, "
          f"T*(p)=0 points={st['Tstar0']}, denominator cases (1,2,3)={st['case']}")
    # Lemma S
    C, nonzero, minimal, inv_ok = lemmaS_ops(LA, sol)
    print(f"  Lemma S: C_alpha nonzero for alpha in {nonzero}; minimal: {minimal}; triangular inversion recovers A_nu: {inv_ok}")
    kR, mR = n2corner(max(J, I))
    k0p, m0p = kR + J, mR + I
    jb_sum = jbox(r, jlo - 3, jhi + 12) if r == 1 else jbox(r, -4, deep[1] + 4)
    S = make_S(T, jb_sum)
    for astar in minimal:
        Cal = C[astar]
        vals = [(k, m, apply_C(Cal, S, k, m)) for k in range(k0p, k0p + 8) for m in range(m0p, m0p + 8)]
        nz = [v for v in vals if v[2] != 0]
        print(f"    alpha*={astar}: C_alpha* = {{(j,mu): c(k)}} = {dict(sorted(Cal.items()))}")
        print(f"    (C_alpha* S)(k,m) on Q'=[k>={k0p}, m>={m0p}] (8x8 points): nonzero at {len(nz)} points"
              + (f", e.g. {nz[:2]}" if nz else ""))
        kms = [(k0p + 1, m0p + 2), (k0p + 3, m0p)]
        jb_m = jbox(r, jlo - 2, jhi + 8) if r == 1 else jbox(r, -4, 12)
        nchk, bad = moment_check(T, C, astar, kms, jb_m)
        print(f"    summation-by-parts moment identities: {nchk} checks, {bad} failures")
    # assembly: hypothesis of Lemma S on Q'
    kms = [(k, m) for k in range(k0p, k0p + 5) for m in range(m0p, m0p + 5)]
    fails, nall, ntriv, nmixed = tilde_rec(LA, sol, kms, jbox(r, jlo - 2, jhi + 6) if r == 1 else jbox(r, -3, 11))
    print(f"  Assembly: R=max(J,I)={max(J, I)}, Q_R corner={kR, mR}, Q' corner={(k0p, m0p)}; on 5x5 (k,m) of Q' x j-box: "
          f"T~-recurrence failures={len(fails)}; windows all-wd={nall}, trivial(all T~=0)={ntriv}, mixed={nmixed}")
    # outside Q' (small k or m): does the T~ recurrence fail? (shows Q' is needed)
    kms_out = [(k, m) for k in range(0, k0p) for m in range(0, 9)] + [(k, m) for k in range(0, 9) for m in range(0, m0p)]
    fo, _, _, mo = tilde_rec(LA, sol, kms_out, jbox(r, jlo, jhi) if r == 1 else jbox(r, -3, 10))
    print(f"    outside Q' (k<{k0p} or m<{m0p}, k,m<=8): T~-recurrence failures={len(fo)}, mixed windows={mo}")
    print(f"  time {time.time() - t0:.1f}s")
    return LA, sol, C, minimal, S


if __name__ == "__main__":
    which = sys.argv[1:] or ["E1"]
    for w in which:
        if w == "E1":
            full_run(E1(), lambda R: (R, R))
        elif w == "E1c0":
            full_run(E1(), lambda R: (R, R), extra_C0=True, label="[constrained C_0=0 => alpha*!=0] ")
        elif w == "E2":
            full_run(E2(), lambda R: (2 * R, R))
        elif w == "E2c0":
            full_run(E2(), lambda R: (2 * R, R), extra_C0=True, label="[constrained C_0=0 => alpha*!=0] ")
        elif w == "E5":
            full_run(E5(), lambda R: (R, R))
        elif w == "E6":
            full_run(E6(), lambda R: (R, R), box_k=(-1, 7), box_m=(-1, 7), jlo=-3, jhi=8, deep=(0, 10),
                     windows=[(1, 1, 0), (1, 1, 1), (2, 1, 0), (1, 2, 0)])
        elif w == "E6c0":
            full_run(E6(), lambda R: (R, R), box_k=(-1, 7), box_m=(-1, 7), jlo=-3, jhi=8, deep=(0, 10),
                     windows=[(1, 1, 0), (1, 1, 1), (2, 1, 0), (1, 2, 0)], extra_C0=True,
                     label="[constrained C_0=0] ")
