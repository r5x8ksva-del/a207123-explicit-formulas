import sys, time
from run_t27 import *


def n2_report(T, corner_fn, Rs=range(0, 5), span=5, jb=None):
    out = []
    for R in Rs:
        kR, mR = corner_fn(R)
        brute = R <= 2 and T.r == 1 or R <= 1
        f = n2_check(T, R, kR, mR, kR + span, mR + span, jb, brute=brute)
        f2 = n2_check(T, R, kR, mR, kR + span, mR + span, jb, brute=False)
        assert bool(f) == bool(f2), "brute vs formula disagree"
        tk = n2_check(T, R, kR - 1, mR, kR - 1, mR + span, jb, brute=False) if kR - 1 >= 0 else None
        tm = n2_check(T, R, kR, mR - 1, kR + span, mR - 1, jb, brute=False) if mR - 1 >= 0 else None
        out.append(f"R={R}: Q_R=[k>={kR},m>={mR}] holds={not f}"
                   + (f"; k={kR-1} row fails={bool(tk)}" if tk is not None else "")
                   + (f"; m={mR-1} col fails={bool(tm)}" if tm is not None else ""))
    return out


def non_n2_run(T, deep=10, windows=WINDOWS, jlo=-6, jhi=14):
    t0 = time.time()
    r = T.r
    print(f"\n===== {T.name} =====")
    jb = jbox(r, jlo, jhi + deep)
    for R in (1, 2):
        f = n2_check(T, R, deep, deep, deep + 3, deep + 3, jb, brute=True)
        print(f"  (N2) at R={R} on [k,m in {deep}..{deep+3}]: violated={bool(f)}" + (f", e.g. wd&nonzero point {f[0]} has an ill-defined neighbour" if f else ""))
    res = find_recurrence(T, windows)
    if res is None:
        print("  Lemma A: none found")
        return
    LA, sol, nullity, (J, I, dk), nrows, ncols = res
    print(f"  Lemma A: window (J,I)=({J},{I}), deg_k<={dk}, nullity={nullity}; identity verified")
    print("    a_w(k):", show_sol(LA, sol))
    pts = [(k, m) + jv for k in range(-2, 11) for m in range(-2, 11) for jv in jbox(r, jlo, jhi)]
    st = check_F(LA, sol, pts)
    print(f"  Lemma F at all-window-wd points: {st['allwd']} points, identity failures={st['id_fail']}, recurrence failures={st['rec_fail']}, boundary pts={st['boundary']}")
    kms = [(k, m) for k in range(deep, deep + 5) for m in range(deep, deep + 5)]
    fails, nall, ntriv, nmixed = tilde_rec(LA, sol, kms, jbox(r, jlo, jhi + deep + 6))
    print(f"  T~-recurrence on deep 5x5 (k,m>={deep}) x j: failures={len(fails)}; windows all-wd={nall}, trivial={ntriv}, mixed(ill-defined & nonzero)={nmixed}")
    if fails:
        print(f"    first failures: {[(p, str(v)) for p, v in fails[:3]]}")
    C, nonzero, minimal, inv_ok = lemmaS_ops(LA, sol)
    S = make_S(T, jbox(r, jlo - 4, jhi + deep + 14))
    for astar in minimal:
        vals = [(k, m, apply_C(C[astar], S, k, m)) for k in range(deep, deep + 5) for m in range(deep, deep + 5)]
        nz = [v for v in vals if v[2] != 0]
        print(f"  Lemma S output alpha*={astar}, C={dict(sorted(C[astar].items()))}: (C S)(k,m) nonzero at {len(nz)}/25 deep points"
              + (f", e.g. {[(a, b, str(c)) for a, b, c in nz[:3]]}" if nz else ""))
    print(f"  time {time.time() - t0:.1f}s")
    return LA, sol, C, minimal, S


if __name__ == "__main__":
    which = sys.argv[1:]
    for w in which:
        if w == "N2":
            for T, fn in [(E1(), lambda R: (R, R)), (E2(), lambda R: (2 * R, R)), (E7r(), lambda R: (R, R)),
                          (E8(), lambda R: (R, R))]:
                print(f"\n(N2) check for {T.name}:")
                for line in n2_report(T, fn, jb=jbox(1, -12, 30)):
                    print("   ", line)
            T = E6()
            print(f"\n(N2) check for {T.name}:")
            for line in n2_report(T, lambda R: (R, R), Rs=range(0, 4), jb=jbox(2, -6, 14), span=3):
                print("   ", line)
            for T in (E3(), E7u()):
                f = n2_check(T, 1, 3, 3, 12, 12, jbox(1, -12, 30), brute=False)
                print(f"\n(N2) for {T.name} at R=1, k,m in 3..12: violated={bool(f)}; e.g. {f[:2]}")
        elif w == "E3":
            non_n2_run(E3())
        elif w == "E4":
            non_n2_run(E4())
        elif w == "E7u":
            non_n2_run(E7u())
        elif w == "E8":
            full_run(E8(), lambda R: (R, R), jlo=-5, jhi=26)
