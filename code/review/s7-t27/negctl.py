# Negative controls: the checks must be able to FAIL.
from run_t27 import *

T = E1()
LA, sol, nullity, win, nrows, ncols = find_recurrence(T, WINDOWS)
bad = {iw: list(c) for iw, c in sol.items()}
first = sorted(bad)[0]
bad[first][0] += 1                                  # corrupt one coefficient
print("NEG1 corrupted coefficient -> polynomial identity holds?", LA.verify_identity(bad), "(expect False)")
pts = [(k, m, j) for k in range(0, 8) for m in range(0, 8) for j in range(-2, 9)]
st = check_F(LA, bad, pts)
print("NEG2 corrupted coefficient -> Lemma F recurrence failures:", st['rec_fail'], "(expect >0)")
# wrong T*: shift dmax by one -> identity T(p-w)=T*(p)Q_w(p) must break
LA.dmax = [x + 1 for x in LA.dmax]
st2 = check_F(LA, sol, [(k, m, j) for k in range(3, 8) for m in range(3, 8) for j in range(0, 4)]) if False else None
cnt = 0
for p in [(k, m, j) for k in range(3, 8) for m in range(3, 8) for j in range(0, 4)]:
    ts = LA.Tstar(p)
    if ts is None:
        continue
    for iw in range(len(LA.Om)):
        if T.val(sub(p, LA.Om[iw])) != ts * LA.Q_prod(iw, p):
            cnt += 1
print("NEG3 anchor d_max+1 (above d_max) -> identity mismatches:", cnt, "(expect 0: any anchor >= d_max is valid)")
# Added when copied into the repository (2026-10-07, main agent): the real negative control is an anchor BELOW d_max.
LA.dmax = [x - 2 for x in LA.dmax]                  # net effect: d_max - 1
cnt_low = 0
tried = 0
for p in [(k, m, j) for k in range(3, 8) for m in range(3, 8) for j in range(0, 4)]:
    ts = LA.Tstar(p)
    if ts is None:
        continue
    for iw in range(len(LA.Om)):
        tried += 1
        if T.val(sub(p, LA.Om[iw])) != ts * LA.Q_prod(iw, p):
            cnt_low += 1
print("NEG3b anchor d_max-1 (below d_max) -> identity mismatches:", cnt_low, "of", tried, "(expect >0)")
LA.dmax = [x + 1 for x in LA.dmax]                  # restore d_max
# Lemma S with a non-minimal alpha (alpha=(1,) when C_0 != 0) must NOT give C_alpha S = 0 in general
LA = LemmaA(T, *win[:2])
C, nonzero, minimal, _ = lemmaS_ops(LA, sol)
S = make_S(T, jbox(1, -8, 40))
nonmin = [al for al in nonzero if al not in minimal]
for al in nonmin:
    vals = [apply_C(C[al], S, k, m) for k in range(3, 9) for m in range(3, 9)]
    print(f"NEG4 non-minimal alpha={al}: C_alpha S nonzero at {sum(v != 0 for v in vals)}/36 points (expect >0)")
