# -*- coding: utf-8 -*-
"""s10-b2: modular sieve and l-adic test for the fibre conditions of note 08 (own implementation).

For a certificate (i, l, P):  D_i(n,b) mod l = pi(eta^b) ^ pi(W eta^n)  computed in F_l[x]/(b_i),
where pi = (coefficient of eta, coefficient of eta^2).  The sieve evaluates this 2x2 wedge directly
on the full table (n0, b0) in (Z/T)^2 (chunked over b0); no projective-class shortcut.
l-adic: mu = (eta^P - 1)/l mod l, from eta^P mod l^2 (fast powering) and, independently, from the
exact value of eta^P in Z[1/i][eta] (big integers);  Delta_l(n) = pi(mu) ^ pi(W eta^n) mod l.
"""
import numpy as np
from s10lib import Kmod, Wtilde_poly, is_prime, prime_factors, exact_order_check, disc_b


def W_for(part, i):
    w = list(Wtilde_poly(i))
    if part == 'E':
        w[0] -= 1
    return w


class Cert:
    def __init__(self, i, l, P, part, Wpoly=None):
        self.i, self.l, self.P, self.part = i, l, P, part
        self.Wpoly = Wpoly if Wpoly is not None else W_for(part, i)
        K = Kmod(i, l)
        pb = np.zeros((P, 2), dtype=np.int64)
        e = (1, 0, 0)
        for b in range(P):
            pb[b, 0], pb[b, 1] = e[1], e[2]
            e = K.mul_eta(e)
        self.period_ok = (e == (1, 0, 0))
        w = K.ev(self.Wpoly)
        qn = np.zeros((P, 2), dtype=np.int64)
        e = w
        for n in range(P):
            qn[n, 0], qn[n, 1] = e[1], e[2]
            e = K.mul_eta(e)
        self.pb, self.qn = pb, qn

    # ---------------- l-adic data
    def mu_modular(self):
        l, P = self.l, self.P
        K2 = Kmod(self.i, l * l)
        e = K2.pow(K2.eta(), P)
        d = ((e[0] - 1) % (l * l), e[1] % (l * l), e[2] % (l * l))
        if any(c % l for c in d):
            return None
        return tuple((c // l) % l for c in d)

    def mu_exact(self):
        """eta^P exactly: numerators (c0,c1,c2) over i^k; then (eta^P - 1)/l mod l"""
        i, l, P = self.i, self.l, self.P
        c0, c1, c2 = 1, 0, 0
        for _ in range(P):
            c0, c1, c2 = c2, i * c0 - c2, i * c1       # multiply by eta, denominator gains a factor i
        den = pow(i, P)                                  # value = (c0 + c1 eta + c2 eta^2) / i^P
        l2 = l * l
        inv = pow(den % l2, -1, l2)
        v = ((c0 - den) * inv % l2, c1 * inv % l2, c2 * inv % l2)     # (eta^P - 1) mod l^2
        if any(c % l for c in v):
            return None
        return tuple((c // l) % l for c in v)

    def delta_good(self, mu):
        """boolean array over n in Z/P: Delta_l(n) != 0 mod l"""
        l = self.l
        d = (mu[1] * self.qn[:, 1] - mu[2] * self.qn[:, 0]) % l
        return d != 0


def verify_cert_static(i, l, P, T):
    """primality, l odd, l does not divide i, exact order, P | T; returns dict of facts"""
    return {
        'prime': is_prime(l),
        'odd': l % 2 == 1,
        'l_not_div_i': i % l != 0,
        'exact_order': exact_order_check(i, l, P),
        'P_div_T': T % P == 0,
        'l_not_div_disc': disc_b(i) % l != 0,
    }


def sieve(T, certs, chunk=512, want_list=20):
    """survivors (n0, b0) in (Z/T)^2 with b0 != 0 such that D_i(n0,b0) = 0 mod l for every cert.
    returns (number of survivors, sample list, per-cert kill counts in the given order)"""
    ar = np.arange(T)
    kills = [0] * len(certs)
    nsurv = 0
    sample = []
    for b_start in range(0, T, chunk):
        bs = ar[b_start:b_start + chunk]
        alive = np.ones((T, len(bs)), dtype=bool)
        alive[:, bs == 0] = False                       # b0 = 0 is not part of the sieve claim
        for ci, c in enumerate(certs):
            P, l = c.P, c.l
            PB = c.pb[bs % P]                           # (chunk, 2)
            QN = c.qn[ar % P]                           # (T, 2)
            D = (QN[:, 0][:, None] * PB[:, 1][None, :] - QN[:, 1][:, None] * PB[:, 0][None, :]) % l
            nz = D != 0
            killed_now = alive & nz
            kills[ci] += int(killed_now.sum())
            alive &= ~nz
            del D, nz, killed_now
        cnt = int(alive.sum())
        if cnt:
            nsurv += cnt
            if len(sample) < want_list:
                ns, bs_idx = np.nonzero(alive)
                for a, bb in zip(ns[:want_list], bs_idx[:want_list]):
                    sample.append((int(a), int(bs[bb])))
    return nsurv, sample, kills


def sieve_sparse(T, certs, chunk=128, dense_k=2, want_list=20):
    """same claim as sieve(), different algorithm: the first dense_k certs on the dense table
    (n0, b0-chunk), then the surviving pairs as index lists through the remaining certs."""
    ar = np.arange(T)
    nsurv = 0
    sample = []
    after_dense = 0
    for b_start in range(0, T, chunk):
        bs = ar[b_start:b_start + chunk]
        alive = np.ones((T, len(bs)), dtype=bool)
        alive[:, bs == 0] = False
        for c in certs[:dense_k]:
            P, l = c.P, c.l
            PB = c.pb[bs % P]
            QN = c.qn[ar % P]
            D = (QN[:, 0][:, None] * PB[:, 1][None, :] - QN[:, 1][:, None] * PB[:, 0][None, :]) % l
            alive &= (D == 0)
            del D
        ns, bi = np.nonzero(alive)
        bv = bs[bi]
        after_dense += len(ns)
        for c in certs[dense_k:]:
            if len(ns) == 0:
                break
            P, l = c.P, c.l
            q = c.qn[ns % P]
            p = c.pb[bv % P]
            D = (q[:, 0] * p[:, 1] - q[:, 1] * p[:, 0]) % l
            keep = D == 0
            ns, bv = ns[keep], bv[keep]
        if len(ns):
            nsurv += len(ns)
            for a, bb in zip(ns[:want_list], bv[:want_list]):
                if len(sample) < want_list:
                    sample.append((int(a), int(bb)))
    return nsurv, sample, after_dense


def padic_cover(T, certs, mus):
    """for every n0 in Z/T: first cert (in the given order) with Delta != 0; returns (uncovered list, first-hit counts)"""
    ar = np.arange(T)
    first = np.full(T, -1, dtype=np.int64)
    for ci, (c, mu) in enumerate(zip(certs, mus)):
        if mu is None:
            continue
        g = c.delta_good(mu)[ar % c.P]
        newly = (first < 0) & g
        first[newly] = ci
    unc = [int(n) for n in np.nonzero(first < 0)[0]]
    counts = [int((first == ci).sum()) for ci in range(len(certs))]
    return unc, counts, first
