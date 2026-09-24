#!/usr/bin/env python3
"""usage: python3 python/jcheck_bernoulli.py [K=1100]
Independent J_s = int_{Z_2} (t+1/2)^{-s} dt = 2^s sum_j C(-s,j) 2^j B_j  (Volkenborn moments = Bernoulli B_j, B_1=-1/2),
compare with the project cache and check v2(S_n) = target(m) for n = 2^m-1 via L1."""
import sys, json, os
from fractions import Fraction as F
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import audit_independent as A
if hasattr(sys, "set_int_max_str_digits"): sys.set_int_max_str_digits(0)

def tangent_numbers(n):
    # Brent-Harvey: T[k] = tangent number T_{2k-1}, k=1..n
    T = [0] * (n + 1); T[1] = 1
    for k in range(2, n + 1): T[k] = (k - 1) * T[k - 1]
    for k in range(2, n + 1):
        for j in range(k, n + 1):
            T[j] = (j - k) * T[j - 1] + (j - k + 2) * T[j]
    return T

def bernoulli_even(nmax):
    kmax = nmax // 2
    T = tangent_numbers(kmax)
    B = {0: F(1), 1: F(-1, 2)}
    for k in range(1, kmax + 1):
        B[2 * k] = F((-1) ** (k - 1) * 2 * k * T[k], 4 ** k * (4 ** k - 1))
    return B

K = int(sys.argv[1]) if len(sys.argv) > 1 else 1100
JMAX = K + 40
B = bernoulli_even(JMAX)
assert B[2] == F(1, 6) and B[4] == F(-1, 30) and B[12] == F(-691, 2730)
def binom_neg(s, j):  # C(-s, j)
    r = F(1)
    for i in range(j): r = r * (-s - i) / (i + 1)
    return r
J = {}
for s in range(1, 13):
    tot = F(0)
    for j in range(0, JMAX + 1):
        if j >= 3 and j % 2 == 1: continue
        tot += binom_neg(s, j) * F(2) ** j * B[j]
    J[s] = F(2) ** s * tot
    print("s=%2d: v2(J_s approx) = %s" % (s, A.vp(J[s], 2)))
# odd s: J_s should be ~0 (zeta_2(even)=0): check v2 >= K - 5
for s in (1, 3, 5, 7, 9, 11):
    A.check("J_odd s=%d ~ 0" % s, A.vp(J[s], 2) >= K - 20, A.vp(J[s], 2))
# compare with project cache: zeta2_K17000.json, J_{m-1} = (m-1) 2^m zeta2(m) = (m-1) 2^m Z 2^{-sh}
d = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "zeta2_K17000.json")))
for key, v in d.items():
    m = int(key); Z = int(v[0]); sh = int(v[1]); s = m - 1
    if s < 1 or s > 12: continue
    cache = F(s) * F(2) ** m * F(Z) / F(2) ** sh
    dv = A.vp(cache - J[s], 2)
    print("  cache vs Bernoulli: s=%d  v2(diff) = %s" % (s, dv if dv < 10**8 else "inf"))
    A.check("cache s=%d" % s, dv >= K - 20, dv)
# L5 limit valuations
for m in range(2, 6):
    n = 2 ** m - 1
    if A.target(m) > K - 100:
        print("  m=%d skipped (target %d needs K > %d)" % (m, A.target(m), A.target(m) + 100)); continue
    S = A.rho0(n) + 60 * A.csum(n, 3) * J[6] + 210 * A.csum(n, 5) * J[8] + 504 * A.csum(n, 7) * J[10]
    v = A.vp(S, 2)
    print("  m=%d n=%d: v2(S_n) = %d, target = %d" % (m, n, v, A.target(m)))
    A.check("L5 limit m=%d" % m, v == A.target(m) and v < K - 60, (v, A.target(m)))
print("FAILS:", len(A.FAILS))
