"""Exact linear forms for the half-shift family
    R_n(t) = 2^{2an} (2t+n) (t+1/2)_n^a / (t)_{n+1}^a,   a even,
    S_n    = - int_{Z_2} R_n^{(j)}(t+1/2) dt   (j odd)
           = rho_0 + sum_i Z_i zeta_2(i+j+1),
    Z_i    = (i)_{j+1} 2^{i+j+1} c_i,  c_i = sum_k r_{i,k},
    rho_0  = - sum_{i,k} (i)_{j+1} r_{i,k} A_k^{(i+j+1)},   A_m^{(s)} = sum_{l<m} (l+1/2)^{-s}.
Partial fractions via  eps^a R(-k+eps) = (n-2k+2eps) (C(2k,k)C(2n-2k,n-k))^a exp(a sum_mu lambda_mu eps^mu),
    lambda_mu = (1/mu)[ -A_k^{(mu)} + (-1)^{mu-1} A_{n-k}^{(mu)} + H_k^{(mu)} - (-1)^{mu-1} H_{n-k}^{(mu)} ],
    r_{a-mu,k} = [eps^mu].
(a,j)=(4,1): LSZ zeta_2(5) forms (check rho_{1,0}=-1024, rho_{1,3}=73728).  (a,j)=(8,3): target forms.
"""
import sys, math
from fractions import Fraction as F
from math import comb, gcd, log
sys.set_int_max_str_digits(0)

def poch(x, m):
    p = 1
    for l in range(m):
        p *= (x + l)
    return p

def v2int(x):
    if x == 0:
        return 10**9
    return (x & -x).bit_length() - 1

def vp(x, p):
    """p-adic valuation of a Fraction or int"""
    x = F(x)
    if x == 0:
        return 10**9
    a, b = x.numerator, x.denominator
    v = 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v

def harmonic_tables(n, smax):
    """H[s][m] = sum_{r=1}^m r^{-s},  A[s][m] = sum_{r=0}^{m-1} (r+1/2)^{-s}  for m=0..n, s=1..smax"""
    H = {s: [F(0)] * (n + 1) for s in range(1, smax + 1)}
    A = {s: [F(0)] * (n + 1) for s in range(1, smax + 1)}
    for s in range(1, smax + 1):
        h = F(0); aa = F(0)
        for m in range(1, n + 1):
            h += F(1, m ** s)
            aa += F(2 ** s, (2 * m - 1) ** s)
            H[s][m] = h; A[s][m] = aa
    return H, A

def partial_fractions(n, a, H, A):
    """r[i][k], i=1..a, k=0..n  (exact Fractions)"""
    r = {i: [F(0)] * (n + 1) for i in range(1, a + 1)}
    for k in range(n + 1):
        Ck = (comb(2 * k, k) * comb(2 * n - 2 * k, n - k)) ** a
        lam = [F(0)] * a
        for mu in range(1, a):
            sg = 1 if (mu - 1) % 2 == 0 else -1
            lam[mu] = (-A[mu][k] + sg * A[mu][n - k] + H[mu][k] - sg * H[mu][n - k]) / mu
        e = [F(0)] * a
        e[0] = F(1)
        for m in range(1, a):
            s_ = F(0)
            for mu in range(1, m + 1):
                s_ += mu * lam[mu] * e[m - mu]
            e[m] = a * s_ / m
        for mu in range(a):
            g = (n - 2 * k) * e[mu] + (2 * e[mu - 1] if mu >= 1 else 0)
            r[a - mu][k] = Ck * g
    return r

def linear_form(n, a=8, j=3):
    smax = max(a - 1, a + j + 1)
    H, A = harmonic_tables(n, smax)
    r = partial_fractions(n, a, H, A)
    c = {i: sum(r[i]) for i in range(1, a + 1)}
    rho0 = F(0)
    for i in range(1, a + 1):
        w = poch(i, j + 1)
        s = i + j + 1
        acc = F(0)
        for k in range(1, n + 1):
            if r[i][k]:
                acc += r[i][k] * A[s][k]
        rho0 -= w * acc
    Z = {}
    for i in range(1, a + 1):
        if c[i] != 0:
            Z[i + j + 1] = poch(i, j + 1) * 2 ** (i + j + 1) * c[i]
    return rho0, Z, c, r

def to2adic(x, K):
    """Fraction -> (v, u mod 2^K) with x = 2^v * u, u odd unit"""
    x = F(x)
    if x == 0:
        return None
    num, den = x.numerator, x.denominator
    v = v2int(abs(num)) - v2int(den)
    num >>= v2int(abs(num)); den >>= v2int(den)
    MOD = 1 << K
    return v, (num * pow(den, -1, MOD)) % MOD

def eval_2adic(rho0, Z, zeta, Kz):
    """S = rho0 + sum_m Z[m] zeta_2(m); zeta[m] = (Y_m mod 2^Kz, sh_m) with zeta_2(m) = Y_m 2^{-sh_m}.
    Returns v2(S) exactly if determined by the precision, else ('>=', bound)."""
    items = [(F(rho0), None)] + [(F(x), m) for m, x in Z.items()]
    E = 0
    for x, m in items:
        if x == 0:
            continue
        need = -vp(x, 2) + (zeta[m][1] if m is not None else 0)
        E = max(E, need)
    MOD = 1 << Kz
    tot = 0
    for x, m in items:
        if x == 0:
            continue
        sh = zeta[m][1] if m is not None else 0
        y = x * F(2) ** (E - sh)          # 2-integral
        num, den = y.numerator, y.denominator
        assert den % 2 == 1
        t = (num * pow(den, -1, MOD)) % MOD
        if m is not None:
            t = (t * zeta[m][0]) % MOD
        tot = (tot + t) % MOD
    if tot == 0:
        return ('>=', Kz - E)
    return v2int(tot) - E

def dn(n):
    L = 1
    for m in range(2, n + 1):
        L = L * m // gcd(L, m)
    return L

def primes_upto(N):
    s = bytearray([1]) * (N + 1)
    s[0:2] = b'\x00\x00'
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]

def logabs(x):
    x = F(x)
    if x == 0:
        return float('-inf')
    return math.log(abs(x.numerator)) - math.log(x.denominator)
