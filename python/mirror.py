#!/usr/bin/env python3
"""Exact-arithmetic mirror of Zeta2Lean/Defs.lean and numerical checks of every Stmt in
Zeta2Lean/Statements.lean (for auditors).  Pure standard library (fractions), Python >= 3.8.

Every Python function below mirrors the Lean definition of the same name *literally*
(natural-number subtraction is truncated as in Lean, `rcoef` is 0 outside 1<=i<=8, k<=n, etc.).
Power series are truncated at order ORD (enough for every coefficient the Lean statements use).

Usage:  python3 python/mirror.py [--quick]
The 2-adic values J_s = int_{Z_2} (t+1/2)^{-s} dt are taken from zeta2_K17000.json (17000 bits;
produced by scratchpad zeta2.py via the distribution relation + Bernoulli expansion) and are
cross-checked here against Riemann sums of the Lean definition `halfPow`.
"""
import sys, os, json, math, random, itertools, time
from fractions import Fraction as F
from math import comb, factorial

sys.setrecursionlimit(10000)
if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
QUICK = "--quick" in sys.argv
ORD = 9          # power series truncated mod eps^ORD
FAILS = []


def check(name, cond, info=""):
    if not cond:
        FAILS.append((name, info))
        print("  FAIL:", name, info, flush=True)
    return cond


# ----------------------------------------------------------------------------------------------
# valuations
def v2int(x):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    return (x & -x).bit_length() - 1


def vp(x, p):
    x = F(x)
    if x == 0:
        return 10 ** 9
    a, b, v = x.numerator, x.denominator, 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v


def is_int(x):
    return F(x).denominator == 1


def primes_upto(N):
    s = bytearray([1]) * (N + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def natlog2(k):          # Nat.log 2 k  (Nat.log 2 0 = 0)
    return k.bit_length() - 1 if k > 0 else 0


def nsub(a, b):          # natural-number subtraction
    return a - b if a >= b else 0


# ----------------------------------------------------------------------------------------------
# truncated power series over Q
def ps(c0=0, c1=0):
    z = [F(0)] * ORD
    z[0] = F(c0)
    if ORD > 1:
        z[1] = F(c1)
    return z


def ps_const(c):
    return ps(c, 0)


def ps_add(a, b):
    return [x + y for x, y in zip(a, b)]


def ps_neg(a):
    return [-x for x in a]


def ps_scale(c, a):
    c = F(c)
    return [c * x for x in a]


def ps_mul(a, b):
    z = [F(0)] * ORD
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j in range(ORD - i):
            if b[j]:
                z[i + j] += x * b[j]
    return z


def ps_inv(a):
    assert a[0] != 0, "inverse of series with zero constant term"
    z = [F(0)] * ORD
    z[0] = 1 / a[0]
    for m in range(1, ORD):
        s = F(0)
        for i in range(1, m + 1):
            s += a[i] * z[m - i]
        z[m] = -s / a[0]
    return z


def ps_pow(a, k):
    z = ps_const(1)
    b = a
    while k:
        if k & 1:
            z = ps_mul(z, b)
        b = ps_mul(b, b)
        k >>= 1
    return z


def ps_prod(lst):
    z = ps_const(1)
    for a in lst:
        z = ps_mul(z, a)
    return z


def ps_rescale_neg(a):   # eps -> -eps
    return [x if i % 2 == 0 else -x for i, x in enumerate(a)]


# ----------------------------------------------------------------------------------------------
# Defs.lean mirror
def rpoch(x, k):
    p = F(1)
    for j in range(k):
        p *= (x + j)
    return p


_pp = {}


def psPoch(c, d, k):
    key = (F(c), F(d), k)
    if key not in _pp:
        z = ps_const(1)
        for j in range(k):
            z = ps_mul(z, ps(F(c) + j, d))
        _pp[key] = z
    return _pp[key]


def Psi(n, k):
    return ps_mul(ps_mul(psPoch(F(1, 2), -1, k), psPoch(F(1, 2), 1, nsub(n, k))),
                  ps_inv(ps_mul(psPoch(1, -1, k), psPoch(1, 1, nsub(n, k)))))


_G = {}


def Gser(n, k):
    if (n, k) not in _G:
        _G[(n, k)] = ps_scale(F(2) ** (16 * n), ps_mul(ps(n - 2 * k, 2), ps_pow(Psi(n, k), 8)))
    return _G[(n, k)]


def rcoef(n, i, k):
    if 1 <= i <= 8 and k <= n:
        return Gser(n, k)[8 - i]
    return F(0)


def csum(n, i):
    return sum((rcoef(n, i, k) for k in range(n + 1)), F(0))


_A = {}


def Ahalf(k, s):
    if (k, s) not in _A:
        _A[(k, s)] = sum((F(2 * l + 1, 2) ** (-s) for l in range(k)), F(0))
    return _A[(k, s)]


def rho0(n):
    return -sum((F(i * (i + 1) * (i + 2) * (i + 3)) * rcoef(n, i, k) * Ahalf(k, i + 4)
                 for i in range(1, 9) for k in range(n + 1)), F(0))


def Z7(n): return 46080 * csum(n, 3)
def Z9(n): return 860160 * csum(n, 5)
def Z11(n): return 10321920 * csum(n, 7)


def integrand(n, x):
    return sum((F(i * (i + 1) * (i + 2)) * rcoef(n, i, k) * F(2 * (x + k) + 1, 2) ** (-(i + 3))
                for i in range(1, 9) for k in range(n + 1)), F(0))


# polynomials: list of Fractions, index = degree
def pl_mul(a, b):
    z = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                z[i + j] += x * y
    return z


def pl_add(a, b):
    L = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(L)]


def pl_pow(a, k):
    z = [F(1)]
    for _ in range(k):
        z = pl_mul(z, a)
    return z


def pl_trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


def Rnum(n):
    p = [F(1)]
    for j in range(n):
        p = pl_mul(p, [F(2 * j + 1, 2), F(1)])
    return pl_mul([F(2) ** (16 * n)], pl_mul([F(n), F(2)], pl_pow(p, 8)))


def PFpoly(n):
    tot = [F(0)]
    for i in range(1, 9):
        for k in range(n + 1):
            t = pl_mul([rcoef(n, i, k)], pl_pow([F(k), F(1)], nsub(8, i)))
            for j in range(n + 1):
                if j != k:
                    t = pl_mul(t, pl_pow([F(j), F(1)], 8))
            tot = pl_add(tot, t)
    return tot


def Rser(n, y):
    y = F(y)
    num = ps_prod([ps(y + F(1, 2) + j, 1) for j in range(n)])
    den = ps_prod([ps(y + j, 1) for j in range(n + 1)])
    return ps_scale(F(2) ** (16 * n), ps_mul(ps(2 * y + n, 2), ps_mul(ps_pow(num, 8), ps_inv(ps_pow(den, 8)))))


def dn(n):
    L = 1
    for m in range(1, n + 1):
        L = L * m // math.gcd(L, m)
    return L


def Phi(n):
    p = 1
    for q in range(n + 1):
        if is_prime(q) and 11 <= q and 2 * n < q * q:
            p *= q
    return p


def Dn(n):
    return dn(n) ** 12 // Phi(n)


def Tser(n, l):
    pre = ps_scale(F(2) ** (16 * n), ps_mul(ps_pow(ps(F(l) - F(1, 2), -1), 3), ps_pow(psPoch(F(1, 2), -1, nsub(l, 1)), 8)))
    s = ps_const(0)
    for k in range(l, n + 1):
        t = ps_mul(ps(n - 2 * k, 2), ps_pow(psPoch(F(l) + F(1, 2), -1, nsub(k, l)), 8))
        t = ps_mul(t, ps_pow(psPoch(F(1, 2), 1, nsub(n, k)), 8))
        t = ps_mul(t, ps_inv(ps_mul(ps_pow(psPoch(1, -1, k), 8), ps_pow(psPoch(1, 1, nsub(n, k)), 8))))
        s = ps_add(s, t)
    return ps_mul(pre, s)


def chains(m, N):
    return [tuple(c) for c in itertools.combinations_with_replacement(range(N + 1), m)]


def chainPrev(ch, k):
    return 0 if k == 0 else ch[k - 1]


def chainLast(ch):
    return 0 if len(ch) == 0 else ch[-1]


def Pser(n, l):
    t = ps_scale(F(2) ** (16 * n), ps_mul(ps_pow(ps(F(l) - F(1, 2), -1), 3), ps_pow(psPoch(F(1, 2), -1, nsub(l, 1)), 8)))
    t = ps_mul(t, ps_pow(psPoch(F(1, 2), 1, nsub(n, l)), 8))
    return ps_mul(t, ps_inv(ps_mul(ps_pow(psPoch(1, -1, l), 8), ps_pow(psPoch(1, 1, nsub(n, l)), 8))))


def Fser(n, l, ch):
    N = nsub(n, l)
    z = ps_mul(ps_const(-F(N) - 1), ps(F(l), -2))
    z = ps_mul(z, Pser(n, l))
    for i in range(8):
        d = nsub(ch[i], chainPrev(ch, i))
        z = ps_scale(rpoch(F(1, 2), d) / factorial(d), z)
    for i in range(7):
        Ji = ch[i]
        z = ps_mul(z, ps_mul(psPoch(-F(N), -1, Ji), psPoch(F(l) + F(1, 2), -1, Ji)))
        z = ps_mul(z, ps_inv(ps_mul(psPoch(F(l) + 1, -1, Ji), psPoch(F(1, 2) - N, -1, Ji))))
    J8 = ch[7]
    z = ps_mul(z, ps_scale(rpoch(-F(N), J8), psPoch(F(l) + 1, -2, J8)))
    z = ps_mul(z, ps_inv(ps_mul(ps_const(F(J8) + 1), ps_mul(psPoch(F(l) + 1, -1, J8), psPoch(F(1, 2) - N, -1, J8)))))
    return z


def FJ0(n, l, ch):
    N = nsub(n, l)
    v = F(-64) / (2 * F(l) - 1) ** 4 * comb(nsub(2 * l, 2), nsub(l, 1)) * (F(N) + 1) / (F(ch[7]) + 1)
    for i in range(8):
        d = nsub(ch[i], chainPrev(ch, i))
        v *= comb(2 * d, d)
    for i in range(7):
        v *= comb(2 * (l + ch[i]), l + ch[i])
    for i in range(8):
        e = nsub(N, ch[i])
        v *= comb(2 * e, e)
    return v


def archBound(C, A, n):
    return C * (n + 1) ** A * 2.0 ** (16 * n)


def Bn(n, x): return comb(x + n, n)
def Yl(n, l, x): return comb(nsub(x + l, 1), nsub(l, 1)) * comb(x + n, nsub(n, l))
def Wl(n, l): return factorial(nsub(l, 1)) * factorial(nsub(n, l))


_H = {}


def hseries(n, x):
    if (n, x) not in _H:
        z = ps_const(1)
        for k in range(n + 1):
            z = ps_mul(z, ps_inv(ps_pow(ps(2 * x + 2 * k + 1, 1), 8)))
        _H[(n, x)] = z
    return _H[(n, x)]


def hcoef(n, beta, x):
    return hseries(n, x)[beta]


def leibTerm(n, g, beta, M, x):
    """M: dict l -> multiplicity (support in [1, n])"""
    v = F(-6) * F(2) ** (24 * n + 8) * (F(2 * x + 1 + n) if g == 0 else F(2)) * F(2) ** beta * hcoef(n, beta, x)
    for l in range(1, n + 1):
        v *= comb(8, M.get(l, 0))
    e = 5 + g + beta
    v *= F(factorial(n)) ** e * F(Bn(n, x)) ** e
    for l in range(1, n + 1):
        if M.get(l, 0):
            v *= (F(Wl(n, l)) * Yl(n, l, x)) ** M[l]
    return v


def domTerm(m, x):
    n = 2 ** m - 1
    k0 = 2 ** (m - 1)
    return (F(-336) * F(2) ** (24 * n + 8) * F(factorial(n)) ** 6 * F(Wl(n, k0)) ** 2 * F(Bn(n, x)) ** 6
            * F(Yl(n, k0, x)) ** 2 * hcoef(n, 0, x))


def target(m):
    return 32 * (2 ** m - 1) + 14 - 11 * m


def finsupp_antidiag(n, a):
    """all M : {1..n} -> N with sum a (as dicts)"""
    out = []
    for combo in itertools.combinations_with_replacement(range(1, n + 1), a):
        M = {}
        for l in combo:
            M[l] = M.get(l, 0) + 1
        out.append(M)
    return out


# ----------------------------------------------------------------------------------------------
# 2-adic helpers:  elements of Q_2 represented exactly (Fractions) or mod 2^K via (v, unit mod 2^K)
def load_J(K=17000):
    """J_s mod 2^K for s = 2..12 even, from the zeta_2 cache: zeta_2(m) = Z 2^{-sh}, J_{m-1} = (m-1) 2^m zeta_2(m)."""
    fn = os.path.join(HERE, "zeta2_K17000.json")
    d = json.load(open(fn))
    J = {}
    for k, v in d.items():
        m = int(k); Z = int(v[0]); sh = int(v[1])
        s = m - 1
        # J_s = s 2^m Z 2^{-sh} = so * 2^{e + m - sh} * Z  with s = 2^e so
        e = v2int(s); so = s >> e
        shift = e + m - sh
        assert shift == 0, (m, shift)
        J[s] = (Z * so) % (1 << K)      # J_s is a 2-adic integer (known mod 2^K)
    return J


def eval_mod(x, K):
    """Fraction with odd-denominator-after-shift -> (v, unit residue mod 2^K)"""
    x = F(x)
    if x == 0:
        return None
    v = vp(x, 2)
    num, den = x.numerator, x.denominator
    if v >= 0:
        num >>= v
    else:
        den >>= -v
    return v, (num * pow(den, -1, 1 << K)) % (1 << K)


def v2_linear_form(rho, coefs, J, K):
    """v2 of rho + sum coefs[s] * J_s, J_s known mod 2^K.  Returns exact v2 if determined."""
    E = 0
    for x in [rho] + list(coefs.values()):
        if x != 0:
            E = max(E, -vp(x, 2))
    MOD = 1 << K
    tot = 0
    for x, s in [(rho, None)] + [(c, s) for s, c in coefs.items()]:
        if x == 0:
            continue
        y = F(x) * F(2) ** E
        assert y.denominator % 2 == 1
        t = (y.numerator * pow(y.denominator, -1, MOD)) % MOD
        if s is not None:
            t = (t * J[s]) % MOD
        tot = (tot + t) % MOD
    if tot == 0:
        return None
    return v2int(tot) - E


def riemann_sum_Q(f, N):
    return sum((f(x) for x in range(2 ** N)), F(0)) / 2 ** N


# ----------------------------------------------------------------------------------------------
def section(t):
    print("\n== " + t, flush=True)


def main():
    t0 = time.time()
    random.seed(20260924)
    nmax_small = 12 if QUICK else 30

    # ------------------------------------------------------------------ r_{i,k} vs lf.py
    section("rcoef (Lean Gser definition) vs independent log-derivative formula (lf.py)")
    try:
        sys.path.insert(0, HERE)
        import lf_reference as lf
        for n in range(0, 16):
            H, A = lf.harmonic_tables(n, 12)
            r = lf.partial_fractions(n, 8, H, A)
            ok = all(r[i][k] == rcoef(n, i, k) for i in range(1, 9) for k in range(n + 1))
            check("rcoef==lf.py n=%d" % n, ok)
            rho, Z, c, _ = lf.linear_form(n, 8, 3)
            check("rho0==lf.py n=%d" % n, rho == rho0(n))
            check("Z==lf.py n=%d" % n, Z.get(7, 0) == Z7(n) and Z.get(9, 0) == Z9(n) and Z.get(11, 0) == Z11(n))
        print("  rcoef, rho0, Z7/9/11 agree with lf.py for n = 0..15")
    except ImportError:
        print("  (lf_reference.py not found; skipped)")
    check("n=0: Z11 = 20643840", Z11(0) == 20643840 and rho0(0) == 0 and Z7(0) == 0 and Z9(0) == 0)
    check("n=1 values", rho0(1) == 14155776 and Z7(1) == -849346560 and Z9(1) == 21139292160 and Z11(1) == 52848230400)
    print("  n=0: S_0 = 20643840 zeta2(11); n=1: rho0 = %s, Z = (%s, %s, %s)" % (rho0(1), Z7(1), Z9(1), Z11(1)))

    # ------------------------------------------------------------------ Stmt_PF
    section("Stmt_PF: poly (Rnum = PFpoly) and series (Rser = sum r (y+k+eps)^-i)")
    for n in range(0, 7):
        check("PF.poly n=%d" % n, pl_trim(Rnum(n)) == pl_trim(PFpoly(n)))
    for n in range(0, 6):
        for _ in range(3):
            y = F(random.randint(-40, 40), random.randint(1, 9))
            if any(y + j == 0 for j in range(n + 1)):
                continue
            lhs = Rser(n, y)
            rhs = ps_const(0)
            for i in range(1, 9):
                for k in range(n + 1):
                    rhs = ps_add(rhs, ps_scale(rcoef(n, i, k), ps_inv(ps_pow(ps(y + k, 1), i))))
            check("PF.series n=%d y=%s" % (n, y), lhs == rhs)
    print("  PF.poly verified n <= 6; PF.series verified at random y, n <= 5")

    # ------------------------------------------------------------------ Stmt_CoeffVanish
    section("Stmt_CoeffVanish: symmetry, c1 = 0, c_even = 0")
    for n in range(0, nmax_small + 1):
        for i in range(0, 10):
            for k in range(n + 1):
                check("symm n=%d i=%d k=%d" % (n, i, k), rcoef(n, i, n - k) == (-1) ** (i + 1) * rcoef(n, i, k))
        check("c1 n=%d" % n, csum(n, 1) == 0)
        for i in range(0, 12, 2):
            check("ceven n=%d i=%d" % (n, i), csum(n, i) == 0)
    print("  verified for n <= %d" % nmax_small)

    # ------------------------------------------------------------------ 2-adic J values
    section("J_s: cache (zeta2_K17000.json) vs Riemann sums of halfPow; zeta2 normalisation")
    J = load_J()
    K = 17000
    for s in (6, 8, 10):
        for Nlev in (8, 12):
            R = riemann_sum_Q(lambda x: F(2 * x + 1, 2) ** (-s), Nlev)
            ev = eval_mod(R, K)
            # compare R with J_s: v2(R - J_s)
            diff = (ev[1] * pow(2, ev[0], 1 << K) if ev[0] >= 0 else None)
            if ev[0] >= 0:
                dv = v2int((ev[1] * (1 << ev[0]) - J[s]) % (1 << K))
                print("  s=%d level N=%d: v2(R_N - J_s) = %d  (Stmt_JConv / Lai 2.4: grows ~ N)" % (s, Nlev, dv))
                check("JConv s=%d N=%d" % (s, Nlev), dv >= Nlev - 4)
    # translation: int (t+k+1/2)^{-s} = J_s - s A_k^{(s+1)}
    for s, k in ((6, 3), (8, 5)):
        Nlev = 12
        R = riemann_sum_Q(lambda x: F(2 * (x + k) + 1, 2) ** (-s), Nlev)
        val = -s * Ahalf(k, s + 1)
        # v2(R - (J_s + val))
        E = max(0, -vp(R, 2), -vp(val, 2))
        MOD = 1 << K
        a = eval_mod(R * F(2) ** E, K); b = eval_mod(val * F(2) ** E, K)
        tot = (a[1] * pow(2, a[0], MOD) - b[1] * pow(2, b[0], MOD) - J[s] * pow(2, E, MOD)) % MOD
        dv = v2int(tot) - E
        print("  Translation s=%d k=%d: v2(R_12 - (J_s - s A_k)) = %d" % (s, k, dv))
        check("Translation s=%d k=%d" % (s, k), dv >= 8)

    # ------------------------------------------------------------------ Stmt_L1
    section("Stmt_L1: Riemann sums of integrand -> rho0 + 60 c3 J6 + 210 c5 J8 + 504 c7 J10")
    for n in (0, 1, 2, 3):
        coefs = {6: 60 * csum(n, 3), 8: 210 * csum(n, 5), 10: 504 * csum(n, 7)}
        Nlev = 11 if not QUICK else 9
        R = riemann_sum_Q(lambda x: integrand(n, x), Nlev)
        # v2(R - L)
        coefs2 = dict(coefs)
        dv = v2_linear_form(rho0(n) - R, coefs2, J, K)
        vL = v2_linear_form(rho0(n), coefs, J, K)
        print("  n=%d: v2(S_n) = %s, v2(R_%d - S_n) = %s" % (n, vL, Nlev, dv))
        check("L1 n=%d" % n, dv is None or dv > vL + 2)

    # ------------------------------------------------------------------ Stmt_BlockF, L2a, L2b
    section("Stmt_BlockF, Stmt_L2a, Stmt_L2b (integrality)")
    for n in range(0, (10 if QUICK else 20) + 1):
        d = dn(n)
        for k in range(n + 1):
            blk = ps_scale(F(4) ** n / factorial(n), ps_mul(psPoch(F(1, 2), -1, k), psPoch(F(1, 2), 1, n - k)))
            check("BlockF n=%d k=%d" % (n, k), all(is_int(F(d) ** j * blk[j]) for j in range(ORD)))
            for i in range(1, 9):
                check("L2a n=%d i=%d k=%d" % (n, i, k), is_int(F(d) ** (8 - i) * rcoef(n, i, k)))
        check("L2b n=%d" % n, is_int(F(d) ** 12 * rho0(n)))
    print("  verified for n <= %d" % (10 if QUICK else 20))

    # ------------------------------------------------------------------ L2c chain
    section("Stmt_ResidueForm, Stmt_AndrewsApplied, Stmt_FJClosed, Stmt_FJKummer, Stmt_L2c, Stmt_L2cor")
    for n in range(0, 9):
        rhs = -24 * sum((Tser(n, l)[7] for l in range(1, n + 1)), F(0))
        check("ResidueForm n=%d" % n, rho0(n) == rhs)
    print("  ResidueForm verified n <= 8")
    nA = 4 if QUICK else 5
    for n in range(1, nA + 1):
        for l in range(1, n + 1):
            T = Tser(n, l)
            S = ps_const(0)
            for ch in chains(8, n - l):
                Fj = Fser(n, l, ch)
                check("FJClosed n=%d l=%d ch=%s" % (n, l, ch), Fj[0] == FJ0(n, l, ch))
                S = ps_add(S, Fj)
            check("AndrewsApplied n=%d l=%d" % (n, l), S == T)
    print("  AndrewsApplied (as truncated power series mod eps^%d) and FJClosed verified n <= %d" % (ORD, nA))
    cnt = 0; mn = 99
    for trial in range(3000 if QUICK else 30000):
        n = random.randint(20, 300)
        ps_ = [p for p in primes_upto(n) if p >= 11 and 2 * n < p * p]
        if not ps_:
            continue
        p = random.choice(ps_)
        cands = [l for l in range(1, n + 1) if (2 * l - 1) % p == 0]
        l = random.choice(cands) if (cands and random.random() < 0.9) else random.randint(1, n)
        N = n - l
        ch = sorted(random.randint(0, N) for _ in range(8))
        if random.random() < 0.9:
            c8 = [x for x in range(ch[6], N + 1) if (x + 1) % p == 0]
            if c8:
                ch[7] = random.choice(c8)
        v = vp(FJ0(n, l, tuple(ch)), p)
        mn = min(mn, v); cnt += 1
        check("FJKummer", v >= -4, (n, l, ch, p, v))
    print("  FJKummer: %d random (critical-biased) samples, min v_p = %d (>= -4 required)" % (cnt, mn))
    for n in range(0, (30 if QUICK else 60) + 1):
        r0 = rho0(n)
        for p in primes_upto(max(2 * n, 11)):
            if p >= 11 and 2 * n < p * p:
                check("L2c n=%d p=%d" % (n, p), vp(r0, p) >= -11 if r0 != 0 else True)
        D = Dn(n)
        check("Phi | dn n=%d" % n, dn(n) % Phi(n) == 0)
        for nm, val in (("rho0", r0), ("Z7", Z7(n)), ("Z9", Z9(n)), ("Z11", Z11(n))):
            check("L2cor %s n=%d" % (nm, n), is_int(D * val))
    print("  L2c and L2cor verified n <= %d" % (30 if QUICK else 60))

    # ------------------------------------------------------------------ Andrews_Stmt (cited): random rational parameters
    section("Andrews_Stmt (cited) at random rational parameters, m <= 3, N <= 5")
    ntest = 0
    for m in range(0, 4):
        for N in range(0, 6):
            for trial in range(6):
                rnd = lambda: F(random.randint(-60, 60), random.randint(1, 13))
                a = rnd(); b = [rnd() for _ in range(m + 1)]; c = [rnd() for _ in range(m + 1)]
                if a == 0:
                    continue
                if any(rpoch(1 + a - b[k], N) == 0 or rpoch(1 + a - c[k], N) == 0 for k in range(m + 1)):
                    continue
                if rpoch(1 + a + N, N) == 0 or rpoch(b[m] + c[m] - a - N, N) == 0:
                    continue
                lhs = F(0)
                for kap in range(N + 1):
                    t = (a + 2 * kap) / a * (rpoch(a, kap) / factorial(kap))
                    for k in range(m + 1):
                        t *= rpoch(b[k], kap) * rpoch(c[k], kap) / (rpoch(1 + a - b[k], kap) * rpoch(1 + a - c[k], kap))
                    t *= rpoch(-F(N), kap) / rpoch(1 + a + N, kap)
                    lhs += t
                pre = rpoch(1 + a, N) * rpoch(1 + a - b[m] - c[m], N) / (rpoch(1 + a - b[m], N) * rpoch(1 + a - c[m], N))
                s = F(0)
                for ch in chains(m, N):
                    t = rpoch(-F(N), chainLast(ch)) / rpoch(b[m] + c[m] - a - N, chainLast(ch))
                    for k in range(m):
                        d = ch[k] - chainPrev(ch, k)
                        t *= rpoch(1 + a - b[k] - c[k], d) * rpoch(b[k + 1], ch[k]) * rpoch(c[k + 1], ch[k])
                        t /= factorial(d) * rpoch(1 + a - b[k], ch[k]) * rpoch(1 + a - c[k], ch[k])
                    s += t
                check("Andrews m=%d N=%d" % (m, N), lhs == pre * s, (a, b, c))
                ntest += 1
    print("  Andrews identity holds exactly in %d random rational instances" % ntest)
    # the specialisation used in Stmt_AndrewsApplied, at a random rational eps (n=5, all l)
    for n in (4, 5):
        for l in range(1, n + 1):
            eps = F(random.randint(1, 50), random.randint(51, 97))
            N = n - l
            a = -F(n) + 2 * l - 2 * eps
            b = [-F(N) - eps] * 8 + [F(1)]
            c = [F(l) + F(1, 2) - eps] * 8 + [1 + a + N]
            lhs = sum(((a + 2 * kap) / a * (rpoch(b[0], kap) * rpoch(c[0], kap) / (rpoch(1 + a - b[0], kap) * rpoch(1 + a - c[0], kap))) ** 8
                       for kap in range(N + 1)), F(0))
            full = F(0)
            for kap in range(N + 1):
                t = (a + 2 * kap) / a * (rpoch(a, kap) / factorial(kap))
                for k in range(9):
                    t *= rpoch(b[k], kap) * rpoch(c[k], kap) / (rpoch(1 + a - b[k], kap) * rpoch(1 + a - c[k], kap))
                t *= rpoch(-F(N), kap) / rpoch(1 + a + N, kap)
                full += t
            check("Andrews specialisation LHS n=%d l=%d" % (n, l), lhs == full)

    # ------------------------------------------------------------------ Stmt_L4
    section("Stmt_L4 with proof.md constants C = 3.4e8, A = 2")
    worst = 0.0
    for n in list(range(0, 41 if not QUICK else 21)) + ([60, 100] if not QUICK else []):
        for nm, val in (("rho0", rho0(n)), ("Z7", Z7(n)), ("Z9", Z9(n)), ("Z11", Z11(n))):
            ratio = abs(float(val)) / archBound(3.4e8, 2, n) if val != 0 else 0.0
            worst = max(worst, ratio)
            check("L4 %s n=%d" % (nm, n), ratio <= 1.0)
    print("  max |coef| / (3.4e8 (n+1)^2 2^{16n}) = %.3g" % worst)

    # ------------------------------------------------------------------ Stmt_Asymptotic (numerical illustration)
    section("Stmt_Asymptotic: log[D_n archBound(3.4e8,2,n) 2^{-target}] along n = 2^m - 1 (exact psi/theta)")
    Mmax = 18 if QUICK else 21
    P = primes_upto(2 ** Mmax)
    for m in range(2, Mmax + 1):
        n = 2 ** m - 1
        logd = sum(math.log(p) * natlog_p(p, n) for p in P if p <= n)
        logPhi = sum(math.log(p) for p in P if p <= n and p >= 11 and 2 * n < p * p)
        logD = 12 * logd - logPhi
        val = logD + math.log(3.4e8) + 2 * math.log(n + 1) + 16 * n * math.log(2) - target(m) * math.log(2)
        if m in (2, 5, 8, 11, 14, 17, 18, 19, 20, 21):
            print("  m=%2d n=%8d  log D_n/n = %.5f  log(expr) = %12.2f  per n: %.5f" % (m, n, logD / n, val, val / n))
    print("  asymptotic slope 11 - 16 log 2 = %.5f" % (11 - 16 * math.log(2)))

    # ------------------------------------------------------------------ Delta calculus helpers
    def DeltaGe_ok(m, c, f, kmax):
        for k in range(2 ** m, kmax):
            km = k - 2 ** natlog2(k)
            d = F(f(k)) - F(f(km))
            if d != 0 and vp(d, 2) < c + natlog2(k):
                return False, k
        return True, None

    def DeltaAll_ok(c, f, kmax):
        ok, k = DeltaGe_ok(0, c, f, kmax)
        f0 = F(f(0))
        return ok and (f0 == 0 or vp(f0, 2) >= c - 1), k

    section("Stmt_DeltaFun (finite ranges)")
    for j in range(0, 6):
        for Nb in range(0, 10):
            ok, k = DeltaAll_ok(-natlog2(Nb), lambda x: comb(x + j, Nb), 300)
            check("binom j=%d N=%d" % (j, Nb), ok, k)
            for mm in range(natlog2(Nb) + 1, natlog2(Nb) + 4):
                ok, k = DeltaGe_ok(mm, 1 - natlog2(Nb), lambda x: comb(x + j, Nb) ** 2, 300)
                check("binomSq j=%d N=%d m=%d" % (j, Nb, mm), ok, k)
    for n in range(0, 4):
        for beta in range(0, 4):
            f = lambda x: hcoef(n, beta, x)
            check("hcoefInt n=%d b=%d" % (n, beta), all(vp(f(x), 2) >= 0 for x in range(200) if f(x) != 0))
            ok, k = DeltaAll_ok(0, f, 200)
            check("hcoefDelta n=%d b=%d" % (n, beta), ok, k)
    print("  binom/binomSq (j<=5, N<=9, k<300) and hcoef (n<=3, beta<=3, x<200) verified")

    section("Stmt_Digit")
    for m in range(0, 15):
        n = 2 ** m - 1
        check("Digit.fact m=%d" % m, vp(factorial(n), 2) == nsub(nsub(2 ** m, 1), m))
        if m >= 2:
            k0 = 2 ** (m - 1)
            check("Digit.dom m=%d" % m, vp(factorial(k0 - 1) * factorial(n - k0), 2) == 2 ** m - 2 * m)
            if m <= 12:
                for l in range(1, n + 1):
                    if l != k0:
                        check("Digit.other m=%d l=%d" % (m, l), vp(factorial(l - 1) * factorial(n - l), 2) >= 2 ** m + 1 - 2 * m)
    print("  verified m <= 14 (other: m <= 12)")

    section("Stmt_Leibniz: integrand n x = sum leibTerm")
    for n in range(0, 5 if QUICK else 6):
        for x in range(0, 6):
            tot = F(0)
            for g in range(2):
                for beta in range(4 - g):
                    for M in finsupp_antidiag(n, 3 - g - beta):
                        tot += leibTerm(n, g, beta, M, x)
            check("Leibniz n=%d x=%d" % (n, x), tot == integrand(n, x))
    print("  verified n <= %d, x <= 5" % (4 if QUICK else 5))

    section("Stmt_LeibTermBound, Stmt_L5Dom (finite ranges), domTerm = leibTerm(1,0,{k0,k0})")
    for m in ((2, 3) if QUICK else (2, 3, 4)):
        n = 2 ** m - 1; k0 = 2 ** (m - 1)
        kmax = 2 ** (m + (4 if m < 4 else 2))
        for x in range(0, 6):
            check("domTerm=leibTerm m=%d x=%d" % (m, x), domTerm(m, x) == leibTerm(n, 1, 0, {k0: 2}, x))
        worst = 99
        for g in range(2):
            for beta in range(4 - g):
                Ms = finsupp_antidiag(n, 3 - g - beta)
                if m == 4:
                    Ms = random.sample(Ms, min(len(Ms), 25))
                for M in Ms:
                    c = (32 * (2 ** m - 1) + 13 - 11 * m + beta * m + sum(vp(comb(8, M.get(l, 0)), 2) for l in range(1, n + 1))
                         + sum(M.get(l, 0) for l in range(1, n + 1) if l != k0))
                    ok, k = DeltaAll_ok(c, lambda x: leibTerm(n, g, beta, M, x), kmax)
                    check("LeibTermBound m=%d g=%d b=%d M=%s" % (m, g, beta, M), ok, k)
                    if not (g == 1 and beta == 0 and M == {k0: 2}):
                        worst = min(worst, c - (target(m) + 2))
                        check("nondominant >= target+2 m=%d" % m, c >= target(m) + 2, (g, beta, M))
        print("  m=%d: all term bounds hold on k < %d; min (bound - (target+2)) over non-dominant terms = %d" % (m, kmax, worst))
    for m in ((2, 3, 4) if QUICK else (2, 3, 4, 5)):
        n = 2 ** m - 1
        f = lambda x: domTerm(m, x)
        ok, k = DeltaGe_ok(m, target(m) + 2, f, 2 ** (m + (4 if m <= 3 else 2)))
        check("L5Dom Delta_m m=%d" % m, ok, k)
        Rm = riemann_sum_Q(f, m)
        check("L5Dom level-m Riemann sum m=%d" % m, vp(Rm, 2) == target(m), (vp(Rm, 2), target(m)))
        print("  m=%d: v2(R_m(domTerm)) = %d = target %d" % (m, vp(Rm, 2), target(m)))

    section("Stmt_L5: v2(S_n) = target(m) along n = 2^m - 1 (via J values)")
    for m in ((2, 3, 4, 5) if QUICK else (2, 3, 4, 5, 6, 7)):
        n = 2 ** m - 1
        coefs = {6: 60 * csum(n, 3), 8: 210 * csum(n, 5), 10: 504 * csum(n, 7)}
        v = v2_linear_form(rho0(n), coefs, J, K)
        check("L5 m=%d" % m, v == target(m), (v, target(m)))
        print("  m=%d n=%d: v2(S_n) = %s, target = %d" % (m, n, v, target(m)))

    print("\n%d checks failed; total time %.1fs" % (len(FAILS), time.time() - t0))
    if FAILS:
        for f_ in FAILS[:30]:
            print("   ", f_)
        sys.exit(1)


def natlog_p(p, n):      # Nat.log p n
    e, q = 0, p
    while q <= n:
        e += 1; q *= p
    return e


if __name__ == "__main__":
    main()
