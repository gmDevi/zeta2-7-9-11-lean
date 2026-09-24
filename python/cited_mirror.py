#!/usr/bin/env python3
"""Exact-arithmetic mirror of Zeta2Lean/Cited: numerical checks of every new statement.

Pure standard library (mpmath optional: used, when importable, for the zeta-function checks of the
PNT track).  Every Lean definition of Zeta2Lean/Cited/Defs.lean and every Stmt_* of
Zeta2Lean/Cited/Statements.lean is transcribed literally, with Lean's semantics:
  * division by zero gives zero (x / 0 = 0), see `ldiv`;
  * natural-number subtraction is truncated, see `nsub`;
  * `a * b / c` parses as `(a * b) / c`, `x / y * z` as `(x / y) * z`.

Sections (each prints the number of checks and failures):
  Stmt_PPS             random rationals and random elements of GF(p), p in {2,3,5,7,11}
  Stmt_UnitPair        generic and degenerate a (a in Z_{<0}, half-integers)
  Stmt_BaileyLemma     random alpha with beta solved from BP; degenerate a with chain pairs;
                       rho, sigma with (1+a-rho)_{n+1} = 0
  Stmt_SumChainsSucc   exhaustive bijection check and random weights
  Stmt_ChainStep       random parameters incl. vanishing denominators (x / 0 = 0)
  Stmt_BPChain         random admissible parameters incl. degenerate a
  Andrews_Stmt         random admissible points, and the assembly identity LHS = N!(1+a)_N Bchain_N
  API lemmas           rpoch_add, rpoch_negN_mul, rpoch_reflect
  PNT track            instance f = Lambda (q = 1) of Stmt_WienerIkehara: Chebyshev bound,
                       psi(x)/x, L-series identity and G = -zeta'/zeta - 1/(s-1) (mpmath),
                       the Mertens instance f = 1 + mu

Usage: python3 python/cited_mirror.py [--quick]
"""
import itertools
import math
import random
import sys
from array import array
from fractions import Fraction as Fr

QUICK = "--quick" in sys.argv
random.seed(20260924)

FAIL = 0
TOTAL = 0


def check(cond, msg):
    global FAIL, TOTAL
    TOTAL += 1
    if not cond:
        FAIL += 1
        if FAIL <= 20:
            print("  FAIL:", msg)


# ----------------------------------------------------------------------------------------------
# Lean semantics


def ldiv(x, y):
    """Lean's division in a field: x / 0 = 0."""
    return x * 0 if y == 0 else x / y


def nsub(a, b):
    """Truncated subtraction on ℕ."""
    return a - b if a >= b else 0


class GF:
    """The prime field GF(p)."""

    __slots__ = ("v", "p")

    def __init__(self, v, p):
        self.p = p
        self.v = v % p

    def _c(self, o):
        return o if isinstance(o, GF) else GF(o, self.p)

    def __add__(self, o):
        o = self._c(o)
        return GF(self.v + o.v, self.p)

    __radd__ = __add__

    def __sub__(self, o):
        o = self._c(o)
        return GF(self.v - o.v, self.p)

    def __rsub__(self, o):
        o = self._c(o)
        return GF(o.v - self.v, self.p)

    def __mul__(self, o):
        o = self._c(o)
        return GF(self.v * o.v, self.p)

    __rmul__ = __mul__

    def __neg__(self):
        return GF(-self.v, self.p)

    def __eq__(self, o):
        return self.v == self._c(o).v

    def __repr__(self):
        return f"{self.v} mod {self.p}"


def one_like(x):
    return GF(1, x.p) if isinstance(x, GF) else Fr(1)


def rpoch(x, k):
    """`rpoch x k = ∏_{j<k} (x + j)` (Defs.lean)."""
    r = one_like(x)
    for j in range(k):
        r = r * (x + j)
    return r


def fact(n):
    return Fr(math.factorial(n))


def rand_q(den=6, num=12):
    return Fr(random.randint(-num, num), random.randint(1, den))


def rand_param():
    """A rational parameter: generic, integer, or half-integer (to hit vanishing Pochhammers)."""
    t = random.random()
    if t < 0.4:
        return rand_q()
    if t < 0.7:
        return Fr(random.randint(-6, 6))
    return Fr(2 * random.randint(-6, 6) + 1, 2)


# ----------------------------------------------------------------------------------------------
# Cited/Defs.lean


def BP(a, alpha, beta, n):
    """`BP a α β n`, returned as the pair (lhs, rhs)."""
    lhs = rpoch(1 + a, 2 * n) * beta(n)
    rhs = sum((ldiv(alpha(r) * rpoch(1 + a + n + r, n - r), fact(n - r))
               for r in range(n + 1)), Fr(0))
    return lhs, rhs


def unit_alpha(a):
    return lambda r: ldiv(ldiv(a + 2 * r, a) * rpoch(a, r) * (-1) ** r, fact(r))


def unit_beta(n):
    return Fr(1) if n == 0 else Fr(0)


def bw(a, rho, sig, n, j):
    return ldiv(rpoch(rho, j) * rpoch(sig, j) * rpoch(1 + a - rho - sig, nsub(n, j)),
                rpoch(1 + a - rho, n) * rpoch(1 + a - sig, n) * fact(nsub(n, j)))


def b_alpha(a, rho, sig, alpha):
    return lambda r: ldiv(rpoch(rho, r) * rpoch(sig, r),
                          rpoch(1 + a - rho, r) * rpoch(1 + a - sig, r)) * alpha(r)


def b_beta(a, rho, sig, beta):
    return lambda n: sum((bw(a, rho, sig, n, j) * beta(j) for j in range(n + 1)), Fr(0))


def chains(m, N):
    """`chains m N`: monotone `Fin m → ℕ` with values ≤ N (as sorted tuples)."""
    return list(itertools.combinations_with_replacement(range(N + 1), m))


def chain_prev(i, k):
    return 0 if k == 0 else i[k - 1]


def chain_last(i):
    return 0 if len(i) == 0 else i[-1]


def chain_factor(a, b, c, i, k):
    d = nsub(i[k], chain_prev(i, k))
    return ldiv(rpoch(1 + a - b[k] - c[k], d) * rpoch(b[k + 1], i[k]) * rpoch(c[k + 1], i[k]),
                fact(d) * rpoch(1 + a - b[k], i[k]) * rpoch(1 + a - c[k], i[k]))


def Bchain(a, b, c):
    m = len(b) - 1
    bl, cl = b[m], c[m]

    def f(n):
        tot = Fr(0)
        for i in chains(m, n):
            w = Fr(1)
            for k in range(m):
                w *= chain_factor(a, b, c, i, k)
            e = nsub(n, chain_last(i))
            tot += w * ldiv(rpoch(1 + a - bl - cl, e),
                            rpoch(1 + a - bl, n) * rpoch(1 + a - cl, n) * fact(e))
        return tot
    return f


def Achain(a, b, c):
    def f(r):
        p = Fr(1)
        for k in range(len(b)):
            p *= ldiv(rpoch(b[k], r) * rpoch(c[k], r),
                      rpoch(1 + a - b[k], r) * rpoch(1 + a - c[k], r))
        return p * unit_alpha(a)(r)
    return f


# ----------------------------------------------------------------------------------------------
# Stmt_PPS


def pps_sides(x, y, z, M):
    lhs = None
    for s in range(M + 1):
        cs = math.comb(M, s)
        term = (GF(cs, x.p) if isinstance(x, GF) else Fr(cs)) * rpoch(x, s) * rpoch(y, s) \
            * rpoch(z - x - y, M - s) * rpoch(z + s, 2 * M - s)
        lhs = term if lhs is None else lhs + term
    rhs = rpoch(z - x, M) * rpoch(z - y, M) * rpoch(z + M, M)
    return lhs, rhs


def test_pps():
    n0 = TOTAL
    f0 = FAIL
    for _ in range(150 if QUICK else 400):
        x, y, z = rand_param(), rand_param(), rand_param()
        M = random.randint(0, 8)
        l, r = pps_sides(x, y, z, M)
        check(l == r, f"PPS over Q x={x} y={y} z={z} M={M}")
    for p in (2, 3, 5, 7, 11):
        for _ in range(60 if QUICK else 150):
            x, y, z = (GF(random.randrange(p), p) for _ in range(3))
            M = random.randint(0, 9)
            l, r = pps_sides(x, y, z, M)
            check(l == r, f"PPS over GF({p}) x={x} y={y} z={z} M={M}")
    print(f"Stmt_PPS: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# Stmt_UnitPair


def test_unit_pair():
    n0, f0 = TOTAL, FAIL
    degenerate = [Fr(-1), Fr(-2), Fr(-3), Fr(-1, 2), Fr(-3, 2), Fr(-5, 2), Fr(1), Fr(2)]
    avals = degenerate + [rand_q() for _ in range(25)]
    for a in avals:
        if a == 0:
            continue
        for n in range(11 if not QUICK else 8):
            l, r = BP(a, unit_alpha(a), unit_beta, n)
            check(l == r, f"UnitPair a={a} n={n}")
    print(f"Stmt_UnitPair: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# Stmt_BaileyLemma


def bailey_conclusion(a, rho, sig, alpha, beta, n):
    l, r = BP(a, b_alpha(a, rho, sig, alpha), b_beta(a, rho, sig, beta), n)
    return l == r


def test_bailey():
    n0, f0 = TOTAL, FAIL
    # (i) generic a, random alpha, beta solved from BP
    for _ in range(40 if QUICK else 120):
        a, rho, sig = rand_q(), rand_param(), rand_param()
        nmax = random.randint(0, 6)
        if any(rpoch(1 + a, 2 * j) == 0 for j in range(nmax + 1)):
            continue
        avals = [rand_q() for _ in range(nmax + 1)]
        alpha = lambda r, avals=avals: avals[r]
        bvals = []
        for j in range(nmax + 1):
            _, rhs = BP(a, alpha, lambda _: Fr(0), j)
            bvals.append(rhs / rpoch(1 + a, 2 * j))
        beta = lambda j, bvals=bvals: bvals[j]
        for n in range(nmax + 1):
            assert all(BP(a, alpha, beta, j)[0] == BP(a, alpha, beta, j)[1] for j in range(n + 1))
            if rpoch(1 + a - rho, n) == 0 or rpoch(1 + a - sig, n) == 0:
                continue
            check(bailey_conclusion(a, rho, sig, alpha, beta, n),
                  f"Bailey generic a={a} rho={rho} sig={sig} n={n}")
    # (ii) degenerate a: (alpha, beta) = chain pair (satisfies BP up to N), one more step
    for _ in range(40 if QUICK else 120):
        a = random.choice([Fr(-1), Fr(-2), Fr(-3), Fr(-1, 2), Fr(-3, 2), rand_q()])
        if a == 0:
            continue
        N = random.randint(0, 4)
        m = random.randint(0, 2)
        b = [rand_param() for _ in range(m + 1)]
        c = [rand_param() for _ in range(m + 1)]
        if any(rpoch(1 + a - v, N) == 0 for v in b + c):
            continue
        alpha, beta = Achain(a, b, c), Bchain(a, b, c)
        rho, sig = rand_param(), rand_param()
        for n in range(N + 1):
            if rpoch(1 + a - rho, n) == 0 or rpoch(1 + a - sig, n) == 0:
                continue
            if not all(BP(a, alpha, beta, j)[0] == BP(a, alpha, beta, j)[1]
                       for j in range(n + 1)):
                check(False, f"chain pair not BP (hypothesis) a={a} b={b} c={c} n={n}")
                continue
            check(bailey_conclusion(a, rho, sig, alpha, beta, n),
                  f"Bailey degenerate a={a} rho={rho} sig={sig} n={n}")
    # (iii) (1+a-rho)_n != 0 but (1+a-rho)_{n+1} = 0: rho = 1+a+n
    for _ in range(20 if QUICK else 60):
        a = random.choice([Fr(-1), Fr(-3, 2), rand_q()])
        if a == 0:
            continue
        n = random.randint(0, 5)
        rho, sig = 1 + a + n, rand_param()
        if rpoch(1 + a - sig, n) == 0:
            continue
        check(bailey_conclusion(a, rho, sig, unit_alpha(a), unit_beta, n),
              f"Bailey edge a={a} rho={rho} sig={sig} n={n}")
    print(f"Stmt_BaileyLemma: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# Stmt_SumChainsSucc


def test_sum_chains():
    n0, f0 = TOTAL, FAIL
    for m in range(5):
        for n in range(6):
            big = chains(m + 1, n)
            pairs = [(j, ip) for j in range(n + 1) for ip in chains(m, j)]
            snoc = [ip + (j,) for (j, ip) in pairs]
            check(sorted(snoc) == sorted(big) and len(set(snoc)) == len(snoc),
                  f"SumChainsSucc bijection m={m} n={n}")
            w = {i: random.randint(-10 ** 6, 10 ** 6) for i in big}
            check(sum(w[i] for i in big) == sum(w[ip + (j,)] for (j, ip) in pairs),
                  f"SumChainsSucc weights m={m} n={n}")
    print(f"Stmt_SumChainsSucc: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# Stmt_ChainStep


def test_chain_step():
    n0, f0 = TOTAL, FAIL
    for _ in range(40 if QUICK else 120):
        a = random.choice([Fr(0), Fr(-1), Fr(-2), rand_q(), rand_param()])
        m = random.randint(0, 3)
        # parameters chosen so that some denominators (1+a-b_k)_r vanish (1+a-b_k ∈ {0,-1,-2,-3})
        b = [random.choice([rand_param(), 1 + a + random.randint(0, 3)]) for _ in range(m + 2)]
        c = [random.choice([rand_param(), 1 + a + random.randint(0, 3)]) for _ in range(m + 2)]
        # zero fields (one pair)
        b1, c1 = b[:1], c[:1]
        for r in range(6):
            check(Achain(a, b1, c1)(r) == b_alpha(a, b1[0], c1[0], unit_alpha(a))(r),
                  f"achain_zero a={a} b={b1} c={c1} r={r}")
        for n in range(5):
            check(Bchain(a, b1, c1)(n) == b_beta(a, b1[0], c1[0], unit_beta)(n),
                  f"bchain_zero a={a} b={b1} c={c1} n={n}")
        # succ fields (m + 2 pairs)
        L = m + 1
        for r in range(6):
            check(Achain(a, b, c)(r) ==
                  b_alpha(a, b[L], c[L], Achain(a, b[:-1], c[:-1]))(r),
                  f"achain_succ a={a} b={b} c={c} r={r}")
        for n in range(4 if QUICK else 5):
            check(Bchain(a, b, c)(n) ==
                  b_beta(a, b[L], c[L], Bchain(a, b[:-1], c[:-1]))(n),
                  f"bchain_succ a={a} b={b} c={c} n={n}")
    print(f"Stmt_ChainStep: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# Stmt_BPChain and Andrews_Stmt


def andrews_sides(a, b, c, N):
    m = len(b) - 1
    lhs = Fr(0)
    for kap in range(N + 1):
        p = Fr(1)
        for k in range(m + 1):
            p *= ldiv(rpoch(b[k], kap) * rpoch(c[k], kap),
                      rpoch(1 + a - b[k], kap) * rpoch(1 + a - c[k], kap))
        lhs += ldiv(a + 2 * kap, a) * ldiv(rpoch(a, kap), fact(kap)) * p \
            * ldiv(rpoch(Fr(-N), kap), rpoch(1 + a + N, kap))
    bl, cl = b[m], c[m]
    s = Fr(0)
    for i in chains(m, N):
        t = ldiv(rpoch(Fr(-N), chain_last(i)), rpoch(bl + cl - a - N, chain_last(i)))
        for k in range(m):
            d = nsub(i[k], chain_prev(i, k))
            t *= ldiv(rpoch(1 + a - b[k] - c[k], d) * rpoch(b[k + 1], i[k])
                      * rpoch(c[k + 1], i[k]),
                      fact(d) * rpoch(1 + a - b[k], i[k]) * rpoch(1 + a - c[k], i[k]))
        s += t
    rhs = ldiv(rpoch(1 + a, N) * rpoch(1 + a - bl - cl, N),
               rpoch(1 + a - bl, N) * rpoch(1 + a - cl, N)) * s
    return lhs, rhs


def test_bpchain_andrews():
    n0, f0 = TOTAL, FAIL
    nbp = nand = ndeg = 0
    for _ in range(80 if QUICK else 250):
        a = random.choice([Fr(-1), Fr(-2), Fr(-1, 2), Fr(-3, 2), rand_q(), rand_param()])
        if a == 0:
            continue
        N = random.randint(0, 4)
        m = random.randint(0, 3 if not QUICK else 2)
        b = [rand_param() for _ in range(m + 1)]
        c = [rand_param() for _ in range(m + 1)]
        if random.random() < 0.3:
            b[m] = Fr(1)
            c[m] = 1 + a + N  # the specialisation used by AndrewsApplied
        if any(rpoch(1 + a - v, N) == 0 for v in b + c):
            continue
        al, be = Achain(a, b, c), Bchain(a, b, c)
        for n in range(N + 1):
            l, r = BP(a, al, be, n)
            check(l == r, f"BPChain a={a} b={b} c={c} N={N} n={n}")
            nbp += 1
        if rpoch(1 + a + N, N) == 0 or rpoch(b[m] + c[m] - a - N, N) == 0:
            continue
        l, r = andrews_sides(a, b, c, N)
        check(l == r, f"Andrews a={a} b={b} c={c} N={N}")
        mid = fact(N) * rpoch(1 + a, N) * be(N)
        check(l == mid, f"Andrews assembly LHS = N!(1+a)_N Bchain_N a={a} b={b} c={c} N={N}")
        nand += 1
        if rpoch(1 + a, 2 * N) == 0:
            ndeg += 1
    print(f"Stmt_BPChain / Andrews_Stmt: {TOTAL - n0} checks ({nbp} BP levels, {nand} Andrews "
          f"points, {ndeg} with (1+a)_(2N) = 0), {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# API lemmas of Cited/Defs.lean (proved in Lean; mirrored for completeness)


def test_api():
    n0, f0 = TOTAL, FAIL
    for _ in range(200):
        x = rand_param()
        A, B = random.randint(0, 6), random.randint(0, 6)
        check(rpoch(x, A + B) == rpoch(x, A) * rpoch(x + A, B), f"rpoch_add x={x} {A} {B}")
        N = random.randint(0, 8)
        k = random.randint(0, N)
        check(rpoch(Fr(-N), k) * fact(N - k) == (-1) ** k * fact(N), f"rpoch_negN_mul {N} {k}")
        check(rpoch(x, N - k) * rpoch(1 - x - N, k) == (-1) ** k * rpoch(x, N),
              f"rpoch_reflect x={x} {N} {k}")
    print(f"API lemmas: {TOTAL - n0} checks, {FAIL - f0} failures")


# ----------------------------------------------------------------------------------------------
# PNT track: the instance f = Λ (q = 1) of Stmt_WienerIkehara used by pnt_of_stmts


def von_mangoldt_table(X):
    sieve = bytearray([1]) * (X + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, math.isqrt(X) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(range(p * p, X + 1, p)))
    lam = array("d", bytes(8 * (X + 1)))
    for p in range(2, X + 1):
        if sieve[p]:
            lp = math.log(p)
            q = p
            while q <= X:
                lam[q] = lp
                q *= p
    return lam


def moebius_table(X):
    mu = [1] * (X + 1)
    mu[0] = 0
    is_comp = bytearray(X + 1)
    for p in range(2, X + 1):
        if not is_comp[p]:
            for k in range(p, X + 1, p):
                if k > p:
                    is_comp[k] = 1
                mu[k] = -mu[k]
            pp = p * p
            for k in range(pp, X + 1, pp):
                mu[k] = 0
    return mu


def test_pnt():
    n0, f0 = TOTAL, FAIL
    X = 10 ** 6 if QUICK else 2 * 10 ** 6
    lam = von_mangoldt_table(X)
    # hypothesis `bound` with C = log 4 + 4: ∑_{i<N} |Λ i| ≤ (log 4 + 4) N for all N ≤ X
    C = math.log(4) + 4
    s = 0.0
    worst = 0.0
    ok = True
    for N in range(X + 1):
        if N > 0 and s > C * N * (1 + 1e-12):
            ok = False
        if N > 0:
            worst = max(worst, s / N)
        s += lam[N]
    check(ok, "Chebyshev bound ∑_{i<N} Λ i ≤ (log 4 + 4) N")
    print(f"  bound: max_N ψ(N-1)/N = {worst:.6f} ≤ log 4 + 4 = {C:.6f} (N ≤ {X})")
    # conclusion (= PNT): (∑_{n ∈ Icc 0 ⌊x⌋} Λ n) / x → 1
    cum = 0.0
    marks = {10 ** k for k in range(1, 7)} | {X}
    for n in range(X + 1):
        cum += lam[n]
        if n in marks:
            print(f"  ψ({n})/{n} = {cum / n:.6f}")
            if n >= 10 ** 5:
                check(abs(cum / n - 1) < 5e-3, f"ψ(x)/x near 1 at x={n}")
    # L-series identity at s = 2: ∑ Λ(n) n^{-2} = -ζ'(2)/ζ(2) = 12 log A - γ - log 2π (Glaisher A)
    ls2 = sum(lam[n] / (n * n) for n in range(2, X + 1)) + 1.0 / X   # tail ≈ ∫_X^∞ dt/t²
    target2 = 0.5699609930945318
    check(abs(ls2 - target2) < 1e-5, f"LSeries Λ (2) = {ls2} vs {target2}")
    print(f"  LSeries Λ 2 = {ls2:.9f}, -ζ'(2)/ζ(2) = {target2:.9f}")
    try:
        import mpmath
        mpmath.mp.dps = 30
        for sv in (2, 3, 4):
            z = -mpmath.zeta(sv, derivative=1) / mpmath.zeta(sv)
            ls = sum(lam[n] / n ** sv for n in range(2, X + 1)) + (X ** (1 - sv)) / (sv - 1)
            check(abs(float(z) - ls) < 1e-5, f"LSeries Λ ({sv})")
            print(f"  s = {sv}: LSeries Λ = {ls:.9f}, -ζ'/ζ = {float(z):.9f}")
        # G(s) = -ζ'/ζ(s) - 1/(s-1) = LFunctionResidueClassAux (0 : ZMod 1): finite on re s = 1
        G = lambda s: -mpmath.zeta(s, derivative=1) / mpmath.zeta(s) - 1 / (s - 1)
        g1 = G(mpmath.mpf(1) + mpmath.mpf("1e-12"))
        check(abs(g1 + mpmath.euler) < 1e-9, "G(1+) = -γ")
        print(f"  G(1 + 1e-12) = {mpmath.nstr(g1, 12)} (-γ = {mpmath.nstr(-mpmath.euler, 12)})")
        for t in (1, 5, 14.134725, 30):
            v = G(mpmath.mpc(1, t))
            check(mpmath.isfinite(v.real) and mpmath.isfinite(v.imag), f"G(1+{t}i) finite")
        print("  G(1+it) finite at t = 1, 5, 14.134725, 30")
    except ImportError:
        print("  (mpmath not available: zeta checks at s = 3, 4 and on re s = 1 skipped)")
    # Mertens instance f = 1 + μ ≥ 0, A = 1 (mathlib4 PR #43238): (∑_{n ≤ x} (1 + μ n)) / x → 1
    Y = 10 ** 6 if not QUICK else 2 * 10 ** 5
    mu = moebius_table(Y)
    Msum = sum(mu[1:])
    val = (sum(1 + mu[n] for n in range(Y + 1))) / Y
    check(all(1 + v >= 0 for v in mu), "1 + μ ≥ 0")
    check(abs(val - 1) < 1e-2, "Mertens instance near 1")
    print(f"  Mertens: M({Y}) = {Msum}, (∑_(n ≤ x) (1 + μ n)) / x = {val:.6f}")
    print(f"PNT track: {TOTAL - n0} checks, {FAIL - f0} failures")


if __name__ == "__main__":
    test_api()
    test_pps()
    test_unit_pair()
    test_bailey()
    test_sum_chains()
    test_chain_step()
    test_bpchain_andrews()
    test_pnt()
    print(f"TOTAL: {TOTAL} checks, {FAIL} failures")
    sys.exit(1 if FAIL else 0)
