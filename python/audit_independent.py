#!/usr/bin/env python3
"""Independent auditor checks of Zeta2Lean Defs/Statements (written from the Lean text, NOT derived
from python/mirror.py; the partial fractions are recomputed factor by factor from the product form of
R_n, the Leibniz identity is compared with a direct -R_n'''(x+1/2), and L5 is checked at the level of
the Riemann sums R_M, M >= m, without any J-values).  Exact Fractions only, standard library.

usage: python3 python/audit_independent.py SECTION [SECTION ...]   (or 'all', about 6 min)
sections: pf L1 denoms denoms150 residue aa aa10 andrews kummer leibniz deltafun L5 L4
"""
import sys, random, itertools, math, time
from fractions import Fraction as F
from math import comb, factorial

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)

FAILS = []
NCHECK = [0]
def check(name, cond, info=""):
    NCHECK[0] += 1
    if not cond:
        FAILS.append((name, info))
        print("  FAIL:", name, info, flush=True)
    return cond

def nsub(a, b): return a - b if a >= b else 0
def natlog2(k): return k.bit_length() - 1 if k > 0 else 0

def vp(x, p):
    x = F(x)
    if x == 0: return 10 ** 9
    a, b, v = x.numerator, x.denominator, 0
    while a % p == 0: a //= p; v += 1
    while b % p == 0: b //= p; v -= 1
    return v

def is_int(x): return F(x).denominator == 1

def primes_upto(N):
    s = bytearray([1]) * (N + 1); s[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(N + 1) if s[i]]

def lcm_upto(n):
    L = 1
    for m in range(1, n + 1): L = L * m // math.gcd(L, m)
    return L

# ---------------- truncated power series -----------------
ORD = 9
def ser(c0=0, c1=0, o=ORD):
    z = [F(0)] * o; z[0] = F(c0)
    if o > 1: z[1] = F(c1)
    return z
def smul(c, a): c = F(c); return [c * x for x in a]
def add(a, b): return [x + y for x, y in zip(a, b)]
def mul(a, b):
    n = len(a); z = [F(0)] * n
    for i, x in enumerate(a):
        if x:
            for j in range(n - i):
                y = b[j]
                if y: z[i + j] += x * y
    return z
def inv(a):
    n = len(a); assert a[0] != 0
    z = [F(0)] * n; z[0] = 1 / a[0]
    for m in range(1, n):
        s = F(0)
        for i in range(1, m + 1):
            if a[i]: s += a[i] * z[m - i]
        z[m] = -s / a[0]
    return z
def pw(a, k):
    z = ser(1, 0, len(a))
    for _ in range(k): z = mul(z, a)
    return z

# ---------------- literal transcription of Defs.lean -----------------
def rpoch(x, k):
    p = F(1)
    for j in range(k): p *= (x + j)
    return p

_pp = {}
def psPoch(c, d, k, o=ORD):
    key = (F(c), F(d), k, o)
    if key not in _pp:
        z = ser(1, 0, o)
        for j in range(k): z = mul(z, ser(F(c) + j, d, o))
        _pp[key] = z
    return _pp[key]

def Psi(n, k):
    return mul(mul(psPoch(F(1, 2), -1, k), psPoch(F(1, 2), 1, nsub(n, k))),
               inv(mul(psPoch(1, -1, k), psPoch(1, 1, nsub(n, k)))))

_G = {}
def Gser(n, k):
    if (n, k) not in _G:
        _G[(n, k)] = smul(F(2) ** (16 * n), mul(ser(F(n) - 2 * k, 2), pw(Psi(n, k), 8)))
    return _G[(n, k)]

def rcoef(n, i, k):
    return Gser(n, k)[8 - i] if (1 <= i <= 8 and k <= n) else F(0)

def csum(n, i): return sum((rcoef(n, i, k) for k in range(n + 1)), F(0))

def Ahalf(k, s): return sum(((F(l) + F(1, 2)) ** -1) ** s for l in range(k))

def rho0(n):
    return -sum((F(i * (i + 1) * (i + 2) * (i + 3)) * rcoef(n, i, k) * Ahalf(k, i + 4)
                 for i in range(1, 9) for k in range(n + 1)), F(0))

def Z7(n): return 46080 * csum(n, 3)
def Z9(n): return 860160 * csum(n, 5)
def Z11(n): return 10321920 * csum(n, 7)

def integrand(n, x):
    return sum((F(i * (i + 1) * (i + 2)) * rcoef(n, i, k) * ((F(x + k) + F(1, 2)) ** -1) ** (i + 3)
                for i in range(1, 9) for k in range(n + 1)), F(0))

def dn(n): return lcm_upto(n)
def Phi(n):
    p = 1
    for q in range(n + 1):
        if q >= 11 and 2 * n < q * q and all(q % r for r in range(2, int(q ** .5) + 1)):
            p *= q
    return p
def Dn(n): return dn(n) ** 12 // Phi(n)

def Tser(n, l):
    pre = smul(F(2) ** (16 * n), mul(pw(ser(F(l) - F(1, 2), -1), 3), pw(psPoch(F(1, 2), -1, nsub(l, 1)), 8)))
    s = ser(0)
    for k in range(l, n + 1):
        t = mul(ser(F(n) - 2 * k, 2), pw(psPoch(F(l) + F(1, 2), -1, nsub(k, l)), 8))
        t = mul(t, pw(psPoch(F(1, 2), 1, nsub(n, k)), 8))
        t = mul(t, inv(mul(pw(psPoch(1, -1, k), 8), pw(psPoch(1, 1, nsub(n, k)), 8))))
        s = add(s, t)
    return mul(pre, s)

def chains(m, N):
    return list(itertools.combinations_with_replacement(range(N + 1), m))
def chainPrev(ch, k): return 0 if k == 0 else ch[k - 1]
def chainLast(ch): return 0 if len(ch) == 0 else ch[-1]

def Pser(n, l):
    t = smul(F(2) ** (16 * n), mul(pw(ser(F(l) - F(1, 2), -1), 3), pw(psPoch(F(1, 2), -1, nsub(l, 1)), 8)))
    t = mul(t, pw(psPoch(F(1, 2), 1, nsub(n, l)), 8))
    return mul(t, inv(mul(pw(psPoch(1, -1, l), 8), pw(psPoch(1, 1, nsub(n, l)), 8))))

def Fser(n, l, ch):
    N = nsub(n, l)
    z = mul(ser(-F(N) - 1), ser(F(l), -2))
    z = mul(z, Pser(n, l))
    c = F(1)
    for i in range(8):
        d = nsub(ch[i], chainPrev(ch, i))
        c *= rpoch(F(1, 2), d) / factorial(d)
    z = smul(c, z)
    for i in range(7):
        Ji = ch[i]
        z = mul(z, mul(psPoch(-F(N), -1, Ji), psPoch(F(l) + F(1, 2), -1, Ji)))
        z = mul(z, inv(mul(psPoch(F(l) + 1, -1, Ji), psPoch(F(1, 2) - N, -1, Ji))))
    J8 = ch[7]
    z = mul(z, mul(psPoch(F(l) + 1, -2, J8), ser(rpoch(-F(N), J8))))
    z = mul(z, inv(mul(ser(F(J8) + 1), mul(psPoch(F(l) + 1, -1, J8), psPoch(F(1, 2) - N, -1, J8)))))
    return z

def FJ0(n, l, ch):
    N = nsub(n, l)
    v = F(-64) / (2 * F(l) - 1) ** 4 * comb(nsub(2 * l, 2), nsub(l, 1)) * (F(N) + 1) / (F(ch[7]) + 1)
    for i in range(8):
        d = nsub(ch[i], chainPrev(ch, i)); v *= comb(2 * d, d)
    for i in range(7):
        v *= comb(2 * (l + ch[i]), l + ch[i])
    for i in range(8):
        e = nsub(nsub(n, l), ch[i]); v *= comb(2 * e, e)
    return v

def Bn(n, x): return comb(x + n, n)
def Yl(n, l, x): return comb(nsub(x + l, 1), nsub(l, 1)) * comb(x + n, nsub(n, l))
def Wl(n, l): return factorial(nsub(l, 1)) * factorial(nsub(n, l))

_H = {}
def hcoef(n, beta, x):
    if (n, x) not in _H:
        z = ser(1)
        for k in range(n + 1):
            z = mul(z, inv(pw(ser(2 * x + 2 * k + 1, 1), 8)))
        _H[(n, x)] = z
    return _H[(n, x)][beta]

def leibTerm(n, g, beta, M, x):
    v = F(-6) * F(2) ** (24 * n + 8) * (F(2 * x + 1 + n) if g == 0 else F(2)) * F(2) ** beta * hcoef(n, beta, x)
    for l in range(1, n + 1): v *= comb(8, M.get(l, 0))
    e = 5 + g + beta
    v *= F(factorial(n)) ** e * F(Bn(n, x)) ** e
    for l in range(1, n + 1):
        v *= (F(Wl(n, l)) * Yl(n, l, x)) ** M.get(l, 0)
    return v

def domTerm(m, x):
    n = 2 ** m - 1; k0 = 2 ** (m - 1)
    return (F(-336) * F(2) ** (24 * n + 8) * F(factorial(n)) ** 6 * F(Wl(n, k0)) ** 2 * F(Bn(n, x)) ** 6
            * F(Yl(n, k0, x)) ** 2 * hcoef(n, 0, x))

def target(m): return 32 * (2 ** m - 1) + 14 - 11 * m

def antidiag(n, a):
    out = []
    for combo in itertools.combinations_with_replacement(range(1, n + 1), a):
        M = {}
        for l in combo: M[l] = M.get(l, 0) + 1
        out.append(M)
    return out

def riemann(f, N): return sum((F(f(x)) for x in range(2 ** N)), F(0)) / 2 ** N

def DeltaGe_ok(m, c, f, kmax):
    for k in range(2 ** m, kmax):
        km = k - 2 ** natlog2(k)
        d = F(f(k)) - F(f(km))
        if d != 0 and vp(d, 2) < c + natlog2(k):
            return False, (k, vp(d, 2) - natlog2(k))
    return True, None

def DeltaAll_ok(c, f, kmax):
    ok, w = DeltaGe_ok(0, c, f, kmax)
    f0 = F(f(0))
    return ok and (f0 == 0 or vp(f0, 2) >= c - 1), w

# ---------------- independent references -----------------
def laurent_direct(n, k):
    """eps^8 R_n(-k+eps) factor by factor from the PRODUCT form (no Psi sign manipulations)."""
    z = ser(F(2) ** (16 * n) * (n - 2 * k), 2 * F(2) ** (16 * n))
    for j in range(n):
        z = mul(z, pw(ser(F(j - k) + F(1, 2), 1), 8))
    for j in range(n + 1):
        if j != k:
            z = mul(z, inv(pw(ser(j - k, 1), 8)))
    return z

def Rval(n, t):
    t = F(t)
    num = F(2) ** (16 * n) * (2 * t + n)
    for j in range(n): num *= (t + j + F(1, 2)) ** 8
    den = F(1)
    for j in range(n + 1): den *= (t + j) ** 8
    return num / den

def Rser_direct(n, y):
    """Taylor series of R_n(y+eps), product form."""
    y = F(y)
    z = smul(F(2) ** (16 * n), ser(2 * y + n, 2))
    for j in range(n): z = mul(z, pw(ser(y + j + F(1, 2), 1), 8))
    for j in range(n + 1): z = mul(z, inv(pw(ser(y + j, 1), 8)))
    return z

# ================================================================
def sec_pf():
    print("== PF: Lean rcoef vs product-form Laurent expansion; R_n(t) = sum r (t+k)^-i at random t")
    random.seed(1)
    for n in range(0, 21):
        for k in range(n + 1):
            L = laurent_direct(n, k)
            for i in range(1, 9):
                check("rcoef==direct n=%d i=%d k=%d" % (n, i, k), rcoef(n, i, k) == L[8 - i])
        for _ in range(4):
            t = F(random.randint(-500, 500), random.randint(1, 50))
            if any(t + j == 0 for j in range(n + 1)): continue
            rhs = sum((rcoef(n, i, k) * (t + k) ** -i for i in range(1, 9) for k in range(n + 1)), F(0))
            check("PF value n=%d t=%s" % (n, t), Rval(n, t) == rhs)
        # series identity: Rser == sum C r * ((C(y+k)+X)^i)^-1   (Stmt_PF.series), random y
        for _ in range(2):
            y = F(random.randint(-60, 60), random.randint(1, 7))
            if any(y + j == 0 for j in range(n + 1)): continue
            lhs = Rser_direct(n, y)
            rhs = ser(0)
            for i in range(1, 9):
                for k in range(n + 1):
                    rhs = add(rhs, smul(rcoef(n, i, k), inv(pw(ser(y + k, 1), i))))
            check("PF.series n=%d y=%s" % (n, y), lhs == rhs)
    # CoeffVanish
    for n in range(0, 25):
        for i in range(0, 11):
            for k in range(n + 1):
                check("symm", rcoef(n, i, n - k) == (-1) ** (i + 1) * rcoef(n, i, k), (n, i, k))
        check("c1 n=%d" % n, csum(n, 1) == 0)
        for i in range(0, 14, 2):
            check("ceven n=%d i=%d" % (n, i), csum(n, i) == 0)
    print("  n=0:", rho0(0), Z7(0), Z9(0), Z11(0), " n=1:", rho0(1), Z7(1), Z9(1), Z11(1))
    check("n=1 values (proof.md)", rho0(1) == 14155776 and Z7(1) == -849346560 and Z9(1) == 21139292160 and Z11(1) == 52848230400)
    check("n=0 value (proof.md)", Z11(0) == 20643840)

def sec_L1():
    print("== L1 algebra: sum_{i,k} (i)_3 r (J_{i+3} - (i+3) A_k) == rho0 + 60c3 J6 + 210 c5 J8 + 504 c7 J10 (J symbolic)")
    for n in range(0, 16):
        coef = {s: F(0) for s in range(4, 12)}
        const = F(0)
        for i in range(1, 9):
            for k in range(n + 1):
                a = F(i * (i + 1) * (i + 2)) * rcoef(n, i, k)
                coef[i + 3] += a
                const -= a * (i + 3) * Ahalf(k, i + 4)
        want = {s: F(0) for s in range(4, 12)}
        want[6] = 60 * csum(n, 3); want[8] = 210 * csum(n, 5); want[10] = 504 * csum(n, 7)
        check("L1 n=%d const" % n, const == rho0(n))
        check("L1 n=%d coefs" % n, coef == want, (coef, want))
    # zeta2 normalisation constants
    check("Z7/zeta", F(46080, 768) == 60); check("Z9/zeta", F(860160, 4096) == 210)
    check("Z11/zeta", F(10321920, 20480) == 504)

def sec_denoms(nmax=60):
    print("== BlockF (all j), L2a, L2b, L2c, L2cor up to n=%d" % nmax)
    for n in range(0, 41):
        d = dn(n)
        for k in range(n + 1):
            # exact polynomial (degree n) of 4^n/n! (1/2-e)_k (1/2+e)_{n-k}
            poly = [F(1)]
            for j in range(k):
                poly = [a + b for a, b in itertools.zip_longest([F(j) + F(1, 2)] * 0 + [x * (F(j) + F(1, 2)) for x in poly] + [F(0)],
                                                               [F(0)] + [-x for x in poly], fillvalue=F(0))]
            for j in range(n - k):
                poly = [a + b for a, b in itertools.zip_longest([x * (F(j) + F(1, 2)) for x in poly] + [F(0)],
                                                               [F(0)] + [x for x in poly], fillvalue=F(0))]
            poly = [F(4) ** n / factorial(n) * x for x in poly]
            for j in range(len(poly) + 3):
                cj = poly[j] if j < len(poly) else F(0)
                check("BlockF n=%d k=%d j=%d" % (n, k, j), is_int(F(d) ** j * cj))
    for n in range(0, nmax + 1):
        d = dn(n)
        for k in range(n + 1):
            for i in range(1, 9):
                check("L2a n=%d i=%d k=%d" % (n, i, k), is_int(F(d) ** (8 - i) * rcoef(n, i, k)))
        r0 = rho0(n)
        check("L2b n=%d" % n, is_int(F(d) ** 12 * r0))
        for p in primes_upto(max(2 * n, 11)):
            if p >= 11 and 2 * n < p * p and r0 != 0:
                check("L2c n=%d p=%d" % (n, p), vp(r0, p) >= -11, vp(r0, p))
        D = Dn(n)
        check("Phi|dn", dn(n) % Phi(n) == 0)
        for nm, val in (("rho0", r0), ("Z7", Z7(n)), ("Z9", Z9(n)), ("Z11", Z11(n))):
            check("L2cor %s n=%d" % (nm, n), is_int(D * val))
        if n % 10 == 0: print("   n=%d ok so far (%d fails)" % (n, len(FAILS)), flush=True)

def sec_residue():
    print("== ResidueForm n<=12")
    for n in range(0, 13):
        rhs = -24 * sum((Tser(n, l)[7] for l in range(1, n + 1)), F(0))
        check("ResidueForm n=%d" % n, rho0(n) == rhs)

def Tval(n, l, e):
    e = F(e)
    def rp(c, d, k):  # (c + d e)_k
        p = F(1)
        for j in range(k): p *= (F(c) + j + d * e)
        return p
    pre = F(2) ** (16 * n) * (F(l) - F(1, 2) - e) ** 3 * rp(F(1, 2), -1, l - 1) ** 8
    s = F(0)
    for k in range(l, n + 1):
        s += ((F(n) - 2 * k + 2 * e) * rp(F(l) + F(1, 2), -1, k - l) ** 8 * rp(F(1, 2), 1, n - k) ** 8
              / (rp(1, -1, k) ** 8 * rp(1, 1, n - k) ** 8))
    return pre * s

def Fval(n, l, ch, e):
    e = F(e); N = n - l
    def rp(c, d, k):
        p = F(1)
        for j in range(k): p *= (F(c) + j + d * e)
        return p
    P = (F(2) ** (16 * n) * (F(l) - F(1, 2) - e) ** 3 * rp(F(1, 2), -1, l - 1) ** 8 * rp(F(1, 2), 1, N) ** 8
         / (rp(1, -1, l) ** 8 * rp(1, 1, N) ** 8))
    z = (-F(N) - 1) * (F(l) - 2 * e) * P
    for i in range(8):
        d = ch[i] - chainPrev(ch, i)
        z *= rpoch(F(1, 2), d) / factorial(d)
    for i in range(7):
        Ji = ch[i]
        z *= rp(-F(N), -1, Ji) * rp(F(l) + F(1, 2), -1, Ji) / (rp(F(l) + 1, -1, Ji) * rp(F(1, 2) - N, -1, Ji))
    J8 = ch[7]
    z *= rp(F(l) + 1, -2, J8) * rpoch(-F(N), J8) / ((F(J8) + 1) * rp(F(l) + 1, -1, J8) * rp(F(1, 2) - N, -1, J8))
    return z

def sec_andrews_applied(nmax_series=5, nmax_val=8):
    print("== AndrewsApplied: series (n<=%d) and rational-eps values (n<=%d); FJClosed" % (nmax_series, nmax_val))
    random.seed(7)
    for n in range(1, nmax_series + 1):
        for l in range(1, n + 1):
            T = Tser(n, l); S_ = ser(0)
            for ch in chains(8, n - l):
                Fj = Fser(n, l, ch)
                check("FJClosed(series) n=%d l=%d %s" % (n, l, ch), Fj[0] == FJ0(n, l, ch))
                S_ = add(S_, Fj)
            check("AndrewsApplied(series) n=%d l=%d" % (n, l), S_ == T)
    for n in range(1, nmax_val + 1):
        for l in range(1, n + 1):
            e = F(random.randint(1, 999), random.randint(1000, 5000)) * random.choice([1, -1])
            T = Tval(n, l, e)
            tot = F(0)
            for ch in chains(8, n - l):
                tot += Fval(n, l, ch, e)
                if n > nmax_series:
                    check("FJClosed(val) n=%d l=%d" % (n, l), Fval(n, l, ch, 0) == FJ0(n, l, ch))
            check("AndrewsApplied(val) n=%d l=%d e=%s" % (n, l, e), tot == T)
        print("   n=%d done (%d fails)" % (n, len(FAILS)), flush=True)

def andrews_sides(m, N, a, b, c):
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
    return lhs, pre * s

def hyps_ok(m, N, a, b, c):
    if a == 0: return False
    if any(rpoch(1 + a - b[k], N) == 0 or rpoch(1 + a - c[k], N) == 0 for k in range(m + 1)): return False
    if rpoch(1 + a + N, N) == 0 or rpoch(b[m] + c[m] - a - N, N) == 0: return False
    return True

def sec_andrews():
    print("== Andrews_Stmt: random rational, random small-integer/half-integer (degenerate) parameters")
    random.seed(12345)
    cnt = 0; cntdeg = 0
    for m in range(0, 6):
        for N in range(0, 7 if m <= 3 else 5):
            for trial in range(8):
                rnd = lambda: F(random.randint(-10 ** 6, 10 ** 6), random.randint(1, 10 ** 4))
                a = rnd(); b = [rnd() for _ in range(m + 1)]; c = [rnd() for _ in range(m + 1)]
                if not hyps_ok(m, N, a, b, c): continue
                L, R = andrews_sides(m, N, a, b, c)
                check("Andrews rnd m=%d N=%d" % (m, N), L == R, (a, b, c)); cnt += 1
            # degenerate: parameters from a small set of integers / half-integers
            for trial in range(40):
                pool = [F(x, 2) for x in range(-12, 13)]
                a = random.choice(pool); b = [random.choice(pool) for _ in range(m + 1)]
                c = [random.choice(pool) for _ in range(m + 1)]
                if not hyps_ok(m, N, a, b, c): continue
                L, R = andrews_sides(m, N, a, b, c)
                check("Andrews deg m=%d N=%d" % (m, N), L == R, (a, b, c)); cntdeg += 1
    for N in range(0, 4):
        for trial in range(3):
            rnd = lambda: F(random.randint(-10 ** 5, 10 ** 5), random.randint(1, 10 ** 3))
            m = 8
            a = rnd(); b = [rnd() for _ in range(m + 1)]; c = [rnd() for _ in range(m + 1)]
            if not hyps_ok(m, N, a, b, c): continue
            L, R = andrews_sides(m, N, a, b, c)
            check("Andrews rnd m=8 N=%d" % N, L == R); cnt += 1
    print("  Andrews: %d generic + %d degenerate instances tested" % (cnt, cntdeg))
    # the specialisation used downstream (b_k,c_k) = (-N-e, l+1/2-e) x8, (1, 1+a+N), at rational e
    for n in range(1, 7):
        for l in range(1, n + 1):
            e = F(random.randint(1, 99), random.randint(100, 999))
            N = n - l; a = -F(n) + 2 * l - 2 * e
            b = [-F(N) - e] * 8 + [F(1)]; c = [F(l) + F(1, 2) - e] * 8 + [1 + a + N]
            check("spec hyps n=%d l=%d" % (n, l), hyps_ok(8, N, a, b, c))
            L, R = andrews_sides(8, N, a, b, c)
            check("spec identity n=%d l=%d" % (n, l), L == R)
            # T = -a P sum_kappa (a+2k)/a [..]^8, and LHS == that sum
            s = sum(((a + 2 * kap) / a * (rpoch(b[0], kap) * rpoch(c[0], kap) / (rpoch(1 + a - b[0], kap) * rpoch(1 + a - c[0], kap))) ** 8
                     for kap in range(N + 1)), F(0))
            check("spec LHS n=%d l=%d" % (n, l), s == L)
            Pv = (F(2) ** (16 * n) * (F(l) - F(1, 2) - e) ** 3 * rpoch(F(1, 2) - e, l - 1) ** 8 * rpoch(F(1, 2) + e, N) ** 8
                  / (rpoch(1 - e, l) ** 8 * rpoch(1 + e, N) ** 8))
            check("T = -a P LHS n=%d l=%d" % (n, l), Tval(n, l, e) == -a * Pv * L)

def sec_kummer():
    print("== FJKummer: exhaustive critical chains for p=11,13 and several n")
    for p in (11, 13, 17):
        l = (p + 1) // 2
        for n in range(l + p, min(l + p + 12, (p * p - 1) // 2 + 1)):
            if not (2 * n < p * p): continue
            N = n - l
            mn = 99
            for J8 in range(p - 1, N + 1, p):
                for pre in itertools.combinations_with_replacement(range(J8 + 1), 7):
                    ch = pre + (J8,)
                    v = vp(FJ0(n, l, ch), p)
                    mn = min(mn, v)
                    if v < -4:
                        check("FJKummer", False, (n, l, ch, p, v))
            print("   p=%d n=%d l=%d: min v_p over critical chains = %d" % (p, n, l, mn), flush=True)

def sec_leibniz():
    print("== Leibniz: integrand == -6 [e^3] R_n(x+1/2+e) (product form) == sum leibTerm")
    for n in range(0, 7):
        for x in range(0, 8):
            I = integrand(n, x)
            direct = -6 * Rser_direct(n, F(x) + F(1, 2))[3]
            check("integrand=-R''' n=%d x=%d" % (n, x), I == direct)
            tot = F(0)
            for g in range(2):
                for beta in range(4 - g):
                    for M in antidiag(n, 3 - g - beta):
                        tot += leibTerm(n, g, beta, M, x)
            check("Leibniz n=%d x=%d" % (n, x), tot == I)

def sec_deltafun():
    print("== DeltaFun on wider ranges")
    for j in range(0, 9):
        for Nb in range(0, 18):
            ok, w = DeltaAll_ok(-natlog2(Nb), lambda x: comb(x + j, Nb), 600)
            check("binom j=%d N=%d" % (j, Nb), ok, w)
            for mm in range(natlog2(Nb) + 1, natlog2(Nb) + 3):
                ok, w = DeltaGe_ok(mm, 1 - natlog2(Nb), lambda x: comb(x + j, Nb) ** 2, 600)
                check("binomSq j=%d N=%d m=%d" % (j, Nb, mm), ok, w)
    for n in range(0, 5):
        for beta in range(0, 5):
            f = lambda x: hcoef(n, beta, x)
            check("hcoefInt", all(vp(f(x), 2) >= 0 for x in range(300) if f(x) != 0), (n, beta))
            ok, w = DeltaAll_ok(0, f, 300)
            check("hcoefDelta n=%d b=%d" % (n, beta), ok, w)
    print("== Digit m<=16 (v2(a!) by Legendre sum floor(a/2^i), independent of digit sums)")
    def v2fact(a):
        s, q = 0, 2
        while q <= a:
            s += a // q; q *= 2
        return s
    check("v2fact sanity", all(v2fact(a) == vp(factorial(a), 2) for a in range(0, 300)))
    for m in range(0, 17):
        n = 2 ** m - 1
        check("fact", v2fact(n) == nsub(nsub(2 ** m, 1), m), m)
        if m >= 2:
            k0 = 2 ** (m - 1)
            check("dom", v2fact(k0 - 1) + v2fact(nsub(nsub(2 ** m, 1), k0)) == nsub(2 ** m, 2 * m), m)
            if m <= 16:
                for l in range(1, n + 1):
                    if l != k0:
                        check("other", v2fact(l - 1) + v2fact(nsub(nsub(2 ** m, 1), l)) >= nsub(2 ** m + 1, 2 * m), (m, l))

def sec_L5(mmax=5):
    print("== LeibTermBound / L5Dom / L5 at Riemann-sum level")
    random.seed(99)
    for m in (2, 3, 4):
        n = 2 ** m - 1; k0 = 2 ** (m - 1)
        kmax = 2 ** (m + (6 if m <= 3 else 3))
        worst = 99
        for g in range(2):
            for beta in range(4 - g):
                Ms = antidiag(n, 3 - g - beta)
                if m == 4: Ms = random.sample(Ms, min(len(Ms), 30)) + [{k0: 3 - g - beta}] if 3 - g - beta > 0 else Ms
                for M in Ms:
                    c = (32 * (2 ** m - 1) + 13 - 11 * m + beta * m + sum(vp(comb(8, M.get(l, 0)), 2) for l in range(1, n + 1))
                         + sum(M.get(l, 0) for l in range(1, n + 1) if l != k0))
                    ok, w = DeltaAll_ok(c, lambda x: leibTerm(n, g, beta, M, x), kmax)
                    check("LeibTermBound m=%d g=%d b=%d M=%s" % (m, g, beta, M), ok, w)
                    if not (g == 1 and beta == 0 and M == {k0: 2}):
                        worst = min(worst, c - (target(m) + 2))
        check("nondominant slack>=0 m=%d" % m, worst >= 0, worst)
        print("   m=%d LeibTermBound ok on k<%d, min nondominant slack %d" % (m, kmax, worst), flush=True)
    for m in range(2, mmax + 1):
        n = 2 ** m - 1
        if m <= 4:
            ok, w = DeltaGe_ok(m, target(m) + 2, lambda x: domTerm(m, x), 2 ** (m + (5 if m <= 3 else 3)))
            check("L5Dom Delta_m m=%d" % m, ok, w)
        Rm = riemann(lambda x: domTerm(m, x), m)
        check("L5Dom level m, m=%d" % m, vp(Rm, 2) == target(m), (vp(Rm, 2), target(m)))
        vals = []
        for Mlev in range(m, m + (5 if m <= 4 else 3)):
            RM = riemann(lambda x: integrand(n, x), Mlev)
            vals.append(vp(RM, 2))
            check("L5 Riemann m=%d M=%d" % (m, Mlev), vp(RM, 2) == target(m), (vp(RM, 2), target(m)))
        print("   m=%d n=%d target=%d  v2(R_M(integrand)), M=m..: %s" % (m, n, target(m), vals), flush=True)

def sec_L4(nmax=45):
    print("== L4 with (3.4e8, 2) and with (2^70, 10), n<=%d" % nmax)
    for n in list(range(0, nmax + 1)):
        b1 = F(340000000) * (n + 1) ** 2 * F(2) ** (16 * n)
        b2 = F(2) ** 70 * (n + 1) ** 10 * F(2) ** (16 * n)
        for nm, val in (("rho0", rho0(n)), ("Z7", Z7(n)), ("Z9", Z9(n)), ("Z11", Z11(n))):
            check("L4a %s n=%d" % (nm, n), abs(val) <= b1)
            check("L4b %s n=%d" % (nm, n), abs(val) <= b2)

SECS = dict(pf=sec_pf, L1=sec_L1, denoms=sec_denoms, residue=sec_residue, aa=sec_andrews_applied,
            andrews=sec_andrews, kummer=sec_kummer, leibniz=sec_leibniz, deltafun=sec_deltafun, L5=sec_L5, L4=sec_L4)


def _big():
    sec_denoms(150)
def _bigaa():
    sec_andrews_applied(5, 10)
SECS["denoms150"] = _big
SECS["aa10"] = _bigaa

if __name__ == "__main__":
    t0 = time.time()
    names = sys.argv[1:] or ["all"]
    if names == ["all"]: names = list(SECS)
    for nm in names:
        t1 = time.time(); c0 = NCHECK[0]; SECS[nm]()
        print("   [%s: %.1fs, %d checks]" % (nm, time.time() - t1, NCHECK[0] - c0), flush=True)
    print("\nTOTAL FAILS: %d  (%.1fs)" % (len(FAILS), time.time() - t0))
    for f in FAILS[:40]: print("   ", f)
    sys.exit(1 if FAILS else 0)
