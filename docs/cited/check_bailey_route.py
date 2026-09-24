"""Exact-arithmetic check of the proposed Lean route for Andrews_Stmt (KR Theoreme 8).

Route (q = 1 Bailey chain, "polynomial" normalisation, no division by (1+a)_k):

  BP(alpha, beta; n):   (1+a)_{2n} beta_n = sum_{r=0}^{n} alpha_r (1+a+n+r)_{n-r} / (n-r)!

  PPS(M; x, y, z):  sum_{s=0}^{M} (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s} / (s! (M-s)!)
                        = (z-x)_M (z-y)_M (z+M)_M / M!                      (polynomial Pfaff-Saalschuetz)

  UNIT:   alpha0_r = (a+2r)/a (a)_r (-1)^r / r!,  beta0_n = [n = 0]   satisfy BP for every n.

  STEP (Bailey lemma):  BP(alpha,beta; j) for all j <= n  ==>  BP(alpha',beta'; n) where
     alpha'_r = (rho)_r (sig)_r / ((1+a-rho)_r (1+a-sig)_r) alpha_r
     beta'_n  = sum_{j<=n} (rho)_j (sig)_j (1+a-rho-sig)_{n-j} / ((1+a-rho)_n (1+a-sig)_n (n-j)!) beta_j
     (needs only (1+a-rho)_n, (1+a-sig)_n != 0)

  Bchain(m, b, c, n) = sum_{i in chains m n} W_m(i) (1+a-b_L-c_L)_{n-last i} / ((1+a-b_L)_n (1+a-c_L)_n (n-last i)!)
  Andrews(m, N):  LHS = N! (1+a)_N Bchain(m+1 pairs, N) = RHS.

We check every piece at random rational points, INCLUDING degenerate points allowed by the
Andrews_Stmt hypotheses (e.g. a = -1, -2, -3/2 where (1+a)_N = 0 or (1+a)_{2N} = 0).
"""
import random, itertools, math
from fractions import Fraction as F

def poch(x, k):
    p = F(1)
    for j in range(k):
        p *= (x + j)
    return p

fact = math.factorial

def PPS_lhs(M, x, y, z):
    return sum(poch(x, s) * poch(y, s) * poch(z - x - y, M - s) * poch(z + s, 2 * M - s) / (fact(s) * fact(M - s))
               for s in range(M + 1))

def PPS_rhs(M, x, y, z):
    return poch(z - x, M) * poch(z - y, M) * poch(z + M, M) / fact(M)

def chains(m, n):
    return list(itertools.combinations_with_replacement(range(n + 1), m))

def W(m, a, b, c, i):
    """prod_{k=0}^{m-1} (1+a-b_k-c_k)_{i_k - i_{k-1}} (b_{k+1})_{i_k} (c_{k+1})_{i_k} /
                       ((i_k-i_{k-1})! (1+a-b_k)_{i_k} (1+a-c_k)_{i_k})"""
    val = F(1)
    prev = 0
    for k in range(m):
        d = i[k] - prev
        val *= poch(1 + a - b[k] - c[k], d) * poch(b[k + 1], i[k]) * poch(c[k + 1], i[k]) / (
            fact(d) * poch(1 + a - b[k], i[k]) * poch(1 + a - c[k], i[k]))
        prev = i[k]
    return val

def Bchain(m, a, b, c, n):
    L = m
    tot = F(0)
    for i in chains(m, n):
        last = i[-1] if m > 0 else 0
        tot += W(m, a, b, c, i) * poch(1 + a - b[L] - c[L], n - last) / (
            poch(1 + a - b[L], n) * poch(1 + a - c[L], n) * fact(n - last))
    return tot

def alpha(m, a, b, c, r):
    val = (a + 2 * r) / a * poch(a, r) * (-1) ** r / fact(r)
    for k in range(m + 1):
        val *= poch(b[k], r) * poch(c[k], r) / (poch(1 + a - b[k], r) * poch(1 + a - c[k], r))
    return val

def BP_holds(alpha_f, beta_f, a, n):
    lhs = poch(1 + a, 2 * n) * beta_f(n)
    rhs = sum(alpha_f(r) * poch(1 + a + n + r, n - r) / fact(n - r) for r in range(n + 1))
    return lhs == rhs

def andrews_lhs(m, N, a, b, c):
    tot = F(0)
    for k in range(N + 1):
        t = (a + 2 * k) / a * poch(a, k) / fact(k)
        for j in range(m + 1):
            t *= poch(b[j], k) * poch(c[j], k) / (poch(1 + a - b[j], k) * poch(1 + a - c[j], k))
        t *= poch(F(-N), k) / poch(1 + a + N, k)
        tot += t
    return tot

def andrews_rhs(m, N, a, b, c):
    L = m
    pre = poch(1 + a, N) * poch(1 + a - b[L] - c[L], N) / (poch(1 + a - b[L], N) * poch(1 + a - c[L], N))
    tot = F(0)
    for i in chains(m, N):
        last = i[-1] if m > 0 else 0
        tot += poch(F(-N), last) / poch(b[L] + c[L] - a - N, last) * W(m, a, b, c, i)
    return pre * tot

def rnd():
    return F(random.randint(-40, 40), random.choice([1, 2, 3, 5, 7]))

def hyps_ok(m, N, a, b, c):
    if a == 0: return False
    for k in range(m + 1):
        if poch(1 + a - b[k], N) == 0 or poch(1 + a - c[k], N) == 0: return False
    if poch(1 + a + N, N) == 0: return False
    if poch(b[m] + c[m] - a - N, N) == 0: return False
    return True

random.seed(20260924)
fails = 0
# (1) PPS at random points, including integer / degenerate ones
cnt = 0
for _ in range(400):
    M = random.randint(0, 7)
    x, y, z = rnd(), rnd(), rnd()
    if random.random() < 0.3: z = F(-random.randint(0, 2 * M + 1))
    if PPS_lhs(M, x, y, z) != PPS_rhs(M, x, y, z):
        fails += 1; print("PPS FAIL", M, x, y, z)
    cnt += 1
print("PPS checked", cnt)

# (2) unit pair, (3) Bailey step, (4) Bchain Bailey relation, (5) Andrews both sides = N!(1+a)_N Bchain
cnt = 0
degenerate = 0
for trial in range(700):
    m = random.choice([0, 0, 1, 1, 2, 2, 3])
    N = random.randint(0, 4 if m < 3 else 3)
    a = rnd()
    if random.random() < 0.35:
        a = random.choice([F(-1), F(-2), F(-3), F(-3, 2), F(-5, 2), F(-2 * N - 1, 1), F(-N - 1)])
    b = [rnd() for _ in range(m + 1)]
    c = [rnd() for _ in range(m + 1)]
    if random.random() < 0.2:
        b[0] = F(-random.randint(0, N))  # terminating b
    if not hyps_ok(m, N, a, b, c):
        continue
    cnt += 1
    if poch(1 + a, 2 * N) == 0: degenerate += 1
    # unit pair
    for n in range(N + 1):
        if not BP_holds(lambda r: (a + 2 * r) / a * poch(a, r) * (-1) ** r / fact(r),
                        lambda nn: F(1) if nn == 0 else F(0), a, n):
            fails += 1; print("UNIT FAIL", a, n)
    # Bchain relation for every prefix length and every n <= N
    for mm in range(m + 1):
        for n in range(N + 1):
            if not BP_holds(lambda r: alpha(mm, a, b, c, r), lambda nn: Bchain(mm, a, b, c, nn), a, n):
                fails += 1; print("BP FAIL", mm, n, a, b, c)
    # recursion of Bchain (chain decomposition)
    for mm in range(1, m + 1):
        for n in range(N + 1):
            L = mm
            rec = sum(poch(b[L], j) * poch(c[L], j) * poch(1 + a - b[L] - c[L], n - j) /
                      (poch(1 + a - b[L], n) * poch(1 + a - c[L], n) * fact(n - j)) * Bchain(mm - 1, a, b, c, j)
                      for j in range(n + 1))
            if rec != Bchain(mm, a, b, c, n):
                fails += 1; print("REC FAIL", mm, n)
    lhs = andrews_lhs(m, N, a, b, c)
    rhs = andrews_rhs(m, N, a, b, c)
    mid = fact(N) * poch(1 + a, N) * Bchain(m, a, b, c, N)
    if not (lhs == rhs == mid):
        fails += 1; print("ANDREWS FAIL", m, N, a, b, c, lhs, rhs, mid)
print("Andrews/Bailey points checked", cnt, "of which (1+a)_{2N} = 0:", degenerate)
print("FAILURES:", fails)
