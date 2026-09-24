"""Division-free Zeilberger certificate for the polynomial Pfaff-Saalschuetz identity (PPS).

   F(M,s) := C(M,s) (x)_s (y)_s (z-x-y)_{M-s} (z+s)_{2M-s}
   S(M)   := sum_{s=0}^{M} F(M,s)          R(M) := (z-x)_M (z-y)_M (z+M)_M
   PPS:  S(M) = R(M)   (identity in Z[x,y,z]; holds in every commutative ring)

Recurrence:  (z+M) S(M+1) = c(M) S(M),   c(M) = (z-x+M)(z-y+M)(z+2M)(z+2M+1),
and (z+M) R(M+1) = c(M) R(M).
Certificate (derived by hand via Gosper, verified below):
   G(M,0) = 0,  G(M,s+1) = g(M,s) := -(z+2M+1) C(M,s) (x)_{s+1} (y)_{s+1} (z-x-y)_{M-s} (z+s)_{2M+1-s}
   (z+M) F(M+1,s) - c(M) F(M,s) = G(M,s+1) - G(M,s)      for 0 <= s <= M+1,
   G(M,0) = G(M,M+2) = 0   (C(M,M+1) = 0).

This script (1) checks the telescoping identity symbolically, case by case, in the "atom" form used
in Lean (so that `ring` / `linear_combination` can close each case), and computes the multiplier
lambda for the middle case, where the binomial relation (u+1) C(M,u+1) = (t+1) C(M,u) is needed;
(2) checks the telescoping identity and PPS numerically with exact rationals.
"""
import sympy as sp
from fractions import Fraction as Fr
import math, random

x, y, z, u, t = sp.symbols('x y z u t')
X, Y, P, Z, C1, C2 = sp.symbols('X Y P Z C1 C2')

# ---------- middle case: s = u+1 <= M, M = u+1+t ----------
M = u + 1 + t
cM = (z - x + M) * (z - y + M) * (z + 2 * M) * (z + 2 * M + 1)
F_M1_s = (C1 + C2) * X * Y * P * (z - x - y + t) * Z * (z + 2 * u + 2 * t + 2) * (z + 2 * u + 2 * t + 3)
F_M_s = C1 * X * Y * P * Z
G_s1 = -(z + 2 * M + 1) * C1 * X * (x + u + 1) * Y * (y + u + 1) * P * Z * (z + 2 * u + 2 * t + 2)
G_s = -(z + 2 * M + 1) * C2 * X * Y * P * (z - x - y + t) * (z + u) * Z * (z + 2 * u + 2 * t + 2)
E = sp.expand((z + M) * F_M1_s - cM * F_M_s - (G_s1 - G_s))
rel = (u + 1) * C1 - (t + 1) * C2
lam, rem = sp.div(sp.Poly(E, C1, C2), sp.Poly(rel, C1, C2))
print("middle case: remainder after dividing by the binomial relation:", sp.simplify(rem.as_expr()))
lam = sp.factor(lam.as_expr())
print("middle case: lambda =", lam)
assert sp.expand(E - lam * rel) == 0

# ---------- case s = 0 ----------
M0 = sp.Symbol('M')
P0, Z0 = sp.symbols('P0 Z0')
c0 = (z - x + M0) * (z - y + M0) * (z + 2 * M0) * (z + 2 * M0 + 1)
E0 = sp.expand((z + M0) * P0 * (z - x - y + M0) * Z0 * (z + 2 * M0) * (z + 2 * M0 + 1) - c0 * P0 * Z0
               - (-(z + 2 * M0 + 1) * x * y * P0 * Z0 * (z + 2 * M0)))
print("case s = 0 residual:", E0)

# ---------- case s = M+1 ----------
Xm, Ym, Zm = sp.symbols('Xm Ym Zm')   # (x)_{M+1}, (y)_{M+1}, (z+M+1)_{M}
# F(M+1,M+1) = Xm Ym (z+M+1)_{M+1} = Xm Ym Zm (z+2M+1);  G(M,M+2)=0;  G(M,M+1) = g(M,M)
#   = -(z+2M+1) Xm Ym (z+M)_{M+1} = -(z+2M+1) Xm Ym (z+M) Zm
E1 = sp.expand((z + M0) * Xm * Ym * Zm * (z + 2 * M0 + 1) - (0 - (-(z + 2 * M0 + 1) * Xm * Ym * (z + M0) * Zm)))
print("case s = M+1 residual:", E1)

# ---------- numeric checks (exact rationals) ----------
def poch(a, k):
    p = Fr(1)
    for j in range(k):
        p *= a + j
    return p

def Fnum(Mv, s, xv, yv, zv):
    if s > Mv: return Fr(0)
    return math.comb(Mv, s) * poch(xv, s) * poch(yv, s) * poch(zv - xv - yv, Mv - s) * poch(zv + s, 2 * Mv - s)

def gnum(Mv, s, xv, yv, zv):
    if s > Mv: return Fr(0)
    return -(zv + 2 * Mv + 1) * math.comb(Mv, s) * poch(xv, s + 1) * poch(yv, s + 1) * poch(zv - xv - yv, Mv - s) * poch(zv + s, 2 * Mv + 1 - s)

def Gnum(Mv, s, xv, yv, zv):
    return Fr(0) if s == 0 else gnum(Mv, s - 1, xv, yv, zv)

random.seed(1)
bad = 0
for _ in range(300):
    Mv = random.randint(0, 8)
    xv, yv, zv = [Fr(random.randint(-30, 30), random.choice([1, 2, 3, 7])) for _ in range(3)]
    if random.random() < 0.3: zv = Fr(-random.randint(0, 2 * Mv + 2))
    cv = (zv - xv + Mv) * (zv - yv + Mv) * (zv + 2 * Mv) * (zv + 2 * Mv + 1)
    for s in range(Mv + 2):
        lhs = (zv + Mv) * Fnum(Mv + 1, s, xv, yv, zv) - cv * Fnum(Mv, s, xv, yv, zv)
        if lhs != Gnum(Mv, s + 1, xv, yv, zv) - Gnum(Mv, s, xv, yv, zv):
            bad += 1
    S = sum(Fnum(Mv, s, xv, yv, zv) for s in range(Mv + 1))
    R = poch(zv - xv, Mv) * poch(zv - yv, Mv) * poch(zv + Mv, Mv)
    if S != R: bad += 1
print("numeric failures:", bad)
