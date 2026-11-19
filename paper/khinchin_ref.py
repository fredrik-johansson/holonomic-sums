"""
Reference implementation of the dilogarithm-series theta splitting for
Khinchin's constant (Theorem thm:khinchin of zetaF.tex), listed with
annotations in Appendix B of the paper (khinchin_listing.tex).

Exact rational matrices (python-flint fmpq_mat) are multiplied by binary
splitting; real numbers are Arb balls, and every truncation adds its bound
from Section sec:khbounds to the radius.

Usage: python3 khinchin_ref.py [bits]
"""
import sys
from flint import arb, fmpq, fmpq_mat, ctx

u0 = fmpq(1, 16)         # splitting point (rational)
r0 = 16                  # bits of the first bit-burst point
g = 4                    # bit-burst growth factor
half = fmpq(1, 2)

def least(n, cond):                     # min{n' >= n : cond(n')}
    while not cond(n):
        n += 1
    return n

def mat(rows):                          # rational matrix from a list of rows
    return fmpq_mat(len(rows), len(rows[0]),
                    [fmpq(x) for r in rows for x in r])

def matvec(S, v):                       # exact matrix times vector of balls
    return [sum((arb(S[i, j]) * v[j] for j in range(S.ncols())
                 if S[i, j] != 0), arb(0)) for i in range(S.nrows())]

def pm(x, r):                           # x +/- r
    return x + arb(0, arb(r).upper())

def Eip(y):                             # sum_{n>=1} y^n/(n n!)
    return y.ei() - arb.const_euler() - y.log()

# Binary splitting
def BinSplit(T, W, a, b):
    """(P, S): P = T(b-1)...T(a), S = sum_{a<=n<b} W(n) T(n-1)...T(a)."""
    if b == a + 1:
        return T(a), W(a)
    m = (a + b) // 2
    P1, S1 = BinSplit(T, W, a, m)
    P2, S2 = BinSplit(T, W, m, b)
    return P2 * P1, S1 + S2 * P1

# The k-terms I_k
def KTerm(k, eps):
    K = fmpq(k * k); x = K * u0; q = 4 / K; n1 = int(x.ceil()) + 1
    X = arb(x)

    def tau(n):
        p = n * X ** (n - 1) * (-X).exp() / arb(n - 1).fac()
        return arb(q) ** n * min(arb(1), p) / n ** 2

    def R(N):
        if N < n1:
            return 2 * tau(N) + arb(9) / 5 * arb(q) ** n1 / n1 ** 2
        return arb(9) / 5 * arb(q) ** (N + 1) / (N + 1) ** 2

    N = least(1, lambda N: R(N) <= eps)
    T = lambda n: mat([[q, q], [0, 4 * u0 / (n + 1)]])
    W = lambda n: mat([[fmpq(1, n * n), 0]])
    _, S = BinSplit(T, W, 1, N + 1)
    s = matvec(S, [arb(q), arb(4 * u0)])[0]
    return pm((-X).exp() * s, R(N))

# The main term M
def MainTerm(eps):
    U = arb(u0)
    R = lambda N: 6 * (8 * U) ** N / arb(N).fac()
    N = least(1, lambda N: R(N) <= eps)

    def T(i):
        a = 4 * u0 / (i + 1); b = u0 / (i + 1); r = 4 * u0 / fmpq(i + 1) ** 3
        return mat([[a, 0, 0], [r, b, 0], [r, 0, a]])
    W = lambda i: mat([[0, 1, 0], [0, 0, 1], [fmpq(1, i * i), 0, 0]])
    _, S = BinSplit(T, W, 1, N + 1)
    A, B, C = matvec(S, [arb(4 * u0)] * 3)
    return pm((-U).exp() * A - (-4 * U).exp() * B - C / 2, R(N))

# Forcing components of the dual state
def Forcing(E):
    U = arb(u0)
    Eh = E / U.sqrt()
    return [Eh * Eip(4 * U), Eh * (4 * U).exp(), Eh]

# Starting values of the dual state at a rational point c0
def StartValues(c0, eps):
    U, C0 = arb(u0), arb(c0)
    D = (arb.pi() / C0).sqrt() * (C0 / U).sqrt().erfc()
    E = (-C0 / U).exp(); Eh = E / U.sqrt()
    alpha = lambda n: C0 ** n / arb.rising(arb(half), n)
    b = lambda n: arb(4) ** n / arb(n).fac()

    def R(N):
        return 2 * b(N) * max(2 * alpha(N + s) * D
                              + E * U ** (N + s - half) / (N + s - half)
                              for s in (0, 1))
    N = least(1, lambda N: 32 * c0 <= (2 * N + 1) * (2 * N + 2)
              and 8 * u0 <= N + 1 and R(N) <= eps)

    def T(n):
        h = n + half; d = 4 / ((n + 1) * h)
        return mat([[-c0 * d, 0, 0], [0, -c0 * d, u0 * d],
                    [0, 0, 4 * u0 / (n + 1)]])

    def W(n):
        h = n + half
        return mat([[fmpq(1, n), 0, 0], [0, fmpq(1, n), 0], [1, 0, 0],
                    [0, 1, 0], [-c0 / h, 0, 0], [0, -c0 / h, u0 / h]])
    _, S = BinSplit(T, W, 1, N)
    s = matvec(S, [arb(-8 * c0), arb(8 * u0), arb(4 * u0)])
    s = [si + arb(ti) for si, ti in zip(s, [0, 0, 1, 0, -2 * c0, 2 * u0])]
    nu = pm(D * s[0] + Eh * s[1], R(N))
    Y = pm(D * s[2] + Eh * s[3], R(N))
    Ym = pm(D * s[4] + Eh * s[5], R(N))
    return [nu, Y, Ym, D] + Forcing(E)

# One bit-burst stage: from V(c) to V(c + delta)
def TaylorStage(c, delta, V, eps):
    U = arb(u0)
    rho = arb(abs(delta) / c)
    R = lambda L: 2 * (4 * U).exp() * rho ** L / (arb(c).sqrt() * (1 - rho))
    L = least(2, lambda L: R(L) <= eps)

    def T(j):
        h = -delta / (j + 1); e = j + half
        M = [[e / c, -1 / c, 0, 1 / c, 1 / c, 0, 0],
             [0, e / c, -4 / c, 0, 0, 1 / c, 0],
             [0, 1, 0, 0, 0, 0, 0],
             [0, 0, 0, e / c, 0, 0, 1 / c],
             [0, 0, 0, 0, 1 / u0, 0, 0],
             [0, 0, 0, 0, 0, 1 / u0, 0],
             [0, 0, 0, 0, 0, 0, 1 / u0]]
        return mat([[h * x for x in row] for row in M])
    W = lambda j: mat([[int(i == l) for l in range(7)] for i in range(4)])
    _, S = BinSplit(T, W, 0, L)
    E = (-arb(c + delta) / U).exp()
    return [pm(si, R(L)) for si in matvec(S, V)] + Forcing(E)

# The dual terms J_m
def DualTerm(m, eps):
    U = arb(u0)
    c = arb.pi() ** 2 * (m + arb(half)) ** 2
    trunc = lambda r: fmpq(int((c.mid() * 2 ** r).floor().unique_fmpz()),
                           2 ** r)
    cm = c.lower() - arb(2) ** (-r0)
    K0 = 2 * arb.pi().sqrt() * Eip(4 * U) * (-cm / U).exp() / (U.sqrt() * cm)
    x = ((K0 / (eps - K0 * c.rad())).log() / arb.const_log2()).upper()
    rstar = max(r0, int(x.ceil().unique_fmpz()))
    r = r0; cc = trunc(r)
    V = StartValues(cc, eps)
    while r < rstar:
        r = min(g * r, rstar)
        V = TaylorStage(cc, trunc(r) - cc, V, eps)
        cc = trunc(r)
    return pm(arb.pi().sqrt() * V[0], K0 * (arb(2) ** (-rstar) + c.rad()))

# Khinchin's constant
def Khinchin(p):
    ctx.prec = p + 30
    eps = arb(2) ** (-p - 10)
    U, pi = arb(u0), arb.pi()
    G = Eip(4 * U) / U
    tk = lambda k: (2 * (-((k + 1) ** 2 - 4) * U).exp()
                    / (((k + 1) ** 2 - 4) * U))
    tm = lambda m: (4 * (pi * U).sqrt() * G
                    * (-pi ** 2 * (m + 1 + arb(half)) ** 2 / U).exp())
    kmax = least(3, lambda k: tk(k) <= eps)
    mmax = least(0, lambda m: tm(m) <= eps)
    S = MainTerm(eps)
    for k in range(3, kmax + 1):
        S += (-1) ** k * KTerm(k, eps)
    for m in range(0, mmax + 1):
        S += DualTerm(m, eps)
    S = pm(S, tk(kmax) + tm(mmax))
    log2 = arb.const_log2()
    L0 = log2 ** 2 + arb(-half).polylog(2) + pi ** 2 / 12
    return ((L0 + S / 2) / log2).exp(), kmax, mmax

if __name__ == "__main__":
    p = int(sys.argv[1]) if len(sys.argv) > 1 else 333
    K, kmax, mmax = Khinchin(p)
    ref = arb.const_khinchin()
    print("p = %d  kmax = %d  mmax = %d" % (p, kmax, mmax))
    print("K =", K.str(30, radius=False), "...")
    print("|K - ref| = %s,  radius = %s,  contains ref: %s" % (
        (K - ref).mid().abs_upper().str(3, radius=False),
        K.rad().str(3, radius=False), K.overlaps(ref)))
