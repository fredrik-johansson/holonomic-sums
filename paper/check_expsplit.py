# Theta splitting for sum_k exp(-tau k^r) k^{-s}, all pieces as convergent P-recursive series:
#   h(u) = sum_j c_j u^{a_j-1},  a_j = (s - r j)/2,  c_j = (-tau)^j / (j! Gamma(a_j))
from mpmath import mp, mpf, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, polylog, fsum
mp.dps = 50
def split(s, tau, r, u0, NJ=400, KMAX=40, MMAX=6, MF=None):
    a = lambda j: (s - r*j)/2
    c = lambda j: (-tau)**j * rgamma(a(j)) / factorial(j)
    I = lambda k: fsum((-tau)**j * mpf(k)**(r*j - s) / factorial(j) * gammainc(a(j), k*k*u0, inf, regularized=True)
                       for j in range(NJ))
    D = lambda b, cc: cc**b * gammainc(-b, cc/u0, inf)
    J = lambda m: fsum(c(j) * D(a(j) - mpf(1)/2, pi**2*m*m) for j in range(NJ))
    T = lambda w: fsum(c(j) * (-u0**(a(j)+w-1) / (a(j)+w-1)) for j in range(NJ))   # int_{u0}^inf u^{w-1} h
    M = sqrt(pi)/2 * (2*MF(1 - s)/sqrt(pi) - T(mpf(1)/2)) + T(1)/2
    return fsum(I(k) for k in range(1, KMAX)) + sqrt(pi)*fsum(J(m) for m in range(1, MMAX)) + M

s = mpf('0.3'); tau = mpf(1)
# r = 1: polylog;  M_F(z) = int x^{z-1} e^{-tau x} dx = Gamma(z) tau^{-z}
v = split(s, tau, 1, mpf(1)/4, MF=lambda z: gamma(z)*tau**-z)
print("r=1  :", v - polylog(s, exp(-tau)))
# r = 1/2: M_F(z) = 2 Gamma(2z) tau^{-2z};  reference by direct summation (slow but fine at 50 digits)
v = split(s, tau, mpf(1)/2, mpf(1)/4, MF=lambda z: 2*gamma(2*z)*tau**(-2*z))
mp.dps = 30
ref = fsum(exp(-sqrt(mpf(k))) * mpf(k)**-s for k in range(1, 20000))
print("r=1/2:", v - ref, " (direct sum needed 20000 terms)")
