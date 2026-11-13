# sum_{k>=k0} e^{-tau k} G(k) k^{-s},  G(k) = f(1/k), f(t) = sum a_n t^n analytic for |t| < 1/R, k0 > R.
# Kernel: h(u) = sum_{m in Z} b_m u^{w_m - 1}/Gamma(w_m), w_m = (s+m)/2, b_m = [t^m] f(t) e^{-tau/t} (Laurent).
# Split h = h_+ (m >= 0) + h_- (m < 0).  h_- is the kernel of x^{-s} P(x), P(x) = sum_n a_n x^{-n}(e^{-tau x} - e_{n+1}(-tau x)),
# whose Mellin transform is int_0^inf x^{z-1} x^{-s} P(x) dx = sum_n a_n tau^{s+n-z} Gamma(z-s-n).
import sys
from mpmath import mp, mpf, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, fsum, log
mp.dps = 45
s, tau, u0, k0 = mpf('0.3'), mpf(1), mpf(1)/4, 2
NA, MP, MN, K, NM = 400, 160, 120, 45, 6
a = [mpf(0)] + [(-1)**(n+1) / mpf(n) for n in range(1, NA)]        # f(t) = log(1+t), R = 1
def b(m):
    if m >= 1:
        return fsum(a[m+j] * (-tau)**j / factorial(j) for j in range(NA - m))
    return fsum(a[n] * (-tau)**(n - m) / factorial(n - m) for n in range(0, NA))
B = {m: b(m) for m in range(-MN, MP)}
w = lambda m: (s + m)/2
Q = lambda A, x: gammainc(A, x, inf, regularized=True)
P_ = lambda A, x: gammainc(A, 0, x, regularized=True)
D = lambda A, c: c**A * gammainc(-A, c/u0, inf)
def I(k):   # int_{u0}^inf e^{-k^2 u} h
    return fsum(B[m] * mpf(k)**(-s-m) * Q(w(m), k*k*u0) for m in B)
def J(c):   # int_0^{u0} u^{-1/2} e^{-c/u} h
    return fsum(B[m] * rgamma(w(m)) * D(w(m) - mpf(1)/2, c) for m in B)
# main term M = int_0^{u0} (sqrt(pi/u)/2 - 1/2 - sum_{1<=k<k0} e^{-k^2 u}) h du
Mplus = fsum(B[m] * (sqrt(pi) * u0**(w(m)-mpf(1)/2) / (2*(w(m)-mpf(1)/2)) * rgamma(w(m))
                     - u0**w(m) * rgamma(w(m)+1) / 2
                     - fsum(mpf(k)**(-s-m) * P_(w(m), k*k*u0) for k in range(1, k0)))
             for m in B if m >= 0)
Mmel = lambda z: fsum(a[n] * tau**(s+n-z) * gamma(z-s-n) for n in range(NA))          # Mellin of x^{-s} P(x)
Ptail = lambda wexp: fsum(-B[m] * rgamma(w(m)) * u0**(w(m)+wexp-1) / (w(m)+wexp-1) for m in B if m < 0)  # int_{u0}^inf u^{wexp-1} h_-
Pk = lambda k: fsum(a[n] * mpf(k)**(-n) * (exp(-tau*k) - fsum((-tau*k)**i / factorial(i) for i in range(n+1))) for n in range(NA))
Lminus = lambda k: fsum(B[m] * mpf(k)**(-s-m) * Q(w(m), k*k*u0) for m in B if m < 0)
Mminus = sqrt(pi)/2 * (2*Mmel(1)/sqrt(pi) - Ptail(mpf(1)/2)) - mpf(1)/2 * (0 - Ptail(1)) \
         - fsum(mpf(k)**(-s) * Pk(k) - Lminus(k) for k in range(1, k0))
total = fsum(I(k) for k in range(k0, K)) + sqrt(pi) * fsum(J(pi**2*m*m) for m in range(1, NM)) + Mplus + Mminus
ref = fsum(exp(-tau*k) * log(1 + mpf(1)/k) * mpf(k)**-s for k in range(k0, 200))
print("split:", total); print("ref  :", ref); print("diff :", total - ref)
print("b_m samples:", [mp.nstr(B[m], 5) for m in (-20, -5, -1, 0, 1, 5, 20, 100)])
