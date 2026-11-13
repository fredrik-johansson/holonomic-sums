# Crandall-style: regular kernel of F(x) x^{-s} (paper), z^k = e^{2 pi i alpha k} with COMPLEX alpha,
# dual moments continued analytically to complex c_n = pi^2 (n - alpha)^2.
from mpmath import mp, mpf, mpc, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, fsum, log, cos, sin
mp.dps = 40
s, u0, k0 = mpf('0.3'), mpf(1)/4, 2
NA = 260
a = [mpf(0)] + [(-1)**(n+1) / mpf(n) for n in range(1, NA)]     # F(k) = log(1+1/k)
Q = lambda A, x: gammainc(A, x, inf, regularized=True)
P = lambda A, x: gammainc(A, 0, x, regularized=True)
D = lambda A, c: c**A * gammainc(-A, c/u0, inf)                 # analytic continuation in c (principal branch)
def I(k, w):  return fsum(a[n] * mpf(k)**(-w-n) * Q((w+n)/2, k*k*u0) for n in range(NA))
def Jd(c, w, delta): return fsum(a[n] * rgamma((w+n)/2) * D((w+n)/2 - mpf(1)/2 - delta, c) for n in range(NA))
def low(k, w): return fsum(a[n] * mpf(k)**(-w-n) * P((w+n)/2, k*k*u0) for n in range(NA))   # int_0^u0 e^{-k^2u} h_w
H0 = lambda w: fsum(a[n] * u0**((w+n)/2) * rgamma((w+n)/2 + 1) for n in range(NA))          # int_0^u0 h_w
def split(alpha, K=30, N=8):
    cn = lambda n: pi**2 * (n - alpha)**2
    even = fsum(cos(2*pi*alpha*k) * I(k, s) for k in range(k0, K)) \
         + sqrt(pi)/2 * fsum(Jd(cn(n), s, 0) for n in range(-N, N+1)) - H0(s)/2 \
         - fsum(cos(2*pi*alpha*k) * low(k, s) for k in range(1, k0))
    odd = fsum(sin(2*pi*alpha*k) * k * I(k, s+1) for k in range(k0, K)) \
        - pi**1.5/2 * fsum((n - alpha) * Jd(cn(n), s+1, 1) for n in range(-N, N+1)) \
        - fsum(sin(2*pi*alpha*k) * k * low(k, s+1) for k in range(1, k0))
    return even + 1j*odd
direct = lambda z: fsum(z**k * log(1 + mpf(1)/k) * mpf(k)**-s for k in range(k0, 400))
tau = mpf(1)
for th in (mpf('0.6')*pi, mpf('0.01')):
    alpha = th/(2*pi) + 1j*tau/(2*pi)
    z = exp(-tau + 1j*th)
    v = split(alpha); r = direct(z)
    print("theta=%s  |split-direct| = %s" % (mp.nstr(th, 4), mp.nstr(abs(v - r), 3)))
