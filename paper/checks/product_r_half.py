# sum_{k>=k0} e^{-tau k^r} G(k) k^{-s} with r = 1/q, G(k) = f(1/k). Kernel exponents e = s + n - r j  (x^{-e}),
# grouped by m = q n - j:  e_m = s + m/q,  b_m = sum_{n>=0, j = q n - m >= 0} a_n (-tau)^j / j!.
from mpmath import mp, mpf, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, fsum, log
mp.dps = 32
q = 2; r = mpf(1)/q
s, tau, u0, k0 = mpf('0.3'), mpf(1), mpf(1)/4, 2
NA, NJ, K, NM = 110, 260, 19, 4
a = [mpf(0)] + [(-1)**(n+1) / mpf(n) for n in range(1, NA)]       # G(k) = log(1+1/k)
B = {}
for n in range(NA):
    for j in range(NJ):
        m = q*n - j
        B[m] = B.get(m, 0) + a[n] * (-tau)**j / factorial(j)
e = lambda m: s + mpf(m)/q
w = lambda m: e(m)/2
Q = lambda A, x: gammainc(A, x, inf, regularized=True)
Pl = lambda A, x: gammainc(A, 0, x, regularized=True)
D = lambda A, c: c**A * gammainc(-A, c/u0, inf)
I = lambda k, sel=lambda m: True: fsum(B[m] * mpf(k)**(-e(m)) * Q(w(m), k*k*u0) for m in B if sel(m))
J = lambda c: fsum(B[m] * rgamma(w(m)) * D(w(m) - mpf(1)/2, c) for m in B)
Mplus = fsum(B[m] * (sqrt(pi) * u0**(w(m)-mpf(1)/2) / (2*(w(m)-mpf(1)/2)) * rgamma(w(m)) - u0**w(m) * rgamma(w(m)+1) / 2
                     - fsum(mpf(k)**(-e(m)) * Pl(w(m), k*k*u0) for k in range(1, k0))) for m in B if m >= 0)
# Mellin of x^{-s} P(x), P(x) = sum_n a_n x^{-n} (e^{-tau x^r} - sum_{j <= q n} (-tau x^r)^j / j!):  sum_n a_n q Gamma(q(z-s-n)) tau^{-q(z-s-n)}
Mmel = lambda z: fsum(a[n] * q * gamma(q*(z-s-n)) * tau**(-q*(z-s-n)) for n in range(NA))
Ptail = lambda wx: fsum(-B[m] * rgamma(w(m)) * u0**(w(m)+wx-1) / (w(m)+wx-1) for m in B if m < 0)
Pk = lambda k: fsum(a[n] * mpf(k)**(-n) * (exp(-tau*mpf(k)**r) - fsum((-tau*mpf(k)**r)**j / factorial(j) for j in range(q*n+1))) for n in range(NA))
Mminus = sqrt(pi)/2 * (2*Mmel(1)/sqrt(pi) - Ptail(mpf(1)/2)) + Ptail(1)/2 \
         - fsum(mpf(k)**(-s) * Pk(k) - I(k, lambda m: m < 0) for k in range(1, k0))
total = fsum(I(k) for k in range(k0, K)) + sqrt(pi) * fsum(J(pi**2*m*m) for m in range(1, NM)) + Mplus + Mminus
ref = fsum(exp(-tau*sqrt(mpf(k))) * log(1 + mpf(1)/k) * mpf(k)**-s for k in range(k0, 12000))
print("split:", total); print("ref  :", ref); print("diff :", total - ref)
