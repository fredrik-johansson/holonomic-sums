# Lerch Phi(z,s,a) = sum_{k>=0} z^k (k+a)^{-s}, z = e^{-tau}: summand e^{tau a} psi(k+a), psi(y) = e^{-tau y} y^{-s};
# Poisson over the shifted lattice n + a, one-sided sum = (even + odd)/2.
from mpmath import mp, mpf, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, fsum, cos, sin, lerchphi
mp.dps = 40
s, tau, a, u0 = mpf('0.3'), mpf(1), mpf('0.3'), mpf(1)/4
NJ, NK, NM = 300, 40, 6
coeffs = lambda s: [((s - j)/2, (-tau)**j * rgamma((s - j)/2) / factorial(j)) for j in range(NJ)]
def I(y, s):  # int_{u0}^inf e^{-y^2 u} h_s(u) du
    return fsum((-tau)**j * y**(j - s) / factorial(j) * gammainc((s - j)/2, y*y*u0, inf, regularized=True) for j in range(NJ))
D = lambda b, c: c**b * gammainc(-b, c/u0, inf)
T = lambda s, w: fsum(-c * u0**(b + w - 1) / (b + w - 1) for b, c in coeffs(s))
Jm = lambda s, c, shift: fsum(cc * D(b - shift, c) for b, cc in coeffs(s))
ksum = fsum(I(abs(n + a), s)/2 + (n + a) * I(abs(n + a), s + 1)/2 for n in range(-NK, NK))
even0 = gamma(1 - s) * tau**(s - 1) - sqrt(pi)/2 * T(s, mpf(1)/2)          # m = 0 term of the even part
evenm = sqrt(pi) * fsum(cos(2*pi*m*a) * Jm(s, pi**2*m*m, mpf(1)/2) for m in range(1, NM))
oddm = pi**1.5 * fsum(m * sin(2*pi*m*a) * Jm(s + 1, pi**2*m*m, mpf(3)/2) for m in range(1, NM))
val = exp(tau*a) * (ksum + even0 + evenm + oddm)
ref = lerchphi(exp(-tau), s, a)
print("split :", val); print("lerch :", ref); print("diff  :", val - ref)
