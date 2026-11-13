# Li_s(z), z = e^{-tau} e^{2 pi i alpha}: e^{-tau k} in the kernel, e^{2 pi i alpha k} as an additive twist.
from mpmath import mp, mpf, mpc, rgamma, gamma, exp, sqrt, pi, gammainc, inf, factorial, polylog, fsum, cos, sin, expjpi
mp.dps = 40
s, tau, alpha, u0 = mpf('0.3'), mpf(1), mpf('0.3'), mpf(1)/4
NJ, K, NN = 300, 40, 7
def coeffs(s):  # kernel of e^{-tau x} x^{-s}: sum_j c_j u^{a_j - 1}
    return [((s - j)/2, (-tau)**j * rgamma((s - j)/2) / factorial(j)) for j in range(NJ)]
def I(k, s):    # int_{u0}^inf e^{-k^2 u} h_s
    return fsum((-tau)**j * mpf(k)**(j - s) / factorial(j) * gammainc((s - j)/2, k*k*u0, inf, regularized=True) for j in range(NJ))
D = lambda b, c: c**b * gammainc(-b, c/u0, inf)
T = lambda s, w: fsum(-c * u0**(a + w - 1) / (a + w - 1) for a, c in coeffs(s))
cn = lambda n: pi**2 * (n - alpha)**2
even = fsum(cos(2*pi*alpha*k) * I(k, s) for k in range(1, K)) \
     + sqrt(pi)/2 * fsum(fsum(c * D(a - mpf(1)/2, cn(n)) for a, c in coeffs(s)) for n in range(-NN, NN + 1)) \
     + T(s, 1)/2
odd = fsum(sin(2*pi*alpha*k) * k * I(k, s + 1) for k in range(1, K)) \
     - pi**1.5/2 * fsum((n - alpha) * fsum(c * D(a - mpf(3)/2, cn(n)) for a, c in coeffs(s + 1)) for n in range(-NN, NN + 1))
z = exp(-tau) * exp(2j*pi*alpha)
print("split  :", even + 1j*odd)
print("polylog:", polylog(s, z))
print("diff   :", abs(even + 1j*odd - polylog(s, z)))
