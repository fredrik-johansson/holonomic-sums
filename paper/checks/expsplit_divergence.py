# Growth of the terms of the dual series J_m = sum_j c_j D_{a_j-1/2}(pi^2 m^2) of Prop. 4.2
# (a_j = (s - r j)/2, c_j = (-tau)^j/(j! Gamma(a_j))) and of the analogous series of Prop. 4.3 (q = 1).
# The j-th term is of size (tau (pi m)^{-r})^j Gamma(rj/2)^2/j!, i.e. (j!)^{r-1} times a geometric factor:
# convergent for r < 1, for r = 1 only when tau < 2 pi m, divergent for 1 < r < 2.
from mpmath import mp, mpf, rgamma, pi, factorial, gammainc, inf, fsum
mp.dps = 60
def D(b, c, u0): return c**b * gammainc(-b, c/u0, inf)       # int_0^u0 u^{b-1} e^{-c/u} du
def term(j, s, r, tau, u0, m):
    a = (s - r*j)/2
    return (-tau)**j / factorial(j) * rgamma(a) * D(a - mpf(1)/2, (pi*m)**2, u0)
s, u0 = mpf('3.3'), mpf(1)
for r, tau, js in [(mpf('0.5'), 1, (10, 40, 100)), (1, 1, (10, 40, 100)), (1, 8, (10, 40, 100)),
                   (mpf('1.5'), 1, (100, 400, 800))]:
    print("Prop 4.2  r =", r, " tau =", tau, " m = 1:",
          [(j, mp.nstr(abs(term(j, s, r, tau, u0, 1)), 3)) for j in js])
# Prop. 4.3, q = 1, f(t) = log(1+t): b_l = [t^l] f(t) e^{-tau/t}, w_l = (s+l)/2
s, u0, NA = mpf('0.3'), mpf(1)/4, 300
a = [mpf(0)] + [(-1)**(n+1) / mpf(n) for n in range(1, NA)]
for tau in (mpf(1), mpf(8)):
    b = lambda l: fsum(a[n] * (-tau)**(n - l) / factorial(n - l) for n in range(NA))
    w = lambda l: (s + l)/2
    print("Prop 4.3  q = 1, tau =", tau, " m = 1:",
          [(l, mp.nstr(abs(b(l) * rgamma(w(l)) * D(w(l) - mpf(1)/2, pi**2, u0)), 3)) for l in (-10, -40, -160)])
