Numerical checks (mpmath) of the splitting identities in Section 4 ("Damped functions") of zetaF.tex.
Each script sums every piece of the identity as a series and compares with an independent value.

| script | identity | agreement |
|---|---|---|
| geometric_complex_z.py | Thm. 4.1 (complex characteristic), sum_{k>=2} z^k log(1+1/k) k^{-0.3}, z = e^{-1+i theta}, theta = 0.6 pi and 0.01 | 41 / 40 digits |
| geometric_somos.py | Thm. 4.1 at z = 1/2 (dual point on the cut), log of Somos's constant | 41 digits |
| expsplit_pure.py | Prop. 4.2, Li_{0.3}(e^{-1}) (r = 1) and sum e^{-sqrt k} k^{-0.3} (r = 1/2) | 50 / 31 digits |
| polylog_complex_z.py | Li_{0.3}(z), z = e^{-1+0.6 pi i}, additive twist (Section 4.4) | 41 digits |
| lerch.py | Lerch Phi(e^{-1}, 0.3, 0.3), shifted lattice (Section 4.4) | 41 digits |
| product_r1.py | Prop. 4.3, sum_{k>=2} e^{-k} log(1+1/k) k^{-0.3} | 45 digits |
| product_r_half.py | Prop. 4.3 with q = 2, sum_{k>=2} e^{-sqrt k} log(1+1/k) k^{-0.3} | 33 digits (working precision) |
