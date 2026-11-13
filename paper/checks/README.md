Numerical checks (mpmath) of the splitting identities in Section 4 ("Beyond regularity at infinity").
Each script sums every piece of the identity as a series and compares with an independent value.

| script | identity | agreement |
|---|---|---|
| expsplit_pure.py | Prop. 4.1, Li_{0.3}(e^{-1}) (r = 1) and sum e^{-sqrt k} k^{-0.3} (r = 1/2) | 50 / 31 digits |
| polylog_complex_z.py | Li_{0.3}(z), z = e^{-1+0.6 pi i}, additive twist (Section 4.3) | 41 digits |
| lerch.py | Lerch Phi(e^{-1}, 0.3, 0.3), shifted lattice (Section 4.3) | 41 digits |
| product_r1.py | Prop. 4.2, sum_{k>=2} e^{-k} log(1+1/k) k^{-0.3} | 45 digits |
| product_r_half.py | Prop. 4.2 with q = 2, sum_{k>=2} e^{-sqrt k} log(1+1/k) k^{-0.3} | 33 digits (working precision) |
