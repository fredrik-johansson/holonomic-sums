/-
# Theta transformation with an odd periodic weight (Remark 3.7, `δ = 1`)

For `χ` odd of period `q`,
`∑_{k ∈ ℤ} χ(k) k e^{-k²u} = c₁ u^{-3/2} ∑_{n ∈ ℤ} χ̂(n) n e^{-π²n²/(q²u)}` with
`c₁ = -i π^{3/2} q^{-2}`.  The residue-class identity is obtained by differentiating the shifted
theta transformation in the shift, which is done for complex shifts so that the derivative of the
series can be taken termwise by `hasSum_deriv_of_summable_norm`.
-/
import ZetaF.Twisted.Theta

open Real Complex Finset Metric

namespace ZetaF

/-- The shifted theta transformation for a complex shift `b`. -/
theorem tsum_cexp_shifted_sq {q : ℕ} (hq : 0 < q) (b : ℂ) {u : ℝ} (hu : 0 < u) :
    ∑' j : ℤ, cexp (-((b + q * j) ^ 2 * u)) =
      (1 / q * √(π / u) : ℝ) * ∑' n : ℤ, cexp (2 * π * I * n * b / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have hπ := Real.pi_pos
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set A : ℂ := ((q ^ 2 * u / π : ℝ) : ℂ) with hA
  set B : ℂ := -(b * q * u / π) with hB
  have hAre : 0 < A.re := by rw [hA, Complex.ofReal_re]; positivity
  have key := Complex.tsum_exp_neg_quadratic hAre B
  have hE : cexp (b ^ 2 * u) ≠ 0 := Complex.exp_ne_zero _
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hπ.ne'
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have hL : ∀ j : ℤ, cexp (-π * A * j ^ 2 + 2 * π * B * j) =
      cexp (b ^ 2 * u) * cexp (-((b + q * j) ^ 2 * u)) := by
    intro j
    rw [← Complex.exp_add]
    congr 1
    rw [hA, hB]; push_cast; field_simp; ring
  have hR : ∀ n : ℤ, cexp (-π / A * (n + I * B) ^ 2) =
      cexp (b ^ 2 * u) * (cexp (2 * π * I * n * b / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ)) := by
    intro n
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hA, hB]; push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]; ring
  have hsq : (1 : ℂ) / A ^ (1 / 2 : ℂ) = ((1 / q * √(π / u) : ℝ) : ℂ) := by
    rw [hA, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow]
    rw [Real.sqrt_div' _ hπ.le, Real.sqrt_mul' _ hu.le, Real.sqrt_sq hq'.le,
      Real.sqrt_div' _ hu.le]
    push_cast
    have : (√π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hπ).ne'
    have : (√u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
    field_simp
  simp only [hL, hR, tsum_mul_left, hsq] at key
  rw [mul_left_comm] at key
  exact mul_left_cancel₀ hE key

/-- Uniform bound for the left-hand terms on `‖w‖ ≤ r`. -/
lemma norm_cexp_shifted_le {q : ℕ} {u : ℝ} (hu : 0 < u) {r : ℝ} {w : ℂ} (hw : ‖w‖ ≤ r) (j : ℤ) :
    ‖cexp (-((w + q * j) ^ 2 * u))‖ ≤
      rexp (2 * u * r ^ 2) * rexp (-(u * q ^ 2 / 2 * (j : ℝ) ^ 2)) := by
  rw [Complex.norm_exp, ← Real.exp_add, Real.exp_le_exp]
  have hre : (-((w + q * j) ^ 2 * u)).re = -u * ((w.re + q * j) ^ 2 - w.im ^ 2) := by
    simp [sq, Complex.mul_re, Complex.add_re]; ring
  rw [hre]
  have h1 : |w.re| ≤ r := (Complex.abs_re_le_norm w).trans hw
  have h2 : |w.im| ≤ r := (Complex.abs_im_le_norm w).trans hw
  have h1' : w.re ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs w.re]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h2' : w.im ^ 2 ≤ r ^ 2 := by
    rw [← sq_abs w.im]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have e1 := mul_nonneg hu.le (sq_nonneg (2 * w.re + q * j))
  have e2 := mul_nonneg hu.le (sub_nonneg.2 h1')
  have e3 := mul_nonneg hu.le (sub_nonneg.2 h2')
  nlinarith

/-- Uniform bound for the right-hand terms on `‖w‖ ≤ r`. -/
lemma norm_cexp_dual_le {q : ℕ} (hq : 0 < q) {u : ℝ} (hu : 0 < u) {r : ℝ} {w : ℂ} (hw : ‖w‖ ≤ r)
    (n : ℤ) :
    ‖cexp (2 * π * I * n * w / q) * (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ)‖ ≤
      rexp ((2 * π * r / q) ^ 2 / (2 * (π ^ 2 / (q ^ 2 * u)))) *
        rexp (-(π ^ 2 / (q ^ 2 * u) / 2 * (n : ℝ) ^ 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set d := π ^ 2 / (q ^ 2 * u) with hd
  have hd0 : 0 < d := by positivity
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  have hre : (2 * π * I * n * w / q).re = -(n * (2 * π * w.im / q)) := by
    simp [Complex.mul_re, Complex.div_re, Complex.mul_im]
    field_simp
  rw [hre, show π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u) = d * n ^ 2 by rw [hd]; ring]
  set y := 2 * π * w.im / q
  have hy : y ^ 2 ≤ (2 * π * r / q) ^ 2 := by
    have h2 : |w.im| ≤ r := (Complex.abs_im_le_norm w).trans hw
    have : |y| ≤ 2 * π * r / q := by
      simp only [y, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hq',
        abs_two]
      gcongr
    rw [← sq_abs y]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  have key : 0 ≤ d / 2 * n ^ 2 + n * y + (2 * π * r / q) ^ 2 / (2 * d) := by
    rw [show d / 2 * (n : ℝ) ^ 2 + n * y + (2 * π * r / q) ^ 2 / (2 * d) =
      ((d * n + y) ^ 2 + ((2 * π * r / q) ^ 2 - y ^ 2)) / (2 * d) by field_simp; ring]
    exact div_nonneg (add_nonneg (sq_nonneg _) (by linarith)) (by positivity)
  linarith

/-- **Differentiated shifted theta transformation**: for every complex `z`,
`∑_j (z + qj) e^{-(z+qj)²u} = (1/q)√(π/u) · (-πi/(qu)) ∑_n n e^{2πinz/q} e^{-π²n²/(q²u)}`. -/
theorem tsum_mul_cexp_shifted_sq {q : ℕ} (hq : 0 < q) (z : ℂ) {u : ℝ} (hu : 0 < u) :
    ∑' j : ℤ, (z + q * j) * cexp (-((z + q * j) ^ 2 * u)) =
      (1 / q * √(π / u) : ℝ) * (-(π * I) / (q * u)) * ∑' n : ℤ, n * cexp (2 * π * I * n * z / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hπ0 : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_pos.ne'
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  set U := ball z 1
  set r := ‖z‖ + 1
  have hUr : ∀ w ∈ U, ‖w‖ ≤ r := fun w hw => by
    have := norm_le_norm_add_norm_sub' w z  -- ‖w‖ ≤ ‖z‖ + ‖w - z‖
    rw [mem_ball, dist_eq_norm] at hw
    linarith
  set F : ℤ → ℂ → ℂ := fun j w => cexp (-((w + q * j) ^ 2 * u)) with hF
  set G : ℤ → ℂ → ℂ := fun n w => cexp (2 * π * I * n * w / q) *
    (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) with hG
  set C : ℂ := ((1 / q * √(π / u) : ℝ) : ℂ)
  have hFd : ∀ j w, HasDerivAt (F j) (cexp (-((w + q * j) ^ 2 * u)) * (-(2 * (w + q * j) * u))) w := by
    intro j w
    have := ((((hasDerivAt_id w).add_const ((q : ℂ) * j)).pow 2).mul_const (u : ℂ)).neg.cexp
    exact this.congr_deriv (by simp)
  have hGd : ∀ n w, HasDerivAt (G n) (cexp (2 * π * I * n * w / q) *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) * (2 * π * I * n / q)) w := by
    intro n w
    have := (((hasDerivAt_id w).const_mul (2 * π * I * n)).div_const (q : ℂ)).cexp.mul_const
      ((rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ))
    exact this.congr_deriv (by simp only [id, mul_one]; ring)
  have hFs := (summable_int_exp_neg_mul_sq (c := u * q ^ 2 / 2) (by positivity)).mul_left
    (rexp (2 * u * r ^ 2))
  have hGs := (summable_int_exp_neg_mul_sq (c := π ^ 2 / (q ^ 2 * u) / 2) (by positivity)).mul_left
    (rexp ((2 * π * r / q) ^ 2 / (2 * (π ^ 2 / (q ^ 2 * u)))))
  have hFdiff : ∀ j, DifferentiableOn ℂ (F j) U := fun j w _ => (hFd j w).differentiableAt.differentiableWithinAt
  have hGdiff : ∀ n, DifferentiableOn ℂ (G n) U := fun n w _ => (hGd n w).differentiableAt.differentiableWithinAt
  have hFle : ∀ j, ∀ w ∈ U, ‖F j w‖ ≤ rexp (2 * u * r ^ 2) * rexp (-(u * q ^ 2 / 2 * (j : ℝ) ^ 2)) :=
    fun j w hw => norm_cexp_shifted_le hu (hUr w hw) j
  have hGle : ∀ n, ∀ w ∈ U, ‖G n w‖ ≤ rexp ((2 * π * r / q) ^ 2 / (2 * (π ^ 2 / (q ^ 2 * u)))) *
      rexp (-(π ^ 2 / (q ^ 2 * u) / 2 * (n : ℝ) ^ 2)) :=
    fun n w hw => norm_cexp_dual_le hq hu (hUr w hw) n
  have hzU : z ∈ U := mem_ball_self one_pos
  have hLs := hasSum_deriv_of_summable_norm hFs hFdiff isOpen_ball hFle hzU
  have hRs := hasSum_deriv_of_summable_norm hGs hGdiff isOpen_ball hGle hzU
  have hRdiff : DifferentiableAt ℂ (fun w => ∑' n, G n w) z :=
    (differentiableOn_tsum_of_summable_norm hGs hGdiff isOpen_ball hGle).differentiableAt
      (isOpen_ball.mem_nhds hzU)
  have hfun : (fun w => ∑' j, F j w) = fun w => C * ∑' n, G n w :=
    funext fun w => tsum_cexp_shifted_sq hq w hu
  rw [hfun, deriv_const_mul _ hRdiff] at hLs
  simp only [fun j => (hFd j z).deriv, fun n => (hGd n z).deriv] at hLs hRs
  have h1 : ∑' j : ℤ, cexp (-((z + q * j) ^ 2 * u)) * (-(2 * (z + q * j) * u)) =
      (-(2 * u)) * ∑' j : ℤ, (z + q * j) * cexp (-((z + q * j) ^ 2 * u)) := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  have h2 : ∑' n : ℤ, cexp (2 * π * I * n * z / q) *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) * (2 * π * I * n / q) =
      (2 * π * I / q) * ∑' n : ℤ, n * cexp (2 * π * I * n * z / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
    rw [← tsum_mul_left]; congr 1; funext n; ring
  have hfin := hLs.tsum_eq
  rw [h1, ← hRs.tsum_eq, h2] at hfin
  have h2u : (-(2 * (u : ℂ))) ≠ 0 := by simpa using hu0
  apply mul_left_cancel₀ h2u
  rw [hfin]
  generalize (∑' n : ℤ, (n : ℂ) * cexp (2 * π * I * n * z / q) *
    (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ)) = S
  field_simp

/-- The real residue-class form: `∑_j (a+qj) e^{-(a+qj)²u}`. -/
theorem tsum_mul_exp_shifted_sq {q : ℕ} (hq : 0 < q) (a : ℝ) {u : ℝ} (hu : 0 < u) :
    ∑' j : ℤ, (((a + q * j) * rexp (-((a + q * j) ^ 2 * u)) : ℝ) : ℂ) =
      (1 / q * √(π / u) : ℝ) * (-(π * I) / (q * u)) * ∑' n : ℤ, n * cexp (2 * π * I * n * a / q) *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  rw [← tsum_mul_cexp_shifted_sq hq (a : ℂ) hu]
  congr 1; funext j
  push_cast [Complex.ofReal_exp]; rfl

/-- `|x| e^{-x²u} ≤ e^{-x²u/2}/√u`. -/
lemma abs_mul_exp_neg_sq_le (x : ℝ) {u : ℝ} (hu : 0 < u) :
    |x| * rexp (-(x ^ 2 * u)) ≤ rexp (-(u / 2 * x ^ 2)) / √u := by
  have hsu := Real.sqrt_pos.2 hu
  have hs2 : √u ^ 2 = u := Real.sq_sqrt hu.le
  have h1 : |x| * √u ≤ rexp (x ^ 2 * u / 2) := by
    have := Real.add_one_le_exp (x ^ 2 * u / 2)
    have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (|x| * √u - 1)]
  rw [le_div_iff₀ hsu]
  calc |x| * rexp (-(x ^ 2 * u)) * √u = (|x| * √u) * rexp (-(x ^ 2 * u)) := by ring
    _ ≤ rexp (x ^ 2 * u / 2) * rexp (-(x ^ 2 * u)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = rexp (-(u / 2 * x ^ 2)) := by rw [← Real.exp_add]; congr 1; ring

lemma summable_int_abs_mul_exp_neg_sq {u : ℝ} (hu : 0 < u) :
    Summable fun k : ℤ => |(k : ℝ)| * rexp (-((k : ℝ) ^ 2 * u)) :=
  Summable.of_nonneg_of_le (fun _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)
    (fun k => abs_mul_exp_neg_sq_le _ hu)
    ((summable_int_exp_neg_mul_sq (c := u / 2) (by positivity)).div_const _)

/-- **Theta transformation with an odd-type weight**:
`∑_{k∈ℤ} χ(k) k e^{-k²u} = (1/q)√(π/u)(-πi/(qu)) ∑_{n∈ℤ} n χ̂(n) e^{-π²n²/(q²u)}`
for any `q`-periodic `χ`. -/
theorem tsum_char_theta_odd {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    {u : ℝ} (hu : 0 < u) :
    ∑' k : ℤ, χ k * (((k : ℝ) * rexp (-((k : ℝ) ^ 2 * u)) : ℝ) : ℂ) =
      (1 / q * √(π / u) : ℝ) * (-(π * I) / (q * u)) * ∑' n : ℤ, n * gaussSum q χ n *
        (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
  have : NeZero q := ⟨hq.ne'⟩
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  set f : ℤ → ℂ := fun k => χ k * (((k : ℝ) * rexp (-((k : ℝ) ^ 2 * u)) : ℝ) : ℂ) with hf
  have hfs : Summable f := by
    refine Summable.of_norm_bounded ((summable_int_abs_mul_exp_neg_sq hu).mul_left
      (∑ a ∈ range q, ‖χ a‖)) fun k => ?_
    rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (by positivity)
  set e : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm with he
  have he_apply : ∀ p : Fin q × ℤ, e p = p.2 * q + p.1 := fun p => by
    simp [he, Int.divModEquiv]
  have h2 : Summable (f ∘ e) := e.summable_iff.2 hfs
  show ∑' k, f k = _
  rw [← e.tsum_eq f, show (fun c => f (e c)) = f ∘ e from rfl, h2.tsum_prod, tsum_fintype]
  set K : ℂ := ((1 / q * √(π / u) : ℝ) : ℂ) * (-(π * I) / (q * u))
  set G : ℤ → ℂ := fun n => (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) with hGdef
  have hrow : ∀ r : Fin q, ∑' j : ℤ, (f ∘ e) (r, j) = χ r * (K *
      ∑' n : ℤ, n * cexp (2 * π * I * n * ((r : ℕ) : ℝ) / q) * G n) := by
    intro r
    rw [← tsum_mul_exp_shifted_sq hq ((r : ℕ) : ℝ) hu, ← tsum_mul_left]
    congr 1; funext j
    rw [Function.comp_apply, he_apply, hf]
    simp only
    congr 1
    · have := hper.int_mul j ((r : ℕ) : ℤ)
      rw [show ((j * q + ((r : ℕ) : ℤ) : ℤ)) = ((r : ℕ) : ℤ) + j * q by ring]
      exact this
    · congr 1; push_cast; ring_nf
  simp only [hrow]
  rw [Fin.sum_univ_eq_sum_range (fun r => χ r * (K *
      ∑' n : ℤ, n * cexp (2 * π * I * n * (r : ℝ) / q) * G n)) q]
  have hd : (0 : ℝ) < π ^ 2 / (q ^ 2 * u) := by positivity
  have hS : ∀ r : ℕ, Summable fun n : ℤ => n * cexp (2 * π * I * n * (r : ℝ) / q) * G n := by
    intro r
    refine Summable.of_norm_bounded (Complex.summable_ofReal.2
      (summable_int_abs_mul_exp_neg_sq hd)).norm fun n => le_of_eq ?_
    rw [norm_mul, norm_mul,
      show 2 * π * I * n * (r : ℝ) / q = ((2 * π * n * r / q : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Complex.norm_real,
      Complex.norm_intCast, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    rw [abs_abs]; congr 3; ring
  have hsum := hasSum_sum (s := range q) fun r _ => ((hS r).hasSum.mul_left (χ r * K))
  calc ∑ r ∈ range q, χ r * (K * ∑' n : ℤ, n * cexp (2 * π * I * n * (r : ℝ) / q) * G n)
      = ∑ r ∈ range q, χ r * K * ∑' n : ℤ, n * cexp (2 * π * I * n * (r : ℝ) / q) * G n :=
        sum_congr rfl fun r _ => by ring
    _ = ∑' n : ℤ, ∑ r ∈ range q, χ r * K * (n * cexp (2 * π * I * n * (r : ℝ) / q) * G n) :=
        hsum.tsum_eq.symm
    _ = K * ∑' n : ℤ, n * gaussSum q χ n * G n := by
        rw [← tsum_mul_left]
        congr 1; funext n
        unfold gaussSum
        rw [Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
        exact sum_congr rfl fun r _ => by ring

/-- For odd `χ`, the Gauss sums are odd. -/
theorem gaussSum_neg_of_odd {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (hodd : ∀ k, χ (-k) = -χ k) (n : ℤ) : gaussSum q χ (-n) = -gaussSum q χ n := by
  set g : ℤ → ℂ := fun a => χ a * cexp (2 * π * I * (-n : ℤ) * (a : ℝ) / q) with hg
  have hgper : Function.Periodic g q := by
    intro a
    simp only [hg, hper a]
    congr 1
    have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    rw [show 2 * π * I * ((-n : ℤ) : ℂ) * (((a + q : ℤ) : ℝ) : ℂ) / q =
      2 * π * I * ((-n : ℤ) : ℂ) * ((a : ℝ) : ℂ) / q + ((-n : ℤ) : ℂ) * (2 * π * I) by
        push_cast; field_simp; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have := sum_range_periodic_neg hgper
  unfold gaussSum
  rw [← show ∑ a ∈ range q, g a = ∑ a ∈ range q, χ a * cexp (2 * π * I * (-n : ℤ) * (a : ℝ) / q)
    from sum_congr rfl fun a _ => by simp [hg]]
  rw [← this, ← Finset.sum_neg_distrib]
  refine sum_congr rfl fun a _ => ?_
  simp only [hg, hodd]
  rw [neg_mul]; congr 3; push_cast; ring

/-- The dual coefficients `c₁ m χ̂(m)` of an odd twist, `c₁ = -iπ^{3/2}q^{-2}`. -/
noncomputable def charDualOdd (q : ℕ) (χ : ℤ → ℂ) (m : ℕ) : ℂ :=
  -(I * ((π * √π / q ^ 2 : ℝ) : ℂ)) * m * gaussSum q χ m

/-- **Remark 3.7 (`δ = 1`), theta side**: for `χ` odd of period `q`,
`∑_{k ≥ 1} χ(k) k e^{-k²u} = u^{-3/2} ∑_{n ≥ 1} c₁ n χ̂(n) e^{-(π²/q²) n²/u}`. -/
theorem tsum_char_theta_odd_half {q : ℕ} (hq : 0 < q) {χ : ℤ → ℂ} (hper : Function.Periodic χ q)
    (hodd : ∀ k, χ (-k) = -χ k) {u : ℝ} (hu : 0 < u) :
    ∑' k : ℕ, χ ((k : ℤ) + 1) * ((k : ℂ) + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * ∑' n : ℕ, charDualOdd q χ (n + 1) *
        (rexp (-(π ^ 2 / q ^ 2 * ((n : ℝ) + 1) ^ 2 / u)) : ℂ) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hth := tsum_char_theta_odd hq hper hu
  set Bχ := ∑ a ∈ range q, ‖χ a‖
  have hsL : Summable fun k : ℤ => χ k * (((k : ℝ) * rexp (-((k : ℝ) ^ 2 * u)) : ℝ) : ℂ) := by
    refine Summable.of_norm_bounded ((summable_int_abs_mul_exp_neg_sq hu).mul_left Bχ) fun k => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_right (periodic_bound hq hper k) (by positivity)
  have hd : (0 : ℝ) < π ^ 2 / (q ^ 2 * u) := by positivity
  have hsR : Summable fun n : ℤ => (n : ℂ) * gaussSum q χ n *
      (rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
    refine Summable.of_norm_bounded ((summable_int_abs_mul_exp_neg_sq hd).mul_left Bχ) fun n => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_intCast,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    calc |(n : ℝ)| * ‖gaussSum q χ n‖ * rexp (-(π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u)))
        = ‖gaussSum q χ n‖ * (|(n : ℝ)| * rexp (-((n : ℝ) ^ 2 * (π ^ 2 / (q ^ 2 * u))))) := by
          rw [show (n : ℝ) ^ 2 * (π ^ 2 / (q ^ 2 * u)) = π ^ 2 * (n : ℝ) ^ 2 / (q ^ 2 * u) by
            ring]; ring
      _ ≤ Bχ * (|(n : ℝ)| * rexp (-((n : ℝ) ^ 2 * (π ^ 2 / (q ^ 2 * u))))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          unfold gaussSum
          refine (norm_sum_le _ _).trans (sum_le_sum fun a _ => ?_)
          rw [norm_mul]
          apply mul_le_of_le_one_right (norm_nonneg _) (le_of_eq _)
          rw [show 2 * π * I * (n : ℂ) * ((a : ℝ) : ℂ) / q = ((2 * π * n * a / q : ℝ) : ℂ) * I by
            push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
  rw [tsum_int_of_even_complex hsL (fun k => by simp [hodd]),
    tsum_int_of_even_complex hsR (fun n => by simp [gaussSum_neg_of_odd hq hper hodd])] at hth
  simp only [Int.cast_zero, Complex.ofReal_zero, zero_mul, mul_zero, zero_add] at hth
  have hK : ((1 / q * √(π / u) : ℝ) : ℂ) * (-(π * I) / (q * u)) =
      ((u ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * (-(I * ((π * √π / q ^ 2 : ℝ) : ℂ))) := by
    have h32 : u ^ (-(3 / 2 : ℝ)) = 1 / (√u * u) := by
      rw [show -(3 / 2 : ℝ) = -((1 / 2 : ℝ) + 1) by norm_num, Real.rpow_neg hu.le,
        Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow, one_div]
    rw [h32, Real.sqrt_div' _ hu.le]
    have hsu : (√u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hu).ne'
    have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
    have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
    push_cast
    field_simp
  rw [hK] at hth
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hL : ∑' k : ℕ, χ ((k : ℤ) + 1) * ((k : ℂ) + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      ∑' k : ℕ, χ ((k : ℤ) + 1) * (((((k : ℤ) + 1 : ℤ) : ℝ) *
        rexp (-((((k : ℤ) + 1 : ℤ) : ℝ) ^ 2 * u)) : ℝ) : ℂ) := by
    congr 1; funext k; push_cast; ring
  have hR : ∑' n : ℕ, charDualOdd q χ (n + 1) * (rexp (-(π ^ 2 / q ^ 2 * ((n : ℝ) + 1) ^ 2 / u)) : ℂ) =
      -(I * ((π * √π / q ^ 2 : ℝ) : ℂ)) * ∑' n : ℕ, ((((n : ℤ) + 1 : ℤ)) : ℂ) *
        gaussSum q χ ((n : ℤ) + 1) *
        (rexp (-(π ^ 2 * ((((n : ℤ) + 1 : ℤ)) : ℝ) ^ 2 / (q ^ 2 * u))) : ℂ) := by
    rw [← tsum_mul_left]; congr 1; funext n
    unfold charDualOdd
    rw [show π ^ 2 / q ^ 2 * ((n : ℝ) + 1) ^ 2 / u = π ^ 2 * ((((n : ℤ) + 1 : ℤ)) : ℝ) ^ 2 /
      (q ^ 2 * u) by push_cast; field_simp]
    push_cast; ring
  rw [hL, hR]
  linear_combination hth / 2

end ZetaF
