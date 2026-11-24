/-
# The estimate (G1) of Appendix A.9

For `x ≥ 1/2` and real `y`,  `|1/Γ(x+iy)| ≤ e^{π|y|/2}/Γ(x)`,
and `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`.  As in the paper:
`|Γ(x)/Γ(x+iy)|² = ∏_{n ≥ 0} (1 + y²/(x+n)²)` (from Euler's limit formula `GammaSeq → Γ`),
which decreases in `x` and equals `cosh πy` at `x = 1/2` (from the reflection formula).
-/
import ZetaF.Holonomic.GammaTwist

open Complex Filter Topology Finset
open scoped Real

namespace ZetaF

/-- The partial products `∏_{j ≤ n} (1 + y²/(x+j)²)`. -/
noncomputable def gProd (x y : ℝ) (n : ℕ) : ℝ := ∏ j ∈ range (n + 1), (1 + y ^ 2 / (x + j) ^ 2)

lemma gProd_anti {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) (n : ℕ) :
    gProd x' y n ≤ gProd x y n := by
  unfold gProd
  apply prod_le_prod₀ (fun j _ => by positivity)
  intro j _
  have h1 : 0 < x + j := by positivity
  have h2 : (x + j) ^ 2 ≤ (x' + j) ^ 2 := by nlinarith
  gcongr

lemma one_le_gProd (x y : ℝ) (n : ℕ) : 1 ≤ gProd x y n := by
  unfold gProd
  exact one_le_prod₀ (fun j _ => le_add_of_nonneg_right (by positivity))

lemma norm_sq_add_I (x y : ℝ) (j : ℕ) :
    ‖((x : ℂ) + y * I) + j‖ ^ 2 = (x + j) ^ 2 + y ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp; ring

/-- `‖GammaSeq x n‖² = gProd x y n · ‖GammaSeq (x+iy) n‖²` for `x > 0`, `n ≥ 1`. -/
lemma norm_GammaSeq_sq {x : ℝ} (hx : 0 < x) (y : ℝ) {n : ℕ} (hn : 0 < n) :
    ‖GammaSeq (x : ℂ) n‖ ^ 2 = gProd x y n * ‖GammaSeq ((x : ℂ) + y * I) n‖ ^ 2 := by
  unfold GammaSeq
  have hP : ∀ j : ℕ, 0 < x + j := fun j => by positivity
  have hQ : ∀ j : ℕ, 0 < ‖((x : ℂ) + y * I) + j‖ := fun j => norm_pos_iff.2 fun h => by
    have := congrArg Complex.re h; simp at this; linarith [hP j]
  rw [norm_div, norm_div, norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos hn,
    Complex.norm_natCast_cpow_of_pos hn, norm_prod, norm_prod]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero]
  have hPn : ∏ j ∈ range (n + 1), ‖(x : ℂ) + j‖ = ∏ j ∈ range (n + 1), (x + j) := by
    apply prod_congr rfl; intro j _
    rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (hP j).le]
  rw [hPn]
  have hPpos : 0 < ∏ j ∈ range (n + 1), (x + j) := prod_pos fun j _ => hP j
  have hQpos : 0 < ∏ j ∈ range (n + 1), ‖((x : ℂ) + y * I) + j‖ := prod_pos fun j _ => hQ j
  have hg : gProd x y n = (∏ j ∈ range (n + 1), ‖((x : ℂ) + y * I) + j‖) ^ 2 /
      (∏ j ∈ range (n + 1), (x + j)) ^ 2 := by
    unfold gProd
    rw [← prod_pow, ← prod_pow, ← prod_div_distrib]
    apply prod_congr rfl; intro j _
    rw [norm_sq_add_I]
    have := hP j
    field_simp
  rw [hg]
  field_simp

/-- `‖Γ(x)‖² / ‖Γ(x+iy)‖² = lim_n gProd x y n`. -/
lemma tendsto_gProd {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Tendsto (gProd x y) atTop (𝓝 (‖Gamma (x : ℂ)‖ ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2)) := by
  have hG : Gamma ((x : ℂ) + y * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx)
  have h1 := ((GammaSeq_tendsto_Gamma (x : ℂ)).norm.pow 2).div
    ((GammaSeq_tendsto_Gamma ((x : ℂ) + y * I)).norm.pow 2) (by simpa using hG)
  refine (tendsto_congr' ?_).1 h1
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hGS : ‖GammaSeq ((x : ℂ) + y * I) n‖ ^ 2 ≠ 0 := by
    have h := norm_GammaSeq_sq hx y hn
    intro h0
    rw [h0, mul_zero] at h
    have : GammaSeq (x : ℂ) n ≠ 0 := by
      unfold GammaSeq
      refine div_ne_zero (mul_ne_zero ?_ (by exact_mod_cast (Nat.factorial_pos n).ne')) ?_
      · exact (Complex.cpow_ne_zero_iff_of_exponent_ne_zero (by simpa using hx.ne')).2
          (by exact_mod_cast hn.ne')
      · exact prod_ne_zero_iff.2 fun j _ => by
          rw [show (x : ℂ) + j = ((x + j : ℝ) : ℂ) by push_cast; ring]
          exact_mod_cast (show 0 < x + j by positivity).ne'
    exact this (by simpa using h)
  show ‖GammaSeq (x : ℂ) n‖ ^ 2 / ‖GammaSeq ((x : ℂ) + y * I) n‖ ^ 2 = gProd x y n
  rw [norm_GammaSeq_sq hx y hn, mul_div_cancel_right₀ _ hGS]

/-- `|Γ(x)/Γ(x+iy)|²` decreases in `x > 0`. -/
lemma ratio_anti {x x' : ℝ} (hx : 0 < x) (hxx : x ≤ x') (y : ℝ) :
    ‖Gamma (x' : ℂ)‖ ^ 2 / ‖Gamma ((x' : ℂ) + y * I)‖ ^ 2 ≤
      ‖Gamma (x : ℂ)‖ ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 :=
  le_of_tendsto_of_tendsto' (tendsto_gProd (hx.trans_le hxx) y) (tendsto_gProd hx y)
    (gProd_anti hx hxx y)

/-- `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`. -/
theorem norm_Gamma_le_Gamma_re {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖Gamma ((x : ℂ) + y * I)‖ ≤ Real.Gamma x := by
  have hG : Gamma ((x : ℂ) + y * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx)
  have h1 : 1 ≤ ‖Gamma (x : ℂ)‖ ^ 2 / ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 :=
    ge_of_tendsto' (tendsto_gProd hx y) (one_le_gProd x y)
  have hpos : 0 < ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 := by positivity
  rw [le_div_iff₀ hpos, one_mul] at h1
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg
    (Real.Gamma_pos_of_pos hx).le] at h1
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.Gamma_pos_of_pos hx).le two_ne_zero).1 h1

/-- The value at `x = 1/2`: `|Γ(1/2)/Γ(1/2+iy)|² = cosh πy`. -/
lemma ratio_half (y : ℝ) :
    ‖Gamma ((1 / 2 : ℝ) : ℂ)‖ ^ 2 / ‖Gamma (((1 / 2 : ℝ) : ℂ) + y * I)‖ ^ 2 = Real.cosh (π * y) := by
  set z : ℂ := ((1 / 2 : ℝ) : ℂ) + y * I with hz
  have hconj : 1 - z = (starRingEnd ℂ) z := by
    rw [hz]; apply Complex.ext <;> simp; norm_num
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at hrefl
  have hsin : Complex.sin (π * z) = Real.cosh (π * y) := by
    rw [hz, show (π : ℂ) * (((1 / 2 : ℝ) : ℂ) + y * I) = π / 2 + ((π * y : ℝ) : ℂ) * I by
      push_cast; ring, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I, zero_mul, add_zero, one_mul, ← Complex.ofReal_cosh]
  rw [hsin] at hrefl
  have hnorm : ‖Gamma z‖ ^ 2 = π / Real.cosh (π * y) := by
    rw [Complex.sq_norm]
    have := congrArg Complex.re hrefl
    rw [Complex.ofReal_re] at this
    rw [this, ← Complex.ofReal_div, Complex.ofReal_re]
  have hhalf : ‖Gamma ((1 / 2 : ℝ) : ℂ)‖ ^ 2 = π := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.Gamma_one_half_eq, Real.norm_eq_abs,
      sq_abs, Real.sq_sqrt Real.pi_pos.le]
  rw [hhalf, hnorm]
  have hc : 0 < Real.cosh (π * y) := Real.cosh_pos _
  field_simp

lemma cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    have : Real.exp (-t) ≤ Real.exp t := Real.exp_le_exp.2 (by linarith)
    linarith
  · rw [abs_of_nonpos h]
    have : Real.exp t ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
    linarith

/-- **(G1)**: for `x ≥ 1/2`, `|1/Γ(x+iy)| ≤ e^{π|y|/2}/Γ(x)`. -/
theorem norm_inv_Gamma_le_G1 {x : ℝ} (hx : 1 / 2 ≤ x) (y : ℝ) :
    ‖(Gamma ((x : ℂ) + y * I))⁻¹‖ ≤ Real.exp (π * |y| / 2) / Real.Gamma x := by
  have hx0 : 0 < x := by linarith
  have hG : Gamma ((x : ℂ) + y * I) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using hx0)
  have hΓ := Real.Gamma_pos_of_pos hx0
  have h1 := (ratio_anti (by norm_num : (0 : ℝ) < 1 / 2) hx y).trans_eq (ratio_half y)
  have h2 := h1.trans (cosh_le_exp_abs _)
  rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg hΓ.le, abs_mul,
    abs_of_pos Real.pi_pos] at h2
  have hpos : 0 < ‖Gamma ((x : ℂ) + y * I)‖ := norm_pos_iff.2 hG
  rw [norm_inv, inv_eq_one_div, div_le_div_iff₀ hpos hΓ, one_mul]
  have h3 : Real.Gamma x ^ 2 ≤ Real.exp (π * |y|) * ‖Gamma ((x : ℂ) + y * I)‖ ^ 2 := by
    rwa [div_le_iff₀ (by positivity)] at h2
  have h4 : Real.exp (π * |y|) = Real.exp (π * |y| / 2) ^ 2 := by
    rw [← Real.exp_natCast_mul]; congr 1; push_cast; ring
  rw [h4, ← mul_pow] at h3
  exact (pow_le_pow_iff_left₀ hΓ.le (by positivity) two_ne_zero).1 h3

/-! ### (G2): an explicit bound for `1/Γ` on discs -/

/-- `Γ(x) ≥ 1/e` for `x ≥ 1`. -/
lemma realGamma_ge_exp_neg_one {x : ℝ} (hx : 1 ≤ x) : Real.exp (-1) ≤ Real.Gamma x := by
  have hx0 : 0 < x := by linarith
  rw [Real.Gamma_eq_integral hx0]
  have hint := Real.GammaIntegral_convergent hx0
  have hnn : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ Real.exp (-t) * t ^ (x - 1) := fun t ht =>
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
  calc Real.exp (-1) = ∫ t in Set.Ioi 1, Real.exp (-t) := (integral_exp_neg_Ioi 1).symm
    _ ≤ ∫ t in Set.Ioi 1, Real.exp (-t) * t ^ (x - 1) := by
        refine MeasureTheory.setIntegral_mono_on (integrableOn_exp_neg_Ioi 1)
          (hint.mono_set (Set.Ioi_subset_Ioi zero_le_one)) measurableSet_Ioi fun t ht => ?_
        exact le_mul_of_one_le_right (Real.exp_pos _).le
          (Real.one_le_rpow (le_of_lt ht) (by linarith))
    _ ≤ ∫ t in Set.Ioi 0, Real.exp (-t) * t ^ (x - 1) :=
        MeasureTheory.setIntegral_mono_set hint
          ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hnn))
          (Eventually.of_forall fun t ht => Set.Ioi_subset_Ioi zero_le_one ht)

/-- `1/Γ(w) = (w)_N / Γ(w+N)`. -/
lemma inv_Gamma_eq_prod_mul (w : ℂ) (N : ℕ) :
    (Gamma w)⁻¹ = (∏ j ∈ range N, (w + j)) * (Gamma (w + N))⁻¹ := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, prod_range_succ, ← ZetaF.mul_inv_Gamma_add_one (w + N)]
    push_cast; ring_nf

/-- **(G2)**, explicitly: if `|w| ≤ T` with `T ≥ 0`, then
`|1/Γ(w)| ≤ e · e^{πT/2} (2T+2)^{T+2}`, i.e. `e^{O(T log T)}`. -/
theorem norm_inv_Gamma_le_G2 {w : ℂ} {T : ℝ} (hT : 0 ≤ T) (hw : ‖w‖ ≤ T) :
    ‖(Gamma w)⁻¹‖ ≤ Real.exp 1 * Real.exp (π * T / 2) * (2 * T + 2) ^ (⌈T⌉₊ + 1) := by
  set N := ⌈T⌉₊ + 1 with hN
  have hTN : T ≤ ⌈T⌉₊ := Nat.le_ceil T
  have hNT : (N : ℝ) ≤ T + 2 := by
    have := Nat.ceil_lt_add_one hT; rw [hN]; push_cast; linarith
  have hre : 1 ≤ (w + N).re := by
    have := neg_le_of_abs_le ((Complex.abs_re_le_norm w).trans hw)
    simp [hN]; linarith
  rw [inv_Gamma_eq_prod_mul w N, norm_mul, norm_prod]
  have hprod : ∏ j ∈ range N, ‖w + j‖ ≤ (2 * T + 2) ^ N := by
    calc ∏ j ∈ range N, ‖w + j‖ ≤ ∏ _j ∈ range N, (2 * T + 2) := by
          apply prod_le_prod₀ (fun j _ => norm_nonneg _)
          intro j hj
          rw [mem_range] at hj
          have hj' : (j : ℝ) ≤ N := by exact_mod_cast hj.le
          calc ‖w + j‖ ≤ ‖w‖ + ‖(j : ℂ)‖ := norm_add_le _ _
            _ ≤ T + (T + 2) := by rw [Complex.norm_natCast]; linarith
            _ = 2 * T + 2 := by ring
      _ = (2 * T + 2) ^ N := by simp
  have hG1 : ‖(Gamma (w + N))⁻¹‖ ≤ Real.exp (π * T / 2) * Real.exp 1 := by
    have hw' : w + N = (((w + N).re : ℝ) : ℂ) + (((w + N).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    have h := norm_inv_Gamma_le_G1 (x := (w + N).re) (by linarith) (w + N).im
    rw [← hw'] at h
    have him : |(w + N).im| ≤ T := by
      simp; exact (Complex.abs_im_le_norm w).trans hw
    have hΓ := realGamma_ge_exp_neg_one hre
    refine h.trans ?_
    rw [div_le_iff₀ ((Real.exp_pos _).trans_le hΓ)]
    calc Real.exp (π * |(w + N).im| / 2) ≤ Real.exp (π * T / 2) := by
          rw [Real.exp_le_exp]; nlinarith [Real.pi_pos]
      _ = Real.exp (π * T / 2) * Real.exp 1 * Real.exp (-1) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hΓ (by positivity)
  calc (∏ j ∈ range N, ‖w + j‖) * ‖(Gamma (w + N))⁻¹‖
      ≤ (2 * T + 2) ^ N * (Real.exp (π * T / 2) * Real.exp 1) :=
        mul_le_mul hprod hG1 (norm_nonneg _) (by positivity)
    _ = _ := by ring

end ZetaF
