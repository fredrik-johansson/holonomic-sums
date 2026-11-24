/-
# Dual moments and the integration-by-parts recurrence (11)

Paper §3.4: for `c > 0`, `Z_t[g](c) = ∫₀^{u₀} u^{-t} e^{-c/u} g(u) du` and, with `E = e^{-c/u₀}`,
`c Z_{t+1}[g] = E u₀^{1-t} g(u₀) - (1-t) Z_t[g] - Z_t[θ g]`          (11)
`Z_t[u^j g] = Z_{t-j}[g]`,  `c C_{t+1} = E u₀^{1-t} - (1-t) C_t`  (`C_t = Z_t[1]`),
`a D_a + c D_{a-1} = E u₀^a`  (`D_a = Z_{1-a}[1]`)                 (14)

We use the weight `w_t(u) = u^{-t} e^{-c/u}` for `u > 0`, extended by `0` for `u ≤ 0`; it is continuous on
all of `ℝ` (for `c > 0`), which makes the boundary term at `0` vanish without any limiting argument.
-/
import ZetaF.Deps

open MeasureTheory Set Filter Topology
open scoped Real

namespace ZetaF

/-- The weight `w_t(u) = u^{-t} e^{-c/u}` (`u > 0`), `0` for `u ≤ 0`. -/
noncomputable def dualWeight (c : ℝ) (t : ℂ) (u : ℝ) : ℂ :=
  if 0 < u then (u : ℂ) ^ (-t) * (rexp (-(c / u)) : ℂ) else 0

/-- The dual moment `Z_t[g](c) = ∫₀^{u₀} u^{-t} e^{-c/u} g(u) du`. -/
noncomputable def dualMoment (u₀ c : ℝ) (t : ℂ) (g : ℝ → ℂ) : ℂ :=
  ∫ u in (0 : ℝ)..u₀, dualWeight c t u * g u

lemma dualWeight_of_pos {c : ℝ} {t : ℂ} {u : ℝ} (hu : 0 < u) :
    dualWeight c t u = (u : ℂ) ^ (-t) * (rexp (-(c / u)) : ℂ) := if_pos hu

lemma norm_dualWeight_of_pos {c : ℝ} {t : ℂ} {u : ℝ} (hu : 0 < u) :
    ‖dualWeight c t u‖ = u⁻¹ ^ t.re * rexp (-c * u⁻¹) := by
  rw [dualWeight_of_pos hu, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, Complex.neg_re, Real.rpow_neg hu.le,
    Real.inv_rpow hu.le]
  congr 2; ring

lemma tendsto_dualWeight_zero {c : ℝ} (hc : 0 < c) (t : ℂ) :
    Tendsto (dualWeight c t) (𝓝 0) (𝓝 0) := by
  rw [← nhdsLE_sup_nhdsGT, tendsto_sup]
  constructor
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    simp only [mem_Iic] at hu
    rw [dualWeight, if_neg (not_lt.2 hu)]
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero t.re c hc).comp tendsto_inv_nhdsGT_zero
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    rw [Function.comp_apply, norm_dualWeight_of_pos hu]

lemma hasDerivAt_dualWeight {c : ℝ} (t : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (dualWeight c t) (dualWeight c t u * (-t / u + c / u ^ 2)) u := by
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-t)) (-t * (u : ℂ) ^ (-t - 1)) u := by
    have := ((hasDerivAt_id (u : ℂ)).cpow_const (c := -t)
      (Complex.ofReal_mem_slitPlane.2 hu)).comp_ofReal
    simpa using this
  have h2 : HasDerivAt (fun y : ℝ => (rexp (-(c / y)) : ℂ)) (rexp (-(c / u)) * (c / u ^ 2) : ℝ) u := by
    apply HasDerivAt.ofReal_comp
    have := ((hasDerivAt_inv hu.ne').const_mul c).neg.exp
    convert this using 1
    · funext y; simp [div_eq_mul_inv]
    · simp only [Pi.neg_apply]; field_simp
  have h4 : HasDerivAt (dualWeight c t) _ u := (h1.mul h2).congr_of_eventuallyEq
    (by filter_upwards [lt_mem_nhds hu] with y hy; exact dualWeight_of_pos hy)
  convert h4 using 1
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  rw [dualWeight_of_pos hu, Complex.cpow_sub _ _ hu', Complex.cpow_one]
  push_cast
  field_simp

lemma continuous_dualWeight {c : ℝ} (hc : 0 < c) (t : ℂ) : Continuous (dualWeight c t) := by
  rw [continuous_iff_continuousAt]
  intro u
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [gt_mem_nhds hu] with y hy
    rw [dualWeight, if_neg (not_lt.2 hy.le)]
  · have h0 : dualWeight c t 0 = 0 := by simp [dualWeight]
    rw [ContinuousAt, h0]; exact tendsto_dualWeight_zero hc t
  · exact (hasDerivAt_dualWeight t hu).continuousAt

lemma dualWeight_add_one {c : ℝ} (t : ℂ) {u : ℝ} (hu : 0 < u) :
    dualWeight c (t + 1) u = dualWeight c t u / u := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  rw [dualWeight_of_pos hu, dualWeight_of_pos hu, neg_add, Complex.cpow_add _ _ hu',
    Complex.cpow_neg_one]
  field_simp

lemma dualWeight_sub_nat {c : ℝ} (t : ℂ) (j : ℕ) {u : ℝ} (hu : 0 < u) :
    dualWeight c (t - j) u = dualWeight c t u * (u : ℂ) ^ j := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  rw [dualWeight_of_pos hu, dualWeight_of_pos hu, neg_sub, sub_eq_add_neg, add_comm,
    Complex.cpow_add _ _ hu', Complex.cpow_natCast]
  ring

/-- `Z_t[u^j g] = Z_{t-j}[g]`. -/
lemma dualMoment_mul_pow (u₀ c : ℝ) (t : ℂ) (j : ℕ) (g : ℝ → ℂ) (hu₀ : 0 ≤ u₀) :
    dualMoment u₀ c t (fun u => (u : ℂ) ^ j * g u) = dualMoment u₀ c (t - j) g := by
  unfold dualMoment
  rw [intervalIntegral.integral_of_le hu₀, intervalIntegral.integral_of_le hu₀]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  simp only
  rw [dualWeight_sub_nat t j hu.1]; ring

/-- **The integration-by-parts recurrence (11).**  For `c, u₀ > 0` and `g` of class `C¹` on
`[0, u₀]`, with `E = e^{-c/u₀}` and `θ g = u g'`:
`c Z_{t+1}[g] = E u₀^{1-t} g(u₀) - (1-t) Z_t[g] - Z_t[θ g]`. -/
theorem dualMoment_ibp {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) {g g' : ℝ → ℂ}
    (hg : ∀ u ∈ Icc 0 u₀, HasDerivAt g (g' u) u) (hg' : ContinuousOn g' (Icc 0 u₀)) :
    c * dualMoment u₀ c (t + 1) g =
      (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * g u₀ - (1 - t) * dualMoment u₀ c t g -
        dualMoment u₀ c t (fun u => u * g' u) := by
  have hgc : ContinuousOn g (Icc 0 u₀) := fun u hu => (hg u hu).continuousAt.continuousWithinAt
  have hw := continuous_dualWeight hc t
  have hw1 := continuous_dualWeight hc (t + 1)
  set F : ℝ → ℂ := fun u => (u : ℂ) * dualWeight c t u * g u with hF
  set F' : ℝ → ℂ := fun u => (1 - t) * (dualWeight c t u * g u) +
    c * (dualWeight c (t + 1) u * g u) + dualWeight c t u * (u * g' u) with hF'
  have hderiv : ∀ u ∈ Ioo 0 u₀, HasDerivAt F (F' u) u := by
    intro u hu
    have h1 := ((Complex.ofRealCLM.hasDerivAt (x := u)).mul (hasDerivAt_dualWeight (c := c) t hu.1)).mul
      (hg u (Ioo_subset_Icc_self hu))
    convert h1 using 1
    · funext v; simp only [hF, Pi.mul_apply, Complex.ofRealCLM_apply]
    · have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.1.ne'
      rw [show F' u = (1 - t) * (dualWeight c t u * g u) + c * (dualWeight c (t + 1) u * g u) +
        dualWeight c t u * (u * g' u) from rfl, dualWeight_add_one t hu.1]
      simp only [Complex.ofRealCLM_apply, Pi.mul_apply, Complex.ofReal_one]
      field_simp
      ring
  have hcontF : ContinuousOn F (Icc 0 u₀) :=
    ((Complex.continuous_ofReal.mul hw).continuousOn).mul hgc
  have hI : ∀ {f : ℝ → ℂ}, ContinuousOn f (Icc 0 u₀) → IntervalIntegrable f volume 0 u₀ :=
    fun hf => (hf.mono (by rw [uIcc_of_le hu₀.le])).intervalIntegrable
  have i1 : IntervalIntegrable (fun u => dualWeight c t u * g u) volume 0 u₀ :=
    hI (hw.continuousOn.mul hgc)
  have i2 : IntervalIntegrable (fun u => dualWeight c (t + 1) u * g u) volume 0 u₀ :=
    hI (hw1.continuousOn.mul hgc)
  have i3 : IntervalIntegrable (fun u => dualWeight c t u * (u * g' u)) volume 0 u₀ :=
    hI (hw.continuousOn.mul (Complex.continuous_ofReal.continuousOn.mul hg'))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu₀.le hcontF hderiv
    (((i1.const_mul _).add (i2.const_mul _)).add i3)
  rw [intervalIntegral.integral_add ((i1.const_mul _).add (i2.const_mul _)) i3,
    intervalIntegral.integral_add (i1.const_mul _) (i2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  have hF0 : F 0 = 0 := by simp [hF]
  have hFu₀ : F u₀ = (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * g u₀ := by
    have hu' : (u₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu₀.ne'
    simp only [hF, dualWeight_of_pos hu₀]
    rw [sub_eq_add_neg, Complex.cpow_add _ _ hu', Complex.cpow_one]; ring
  rw [hF0, sub_zero, hFu₀] at hftc
  unfold dualMoment
  rw [← hftc]; ring

/-- `C_t = Z_t[1]` satisfies `c C_{t+1} = E u₀^{1-t} - (1-t) C_t`. -/
theorem dualMoment_one_rec {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) :
    c * dualMoment u₀ c (t + 1) (fun _ => 1) =
      (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) - (1 - t) * dualMoment u₀ c t (fun _ => 1) := by
  have := dualMoment_ibp hc hu₀ t (g := fun _ => (1 : ℂ)) (g' := fun _ => 0)
    (fun u _ => hasDerivAt_const u 1) continuousOn_const
  rw [this]
  have h0 : dualMoment u₀ c t (fun u => (u : ℂ) * 0) = 0 := by simp [dualMoment]
  rw [h0]; ring

/-- `D_a = ∫₀^{u₀} u^{a-1} e^{-c/u} du = Z_{1-a}[1]`. -/
noncomputable def momentD (u₀ c : ℝ) (a : ℂ) : ℂ := dualMoment u₀ c (1 - a) fun _ => 1

/-- **Recurrence (14)**: `a D_a + c D_{a-1} = E u₀^a`. -/
theorem momentD_rec {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (a : ℂ) :
    a * momentD u₀ c a + c * momentD u₀ c (a - 1) = (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ a := by
  have := dualMoment_one_rec hc hu₀ (1 - a)
  unfold momentD
  rw [show (1 - (a - 1) : ℂ) = 1 - a + 1 by ring, this, show (1 - (1 - a) : ℂ) = a by ring]
  ring

/-! ### Linearity and the row recurrence of Proposition 3.6 -/

section linearity

variable {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀)
include hc hu₀

lemma intervalIntegrable_dualWeight_mul (t : ℂ) {g : ℝ → ℂ} (hg : ContinuousOn g (Icc 0 u₀)) :
    IntervalIntegrable (fun u => dualWeight c t u * g u) volume 0 u₀ :=
  (((continuous_dualWeight hc t).continuousOn.mul hg).mono
    (by rw [uIcc_of_le hu₀.le])).intervalIntegrable

lemma dualMoment_add (t : ℂ) {g₁ g₂ : ℝ → ℂ} (h₁ : ContinuousOn g₁ (Icc 0 u₀))
    (h₂ : ContinuousOn g₂ (Icc 0 u₀)) :
    dualMoment u₀ c t (fun u => g₁ u + g₂ u) = dualMoment u₀ c t g₁ + dualMoment u₀ c t g₂ := by
  unfold dualMoment
  simp_rw [mul_add]
  exact intervalIntegral.integral_add (intervalIntegrable_dualWeight_mul hc hu₀ t h₁)
    (intervalIntegrable_dualWeight_mul hc hu₀ t h₂)

lemma dualMoment_finsetSum (t : ℂ) {ι : Type*} (S : Finset ι) {g : ι → ℝ → ℂ}
    (hg : ∀ i ∈ S, ContinuousOn (g i) (Icc 0 u₀)) :
    dualMoment u₀ c t (fun u => ∑ i ∈ S, g i u) = ∑ i ∈ S, dualMoment u₀ c t (g i) := by
  unfold dualMoment
  simp_rw [Finset.mul_sum]
  exact intervalIntegral.integral_finsetSum fun i hi =>
    intervalIntegrable_dualWeight_mul hc hu₀ t (hg i hi)

end linearity

lemma dualMoment_const_mul (u₀ c : ℝ) (t a : ℂ) (g : ℝ → ℂ) :
    dualMoment u₀ c t (fun u => a * g u) = a * dualMoment u₀ c t g := by
  unfold dualMoment
  simp_rw [mul_left_comm _ a]
  exact intervalIntegral.integral_const_mul a _

lemma dualMoment_congr {u₀ c : ℝ} (hu₀ : 0 ≤ u₀) (t : ℂ) {g₁ g₂ : ℝ → ℂ}
    (h : EqOn g₁ g₂ (Ioc 0 u₀)) : dualMoment u₀ c t g₁ = dualMoment u₀ c t g₂ := by
  unfold dualMoment
  rw [intervalIntegral.integral_of_le hu₀, intervalIntegral.integral_of_le hu₀]
  exact setIntegral_congr_fun measurableSet_Ioc fun u hu => by simp only [h hu]

/-- **Proposition 3.6, row recurrence.**  Let `𝐆 = (G_r)` satisfy the system (10)
`θ 𝐆 = A(u) 𝐆 + b(u)`, `A = ∑_{i ≤ d} A_i u^i`, `b = ∑_{i ≤ e} b_i u^i`.  Then, with
`W_t = Z_t[𝐆]` and `C_t = Z_t[1]`,
`c W_{t+1} = E u₀^{1-t} 𝐆(u₀) - (1-t) W_t - ∑_i A_i W_{t-i} - ∑_i b_i C_{t-i}`. -/
theorem dualMoment_system_rec {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) {ℓ d e : ℕ}
    (A : Fin (d + 1) → Matrix (Fin ℓ) (Fin ℓ) ℂ) (b : Fin (e + 1) → Fin ℓ → ℂ)
    {G G' : Fin ℓ → ℝ → ℂ} (hG : ∀ q, ∀ u ∈ Icc 0 u₀, HasDerivAt (G q) (G' q u) u)
    (hG' : ∀ q, ContinuousOn (G' q) (Icc 0 u₀))
    (hsys : ∀ q, ∀ u ∈ Icc 0 u₀, (u : ℂ) * G' q u =
      ∑ i : Fin (d + 1), ∑ p : Fin ℓ, A i q p * ((u : ℂ) ^ (i : ℕ) * G p u) +
        ∑ i : Fin (e + 1), b i q * (u : ℂ) ^ (i : ℕ))
    (q : Fin ℓ) :
    c * dualMoment u₀ c (t + 1) (G q) =
      (rexp (-(c / u₀)) : ℂ) * (u₀ : ℂ) ^ (1 - t) * G q u₀ - (1 - t) * dualMoment u₀ c t (G q) -
        ∑ i : Fin (d + 1), ∑ p : Fin ℓ, A i q p * dualMoment u₀ c (t - (i : ℕ)) (G p) -
        ∑ i : Fin (e + 1), b i q * dualMoment u₀ c (t - (i : ℕ)) (fun _ => 1) := by
  have hGc : ∀ p, ContinuousOn (G p) (Icc 0 u₀) := fun p u hu =>
    (hG p u hu).continuousAt.continuousWithinAt
  have hpow : ∀ i : ℕ, ContinuousOn (fun u : ℝ => (u : ℂ) ^ i) (Icc 0 u₀) := fun i =>
    (Complex.continuous_ofReal.pow i).continuousOn
  rw [dualMoment_ibp hc hu₀ t (hG q) (hG' q)]
  have h1 : dualMoment u₀ c t (fun u => (u : ℂ) * G' q u) =
      ∑ i : Fin (d + 1), ∑ p : Fin ℓ, A i q p * dualMoment u₀ c (t - (i : ℕ)) (G p) +
        ∑ i : Fin (e + 1), b i q * dualMoment u₀ c (t - (i : ℕ)) (fun _ => 1) := by
    rw [dualMoment_congr hu₀.le t fun u hu => hsys q u (Ioc_subset_Icc_self hu)]
    have c1 : ∀ i : Fin (d + 1), ContinuousOn
        (fun u : ℝ => ∑ p : Fin ℓ, A i q p * ((u : ℂ) ^ (i : ℕ) * G p u)) (Icc 0 u₀) :=
      fun i => continuousOn_finsetSum _ fun p _ => continuousOn_const.mul ((hpow i).mul (hGc p))
    have c2 : ∀ i : Fin (e + 1), ContinuousOn (fun u : ℝ => b i q * (u : ℂ) ^ (i : ℕ)) (Icc 0 u₀) :=
      fun i => continuousOn_const.mul (hpow i)
    rw [dualMoment_add hc hu₀ t (continuousOn_finsetSum _ fun i _ => c1 i)
      (continuousOn_finsetSum _ fun i _ => c2 i)]
    rw [dualMoment_finsetSum hc hu₀ t _ fun i _ => c1 i,
      dualMoment_finsetSum hc hu₀ t _ fun i _ => c2 i]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      have c3 : ∀ p : Fin ℓ, ContinuousOn (fun u : ℝ => A i q p * ((u : ℂ) ^ (i : ℕ) * G p u))
          (Icc 0 u₀) := fun p => continuousOn_const.mul ((hpow i).mul (hGc p))
      rw [dualMoment_finsetSum hc hu₀ t _ fun p _ => c3 p]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [dualMoment_const_mul, dualMoment_mul_pow _ _ _ _ _ hu₀.le]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [dualMoment_const_mul, ← dualMoment_mul_pow _ _ _ _ _ hu₀.le]
      simp
  rw [h1]; ring

/-! ### Differentiation in `c` -/

lemma hasDerivAt_dualWeight_c (t : ℂ) {u : ℝ} (hu : 0 < u) (c : ℝ) :
    HasDerivAt (fun x => dualWeight x t u) (-dualWeight c (t + 1) u) c := by
  have h : HasDerivAt (fun x : ℝ => (rexp (-(x / u)) : ℂ)) ((rexp (-(c / u)) * (-(1 / u)) : ℝ)) c := by
    apply HasDerivAt.ofReal_comp
    have := ((hasDerivAt_id c).div_const u).neg.exp
    simpa [div_eq_mul_inv] using this
  have h2 := h.const_mul ((u : ℂ) ^ (-t))
  simp only [dualWeight_of_pos hu]
  convert h2 using 1
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  rw [neg_add, Complex.cpow_add _ _ hu', Complex.cpow_neg_one]
  push_cast; field_simp

lemma norm_dualWeight_anti {t : ℂ} {u c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    ‖dualWeight c₂ t u‖ ≤ ‖dualWeight c₁ t u‖ := by
  rcases le_or_gt u 0 with hu | hu
  · simp [dualWeight, not_lt.2 hu]
  · rw [norm_dualWeight_of_pos hu, norm_dualWeight_of_pos hu]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (inv_nonneg.2 hu.le) _)
    rw [Real.exp_le_exp]
    have := inv_pos.2 hu
    nlinarith

/-- **`-∂_c Z_t[g] = Z_{t+1}[g]`** (paper, before Proposition 3.6). -/
theorem hasDerivAt_dualMoment {u₀ c : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (t : ℂ) {g : ℝ → ℂ}
    (hg : ContinuousOn g (Icc 0 u₀)) :
    HasDerivAt (fun x => dualMoment u₀ x t g) (-dualMoment u₀ c (t + 1) g) c := by
  have hc2 : 0 < c / 2 := by positivity
  have hIcc : uIcc (0 : ℝ) u₀ = Icc 0 u₀ := uIcc_of_le hu₀.le
  have hmeas : ∀ x, 0 < x → ∀ t', AEStronglyMeasurable (fun u => dualWeight x t' u * g u)
      (volume.restrict (Set.uIoc 0 u₀)) := fun x hx t' =>
    (((continuous_dualWeight hx t').continuousOn.mul hg).mono
      (by rw [uIoc_of_le hu₀.le]; exact Ioc_subset_Icc_self)).aestronglyMeasurable
      measurableSet_uIoc
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := u₀)
    (F := fun x u => dualWeight x t u * g u) (F' := fun x u => -dualWeight x (t + 1) u * g u)
    (x₀ := c) (s := Ioi (c / 2)) (bound := fun u => ‖dualWeight (c / 2) (t + 1) u‖ * ‖g u‖)
    (Ioi_mem_nhds (by linarith))
    (by filter_upwards [Ioi_mem_nhds hc] with x hx using hmeas x hx t)
    (intervalIntegrable_dualWeight_mul hc hu₀ t hg)
    (by
      have := (hmeas c hc (t + 1)).neg
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp [neg_mul])
    (Eventually.of_forall fun u hu x hx => by
      rw [norm_mul, norm_neg]
      exact mul_le_mul_of_nonneg_right (norm_dualWeight_anti (le_of_lt hx)) (norm_nonneg _))
    ((((continuous_dualWeight hc2 (t + 1)).norm.continuousOn.mul hg.norm).mono
      (by rw [hIcc])).intervalIntegrable)
    (Eventually.of_forall fun u hu x _ => by
      rw [uIoc_of_le hu₀.le] at hu
      exact (hasDerivAt_dualWeight_c t hu.1 x).mul_const (g u))
  unfold dualMoment
  convert key.2 using 1
  rw [← intervalIntegral.integral_neg]
  congr 1; funext u; ring

end ZetaF
