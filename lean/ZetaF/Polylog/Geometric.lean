/-
# Theorem 4.1(1) on the unit circle: the polylogarithm `Li_F(s, z)`, `|z| = 1`

For real `α`, `z = e^{2πiα}` and `Re s > 2`,
`Li_F^{≥k₀}(s,z) = ∑_{k≥k₀} (C_k I_k(s) + k S_k I_k(s+1))
    + (√π/2) ∑_{n∈ℤ} (J^{(0)}_s(c_n) - iπ(n-α) J^{(1)}_{s+1}(c_n))
    - ½ H(s) - ∑_{k<k₀} (C_k L_k(s) + k S_k L_k(s+1))`.
This is the first step of the paper's proof of Theorem 4.1(1); the extension to `|z| < 1` is by
analytic continuation in `α` and is not formalized.
-/
import ZetaF.Polylog.Split
import ZetaF.Polylog.Theta

open Real MeasureTheory Set Filter Finset

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-- `J^{(δ)}_w(c) = Z_t[h](c) = ∫₀^{u₀} u^{-t} e^{-c/u} h(u) du` (with `t = 1/2 + δ`). -/
noncomputable def geoJ (h : ℝ → ℂ) (u₀ t c : ℝ) : ℂ :=
  ∫ u in Ioc 0 u₀, ((u ^ (-t) * rexp (-(c / u)) : ℝ) : ℂ) * h u

/-- `L_k = ∫₀^{u₀} e^{-k²u} h(u) du`. -/
noncomputable def lowerL (h : ℝ → ℂ) (u₀ : ℝ) (k : ℕ) : ℂ :=
  ∫ u in Ioc 0 u₀, (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u

/-- `H = ∫₀^{u₀} h(u) du`. -/
noncomputable def lowerH (h : ℝ → ℂ) (u₀ : ℝ) : ℂ := ∫ u in Ioc 0 u₀, h u

lemma norm_geoC_le {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) : ‖geoC z k‖ ≤ 1 := by
  rw [geoC, norm_div, Complex.norm_two]
  calc ‖z ^ k + (z ^ k)⁻¹‖ / 2 ≤ (‖z ^ k‖ + ‖(z ^ k)⁻¹‖) / 2 := by gcongr; exact norm_add_le _ _
    _ = 1 := by rw [norm_inv, norm_pow, hz]; norm_num

lemma norm_geoS_le {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) : ‖geoS z k‖ ≤ 1 := by
  rw [geoS, norm_div, Complex.norm_two]
  calc ‖z ^ k - (z ^ k)⁻¹‖ / 2 ≤ (‖z ^ k‖ + ‖(z ^ k)⁻¹‖) / 2 := by gcongr; exact norm_sub_le _ _
    _ = 1 := by rw [norm_inv, norm_pow, hz]; norm_num

lemma geoDual_nonneg (α : ℝ) (n : ℤ) : 0 ≤ geoDual α n := by unfold geoDual; positivity

/-- The Laplace representation in closed form: `∫₀^∞ e^{-K²u} h_w(u) du = F(K) K^{-w}`. -/
lemma integral_exp_kernel_eq (ha : GeomBounded a R) (hR : 0 ≤ R) {w : ℂ} (hw : 0 < w.re)
    {K : ℕ} (hK : R < K) :
    ∫ u in Ioi 0, (rexp (-((K : ℝ) ^ 2 * u)) : ℂ) * kernel a w u =
      evalInv a K / (K : ℂ) ^ w := by
  have hK0 : K ≠ 0 := by rintro rfl; simp at hK; linarith
  rw [← (hasSum_laplace_kernel ha hR hw hK).tsum_eq, evalInv]
  simp_rw [Complex.ofReal_natCast, natCast_cpow_neg_add hK0]
  rw [div_eq_mul_inv, ← tsum_mul_right]; congr 1; funext n; ring

lemma integrableOn_of_inv_mul {h : ℝ → ℂ} {u₀ : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hn1 : IntegrableOn (fun u => u⁻¹ * ‖h u‖) (Ioc 0 u₀)) : IntegrableOn h (Ioc 0 u₀) := by
  refine Integrable.mono' (hn1.const_mul u₀) ?_ ?_
  · exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
  · refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    rw [← mul_assoc]
    refine le_mul_of_one_le_left (norm_nonneg _) ?_
    rw [← div_eq_mul_inv]; exact (one_le_div hu.1).2 hu.2

lemma integrableOn_kernel_inv (ha : GeomBounded a R) (hR : 0 ≤ R) {s : ℂ} (hs : 2 < s.re)
    {u₀ : ℝ} (hu₀ : 0 < u₀) :
    IntegrableOn (fun u => u⁻¹ * ‖kernel a s u‖) (Ioc 0 u₀) := by
  have := integrableOn_rpow_neg_mul_norm_kernel ha hR (by linarith) (t := 1) (by linarith) hu₀
  refine this.congr_fun (fun u hu => ?_) measurableSet_Ioc
  simp only [Real.rpow_neg_one]

lemma integral_main_split {h : ℝ → ℂ} {u₀ : ℝ} (hcont : ContinuousOn h (Ioi 0))
    (hn1 : IntegrableOn (fun u => u⁻¹ * ‖h u‖) (Ioc 0 u₀)) (W₀ : ℂ) (c : ℕ → ℂ) (k₀ : ℕ) :
    ∫ u in Ioc 0 u₀, (W₀ - ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) * h u =
      W₀ * lowerH h u₀ - ∑ k ∈ Ico 1 k₀, c k * lowerL h u₀ k := by
  have hh := integrableOn_of_inv_mul hcont hn1
  have hhn : IntegrableOn (fun u => 1 * ‖h u‖) (Ioc 0 u₀) := by
    have : IntegrableOn (fun u => ‖h u‖) (Ioc 0 u₀) := hh.norm
    simpa using this
  have hL : ∀ k : ℕ, IntegrableOn (fun u => (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u) (Ioc 0 u₀) :=
    fun k => integrableOn_weight_mul_of_le hcont (continuous_expneg _).continuousOn
      Ioc_subset_Ioi_self measurableSet_Ioc (g := fun _ => 1) hhn
      (fun u hu => by
        rw [abs_of_pos (exp_pos _), exp_le_one_iff, neg_nonpos]
        exact mul_nonneg (sq_nonneg _) hu.1.le)
  calc ∫ u in Ioc 0 u₀, (W₀ - ∑ k ∈ Ico 1 k₀, c k * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) * h u
      = ∫ u in Ioc 0 u₀, (W₀ * h u -
          ∑ k ∈ Ico 1 k₀, c k * ((rexp (-((k : ℝ) ^ 2 * u)) : ℂ) * h u)) := by
        congr 1; funext u; rw [sub_mul, Finset.sum_mul]; congr 1
        exact sum_congr rfl fun k _ => by ring
    _ = W₀ * lowerH h u₀ - ∑ k ∈ Ico 1 k₀, c k * lowerL h u₀ k := by
        rw [integral_sub (hh.const_mul _) (integrable_finsetSum _ fun k _ => (hL k).const_mul _),
          integral_const_mul, integral_finsetSum _ fun k _ => (hL k).const_mul _]
        simp_rw [integral_const_mul]
        rfl

/-- **Theorem 4.1(1) for `|z| = 1`, `Re s > 2`.** -/
theorem polylogTail_split (ha : GeomBounded a R) (hR : 0 ≤ R) {F : ℕ → ℂ} {k₀ : ℕ}
    (hk₀ : 1 ≤ k₀) (hRk : R < k₀) (hF : ∀ k ≥ k₀, F k = evalInv a k) {s : ℂ} (hs : 2 < s.re)
    (α : ℝ) {u₀ : ℝ} (hu₀ : 0 < u₀) :
    zetaTail (fun k => F k * Complex.exp (2 * π * Complex.I * α) ^ k) k₀ s =
      (∑' k : ℕ, (geoC (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
          kTerm (kernel a s) u₀ (k + k₀) +
        ((k + k₀ : ℕ) : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) (k + k₀) *
          kTerm (kernel a (s + 1)) u₀ (k + k₀))) +
      ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, (geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
        Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) *
          geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) -
      1 / 2 * lowerH (kernel a s) u₀ -
      ∑ k ∈ Ico 1 k₀, (geoC (Complex.exp (2 * π * Complex.I * α)) k * lowerL (kernel a s) u₀ k +
        (k : ℂ) * geoS (Complex.exp (2 * π * Complex.I * α)) k * lowerL (kernel a (s + 1)) u₀ k) := by
  set z := Complex.exp (2 * π * Complex.I * α) with hz_def
  have hz : ‖z‖ = 1 := by
    rw [hz_def, show 2 * π * Complex.I * (α : ℂ) = ((2 * π * α : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hs0 : 0 < s.re := by linarith
  have hs1 : 0 < (s + 1).re := by simp; linarith
  set e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  have hIoc : Ioc (0 : ℝ) u₀ ⊆ Ioi 0 := Ioc_subset_Ioi_self
  -- the even part
  set De : ℕ → ℝ → ℂ := fun m u =>
    (((√π / 2) * (u ^ (-(1 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u))) : ℝ) : ℂ) with hDe
  have hθe : ∀ u ∈ Ioc 0 u₀, ∑' k : ℕ, geoC z (k + 1) * (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) =
      (fun _ => -(1 / 2 : ℂ)) u + ∑' m, De m u := by
    intro u hu
    rw [tsum_geoC_theta α hu.1, e.tsum_eq (f := fun n => ((((√π / 2) * (u ^ (-(1 / 2 : ℝ)) *
      rexp (-(geoDual α n / u)))) : ℝ) : ℂ)), ← tsum_mul_left]
    congr 2; funext n; push_cast; ring
  have hev := split_theta_lin (h := kernel a s) (c := geoC z) (B := 1)
    (fun k => (norm_geoC_le hz k).trans (by
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith))
    hθe hk₀ hu₀ (continuousOn_kernel ha hR hs0) (integrableOn_kernel_inv ha hR hs hu₀)
    ((integrableOn_exp_mul_norm_kernel ha hR hs0 hRk).mono_set (Ioi_subset_Ioi hu₀.le))
    (fun m => Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (continuousOn_dualWeight _)))
    (b := fun m => √π / 2 * rexp (-(geoDual α (e m) / u₀))) (g := fun u => u ^ (-(1 / 2 : ℝ)))
    ((e.summable_iff.2 (summable_geoDual α hu₀)).mul_left _)
    (integrableOn_rpow_neg_mul_norm_kernel ha hR hs0 (t := 1 / 2) (by linarith) hu₀)
    (fun m u hu => by
      have hr := Real.rpow_nonneg hu.1.le (-(1 / 2 : ℝ))
      rw [hDe, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have hexp : rexp (-(geoDual α (e m) / u)) ≤ rexp (-(geoDual α (e m) / u₀)) := by
        rw [exp_le_exp, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (geoDual_nonneg _ _) hu.1 hu.2
      calc √π / 2 * (u ^ (-(1 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u)))
          ≤ √π / 2 * (u ^ (-(1 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u₀))) := by gcongr
        _ = _ := by ring)
    continuousOn_const (A := 1 / 2) (fun u _ => by norm_num)
  -- the odd part
  set Do : ℕ → ℝ → ℂ := fun m u => -(Complex.I / 2 * ((π * √π : ℝ) : ℂ)) *
    (((((e m : ℤ) : ℝ) - α) * (u ^ (-(3 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u))) : ℝ) : ℂ)
    with hDo
  have hθo : ∀ u ∈ Ioc 0 u₀, ∑' k : ℕ, (fun k : ℕ => (k : ℂ) * geoS z k) (k + 1) *
      (rexp (-(((k : ℝ) + 1) ^ 2 * u)) : ℂ) = (fun _ => (0 : ℂ)) u + ∑' m, Do m u := by
    intro u hu
    have h1 := tsum_geoS_theta α hu.1
    simp only [Nat.cast_add, Nat.cast_one, zero_add]
    rw [h1, e.tsum_eq (f := fun n : ℤ => -(Complex.I / 2 * ((π * √π : ℝ) : ℂ)) *
      (((((n : ℝ) - α) * (u ^ (-(3 / 2 : ℝ)) * rexp (-(geoDual α n / u))) : ℝ) : ℂ))),
      ← tsum_mul_left]
    congr 1; funext n; push_cast; ring
  have hod := split_theta_lin (h := kernel a (s + 1)) (c := fun k : ℕ => (k : ℂ) * geoS z k)
    (B := 1)
    (fun k => by
      rw [norm_mul, Complex.norm_natCast]
      calc (k : ℝ) * ‖geoS z k‖ ≤ k * 1 :=
            mul_le_mul_of_nonneg_left (norm_geoS_le hz k) (Nat.cast_nonneg _)
        _ ≤ 1 * ((k : ℝ) + 1) := by linarith)
    hθo hk₀ hu₀ (continuousOn_kernel ha hR hs1)
    (integrableOn_kernel_inv ha hR (by simp; linarith) hu₀)
    ((integrableOn_exp_mul_norm_kernel ha hR hs1 hRk).mono_set (Ioi_subset_Ioi hu₀.le))
    (fun m => continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_const.mul (continuousOn_dualWeightOdd _))))
    (b := fun m => π * √π / 2 * (|((e m : ℤ) : ℝ) - α| * rexp (-(geoDual α (e m) / u₀))))
    (g := fun u => u ^ (-(3 / 2 : ℝ)))
    ((e.summable_iff.2 (summable_abs_mul_geoDual α hu₀)).mul_left _)
    (integrableOn_rpow_neg_mul_norm_kernel ha hR hs1 (t := 3 / 2) (by simp; linarith) hu₀)
    (fun m u hu => by
      have hr := Real.rpow_nonneg hu.1.le (-(3 / 2 : ℝ))
      rw [hDo, norm_mul, norm_neg, norm_mul, norm_div, Complex.norm_I, Complex.norm_two,
        Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < π * √π), abs_mul,
        abs_of_nonneg (mul_nonneg hr (exp_pos _).le)]
      have hexp : rexp (-(geoDual α (e m) / u)) ≤ rexp (-(geoDual α (e m) / u₀)) := by
        rw [exp_le_exp, neg_le_neg_iff]
        exact div_le_div_of_nonneg_left (geoDual_nonneg _ _) hu.1 hu.2
      calc 1 / 2 * (π * √π) * (|((e m : ℤ) : ℝ) - α| *
            (u ^ (-(3 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u))))
          ≤ 1 / 2 * (π * √π) * (|((e m : ℤ) : ℝ) - α| *
            (u ^ (-(3 / 2 : ℝ)) * rexp (-(geoDual α (e m) / u₀)))) := by gcongr
        _ = _ := by ring)
    continuousOn_const (A := 0) (fun u _ => by simp)
  -- the terms
  have hterm : ∀ k : ℕ, geoC z (k + k₀) *
      (∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a s u) +
      (fun k : ℕ => (k : ℂ) * geoS z k) (k + k₀) *
      (∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a (s + 1) u) =
      LSeries.term (tail k₀ (fun k => F k * z ^ k)) s (k + k₀) := by
    intro k
    have hK : (k + k₀ : ℕ) ≠ 0 := by omega
    have hK' : ((k + k₀ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hK
    have hRK : R < ((k + k₀ : ℕ) : ℝ) :=
      lt_of_lt_of_le hRk (by exact_mod_cast Nat.le_add_left k₀ k)
    rw [integral_exp_kernel_eq ha hR hs0 hRK, integral_exp_kernel_eq ha hR hs1 hRK,
      LSeries.term_of_ne_zero hK, tail, ite_eq_left (Nat.le_add_left k₀ k),
      hF _ (Nat.le_add_left k₀ k)]
    have hKs : ((k + k₀ : ℕ) : ℂ) ^ (s + 1) = ((k + k₀ : ℕ) : ℂ) ^ s * ((k + k₀ : ℕ) : ℂ) := by
      rw [Complex.cpow_add _ _ hK', Complex.cpow_one]
    have hKs0 : ((k + k₀ : ℕ) : ℂ) ^ s ≠ 0 := by
      rw [Ne, Complex.cpow_eq_zero_iff]; tauto
    have hzK : z ^ (k + k₀) ≠ 0 := pow_ne_zero _ (Complex.exp_ne_zero _)
    rw [hKs]
    simp only [geoC, geoS]
    field_simp
    ring
  have hsum := hev.2.2.add hod.2.2
  rw [show (fun k => geoC z (k + k₀) *
      (∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a s u) +
      (fun k : ℕ => (k : ℂ) * geoS z k) (k + k₀) *
      (∫ u in Ioi 0, (rexp (-(((k + k₀ : ℕ) : ℝ) ^ 2 * u)) : ℂ) * kernel a (s + 1) u)) =
      fun k => LSeries.term (tail k₀ (fun k => F k * z ^ k)) s (k + k₀) from funext hterm] at hsum
  have hzero : ∑ i ∈ Finset.range k₀, LSeries.term (tail k₀ (fun k => F k * z ^ k)) s i = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [LSeries.term, tail, show ¬ k₀ ≤ i by omega]
  have hfull := (hasSum_nat_add_iff' (f := LSeries.term (tail k₀ (fun k => F k * z ^ k)) s) k₀).1
    (by rw [hzero, sub_zero]; exact hsum)
  rw [zetaTail, LSeries, hfull.tsum_eq]
  -- rearranging the value
  have hDe_int : ∀ m, ∫ u in Ioc 0 u₀, De m u * kernel a s u =
      ((√π / 2 : ℝ) : ℂ) * geoJ (kernel a s) u₀ (1 / 2) (geoDual α (e m)) := fun m => by
    rw [geoJ, ← integral_const_mul]; congr 1; funext u; simp only [hDe]; push_cast; ring
  have hDo_int : ∀ m, ∫ u in Ioc 0 u₀, Do m u * kernel a (s + 1) u =
      ((√π / 2 : ℝ) : ℂ) * (-(Complex.I * π * (((((e m : ℤ) : ℝ)) - α : ℝ) : ℂ)) *
        geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α (e m))) := fun m => by
    rw [geoJ, ← integral_const_mul, ← integral_const_mul]; congr 1; funext u; simp only [hDo]
    push_cast
    ring
  have hd1 : ∑' m, ∫ u in Ioc 0 u₀, De m u * kernel a s u =
      ∑' n : ℤ, ((√π / 2 : ℝ) : ℂ) * geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) := by
    simp_rw [hDe_int]
    exact e.tsum_eq (fun n => ((√π / 2 : ℝ) : ℂ) * geoJ (kernel a s) u₀ (1 / 2) (geoDual α n))
  have hd2 : ∑' m, ∫ u in Ioc 0 u₀, Do m u * kernel a (s + 1) u =
      ∑' n : ℤ, ((√π / 2 : ℝ) : ℂ) * (-(Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ)) *
        geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) := by
    simp_rw [hDo_int]
    exact e.tsum_eq (fun n : ℤ => ((√π / 2 : ℝ) : ℂ) * (-(Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ)) *
        geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)))
  have hs1' : Summable fun n : ℤ => ((√π / 2 : ℝ) : ℂ) *
      geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) :=
    e.summable_iff.1 (hev.2.1.congr hDe_int)
  have hs2' : Summable fun n : ℤ => ((√π / 2 : ℝ) : ℂ) * (-(Complex.I * π *
      (((n : ℝ) - α : ℝ) : ℂ)) * geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) :=
    e.summable_iff.1 (hod.2.1.congr hDo_int)
  have hdual : ((√π / 2 : ℝ) : ℂ) * ∑' n : ℤ, (geoJ (kernel a s) u₀ (1 / 2) (geoDual α n) -
      Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ) * geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) =
      (∑' n : ℤ, ((√π / 2 : ℝ) : ℂ) * geoJ (kernel a s) u₀ (1 / 2) (geoDual α n)) +
      ∑' n : ℤ, ((√π / 2 : ℝ) : ℂ) * (-(Complex.I * π * (((n : ℝ) - α : ℝ) : ℂ)) *
        geoJ (kernel a (s + 1)) u₀ (3 / 2) (geoDual α n)) := by
    rw [← hs1'.tsum_add hs2', ← tsum_mul_left]; congr 1; funext n; ring
  rw [integral_main_split (continuousOn_kernel ha hR hs0) (integrableOn_kernel_inv ha hR hs hu₀),
    integral_main_split (continuousOn_kernel ha hR hs1)
      (integrableOn_kernel_inv ha hR (by simp; linarith) hu₀),
    hev.1.tsum_add hod.1, hd1, hd2, hdual, Finset.sum_add_distrib]
  ring

end ZetaF
