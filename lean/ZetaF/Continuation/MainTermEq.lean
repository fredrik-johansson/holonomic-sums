/-
# `M(s)` equals its series for `Re s > 1`

Termwise integration of `M(s) = ∫₀^{u₀} (½√(π/u) - ½ - ∑_{k<k₀} e^{-k²u}) h_s(u) du`.
-/
import ZetaF.Continuation.MainTerm

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

lemma ofReal_sqrt_cpow {u : ℝ} (hu : 0 < u) (w : ℂ) :
    ((√u : ℝ) : ℂ)⁻¹ * (u : ℂ) ^ (w - 1) = (u : ℂ) ^ (w - 3 / 2) := by
  have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
  have hs : ((√u : ℝ) : ℂ) = (u : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hu.le]; push_cast; ring_nf
  have hne : (u : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hu')
  rw [hs, show w - 1 = (w - 3 / 2) + 1 / 2 by ring, Complex.cpow_add _ _ hu']
  field_simp

/-- Pointwise form of the main-term integrand. -/
lemma mainWeight_mul_kernelTerm {k₀ : ℕ} {s : ℂ} (n : ℕ) {u : ℝ} (hu : 0 < u) :
    (mainWeight k₀ u : ℂ) * kernelTerm a s n u =
      a n * (Complex.Gamma ((s + n) / 2))⁻¹ * ((√π / 2 : ℂ) * (u : ℂ) ^ ((s + n) / 2 - 3 / 2) -
        (1 / 2 : ℂ) * (u : ℂ) ^ ((s + n) / 2 - 1) -
        ∑ k ∈ Finset.Ico 1 k₀, (u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) := by
  unfold mainWeight kernelTerm
  have h1 : ((√(π / u) : ℝ) : ℂ) * (u : ℂ) ^ ((s + n) / 2 - 1) =
      (√π : ℂ) * (u : ℂ) ^ ((s + n) / 2 - 3 / 2) := by
    rw [Real.sqrt_div' _ hu.le, Complex.ofReal_div, div_eq_mul_inv, mul_assoc,
      ofReal_sqrt_cpow hu]
  push_cast
  rw [← Finset.mul_sum]
  linear_combination (1 / 2 * a n * (Complex.Gamma ((s + n) / 2))⁻¹) * h1

lemma integral_Ioc_cpow {u₀ : ℝ} (hu₀ : 0 < u₀) {r : ℂ} (hr : -1 < r.re) :
    ∫ u in Ioc 0 u₀, (u : ℂ) ^ r = (u₀ : ℂ) ^ (r + 1) / (r + 1) := by
  have hr1 : r + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [← intervalIntegral.integral_of_le hu₀.le, integral_cpow (Or.inl hr)]
  simp [Complex.zero_cpow hr1]

lemma integrableOn_Ioc_cpow {u₀ : ℝ} (hu₀ : 0 < u₀) {r : ℂ} (hr : -1 < r.re) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ r) (Ioc 0 u₀) :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
    (intervalIntegral.intervalIntegrable_cpow' hr)

/-- The integral of one term of the main term. -/
lemma integral_mainWeight_mul_kernelTerm {u₀ : ℝ} (hu₀ : 0 < u₀) (k₀ : ℕ) {s : ℂ} (n : ℕ)
    (hw : 1 / 2 < ((s + n) / 2).re) :
    ∫ u in Ioc 0 u₀, (mainWeight k₀ u : ℂ) * kernelTerm a s n u = mainSeriesTerm a u₀ k₀ n s := by
  set w := (s + n) / 2 with hwdef
  have hw0 : 0 < w.re := by linarith
  have hk : ∀ k ∈ Finset.Ico 1 k₀, 0 < (k : ℝ) := fun k hk => by
    simp only [Finset.mem_Ico] at hk; exact_mod_cast (by omega : 0 < k)
  have i1 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 3 / 2)) (Ioc 0 u₀) :=
    integrableOn_Ioc_cpow hu₀ (by simp; linarith)
  have i2 : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1)) (Ioc 0 u₀) :=
    integrableOn_Ioc_cpow hu₀ (by simp; linarith)
  have i3 : ∀ k ∈ Finset.Ico 1 k₀, IntegrableOn (fun u : ℝ => (u : ℂ) ^ (w - 1) *
      (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) (Ioc 0 u₀) := fun k hk' =>
    (integrableOn_cpow_mul_exp_Ioi_zero (by have := hk k hk'; positivity) hw0).mono_set
      Ioc_subset_Ioi_self
  have j1 : IntegrableOn (fun u : ℝ => (√π / 2 : ℂ) * (u : ℂ) ^ (w - 3 / 2)) (Ioc 0 u₀) :=
    i1.const_mul _
  have j2 : IntegrableOn (fun u : ℝ => (1 / 2 : ℂ) * (u : ℂ) ^ (w - 1)) (Ioc 0 u₀) :=
    i2.const_mul _
  have j12 : IntegrableOn (fun u : ℝ => (√π / 2 : ℂ) * (u : ℂ) ^ (w - 3 / 2) -
      (1 / 2 : ℂ) * (u : ℂ) ^ (w - 1)) (Ioc 0 u₀) := j1.sub j2
  have j3 : IntegrableOn (fun u : ℝ => ∑ k ∈ Finset.Ico 1 k₀, (u : ℂ) ^ (w - 1) *
      (rexp (-((k : ℝ) ^ 2 * u)) : ℂ)) (Ioc 0 u₀) := integrable_finsetSum _ i3
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u hu => mainWeight_mul_kernelTerm n hu.1),
    integral_const_mul, ← hwdef, integral_sub j12 j3, integral_sub j1 j2,
    integral_const_mul, integral_const_mul, integral_finsetSum _ i3,
    integral_Ioc_cpow hu₀ (by simp; linarith), integral_Ioc_cpow hu₀ (by simp; linarith)]
  have hL : ∀ k ∈ Finset.Ico 1 k₀, ∫ u in Ioc 0 u₀, (u : ℂ) ^ (w - 1) *
      (rexp (-((k : ℝ) ^ 2 * u)) : ℂ) = lowerLaplace ((k : ℝ) ^ 2) u₀ w := fun _ _ => rfl
  rw [Finset.sum_congr rfl hL]
  unfold mainSeriesTerm
  rw [← hwdef]
  have hU : ∀ k ∈ Finset.Ico 1 k₀, (k : ℂ) ^ (-2 * w) - (Complex.Gamma w)⁻¹ *
      upperLaplace ((k : ℝ) ^ 2) u₀ w = (Complex.Gamma w)⁻¹ * lowerLaplace ((k : ℝ) ^ 2) u₀ w := by
    intro k hk'
    have h := cpow_sub_upperLaplace (k := (k : ℝ)) (hk k hk') hu₀ hw0
    simpa only [Complex.ofReal_natCast] using h
  rw [Finset.sum_congr rfl hU, ← Finset.mul_sum]
  have hwne : w ≠ 0 := fun h => by rw [h] at hw0; simp at hw0
  have hΓ1 : (Complex.Gamma (w + 1))⁻¹ = (Complex.Gamma w)⁻¹ / w := by
    rw [← mul_inv_Gamma_add_one w]; field_simp
  have hsn : s + n - 1 = 2 * (w - 1 / 2) := by rw [hwdef]; ring
  have hw2 : w - 1 / 2 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [hΓ1, hsn, show w - 3 / 2 + 1 = w - 1 / 2 by ring, show w - 1 + 1 = w by ring]
  field_simp

/-- **The main term equals its series for `Re s > 1`.** -/
theorem hasSum_mainSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {u₀ : ℝ} (hu₀ : 0 < u₀) (k₀ : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n => mainSeriesTerm a u₀ k₀ n s) (mainTerm (kernel a s) u₀ k₀) := by
  have hs0 : 0 < s.re := by linarith
  obtain ⟨D, hD0, hD⟩ := exists_coeff_bound ha hs0
  set σ := s.re
  have hx : ∀ n : ℕ, 1 / 2 < ((s + n) / 2).re := fun n => by
    simp; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  -- majorant for one term
  set g : ℕ → ℝ → ℝ := fun n u => ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
    (1 / 2 * √π * u ^ ((σ + n) / 2 - 3 / 2) + (k₀ + 1) * u ^ ((σ + n) / 2 - 1)) with hg
  have hgint : ∀ n, IntegrableOn (g n) (Ioc 0 u₀) := by
    intro n
    have h1 : -1 < (σ + n) / 2 - 3 / 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have h2 : -1 < (σ + n) / 2 - 1 := by linarith
    have r1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
      (intervalIntegral.intervalIntegrable_rpow' h1)
    have r2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
      (intervalIntegral.intervalIntegrable_rpow' h2)
    exact ((r1.const_mul _).add (r2.const_mul _)).const_mul _
  have hgle : ∀ n, ∀ u ∈ Ioc 0 u₀, (1 / 2 * √π * u ^ (-(1 / 2 : ℝ)) + (k₀ + 1)) *
      ‖kernelTerm a s n u‖ = g n u := by
    intro n u hu
    rw [norm_kernelTerm hu.1]
    simp only [hg]
    have e : u ^ (-(1 / 2 : ℝ)) * u ^ ((σ + n) / 2 - 1) = u ^ ((σ + n) / 2 - 3 / 2) := by
      rw [← Real.rpow_add hu.1]; ring_nf
    linear_combination (1 / 2 * √π * (‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖)) * e
  have hint : ∀ n, IntegrableOn (fun u => (mainWeight k₀ u : ℂ) * kernelTerm a s n u)
      (Ioc 0 u₀) := by
    intro n
    refine integrableOn_weight_mul_of_le (continuousOn_kernelTerm n) (continuousOn_mainWeight k₀)
      Ioc_subset_Ioi_self measurableSet_Ioc ((hgint n).congr_fun (fun u hu => (hgle n u hu).symm)
        measurableSet_Ioc) fun u hu => abs_mainWeight_le hu.1
  have hnorm_le : ∀ n, ∫ u in Ioc 0 u₀, ‖(mainWeight k₀ u : ℂ) * kernelTerm a s n u‖ ≤
      ∫ u in Ioc 0 u₀, g n u := by
    intro n
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hgint n) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
    dsimp only
    rw [← hgle n u hu, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_mainWeight_le hu.1) (norm_nonneg _)
  have hgval : ∀ n, ∫ u in Ioc 0 u₀, g n u ≤ majCoeff D R σ n *
      ((1 / 2 * √π * (2 / (σ - 1)) * u₀ ^ ((σ - 1) / 2) + (k₀ + 1) * (2 / σ) * u₀ ^ (σ / 2)) *
        (√u₀) ^ n) := by
    intro n
    have h1 : -1 < (σ + n) / 2 - 3 / 2 := by
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
    have h2 : -1 < (σ + n) / 2 - 1 := by linarith
    simp only [hg]
    rw [integral_const_mul, integral_add, integral_const_mul, integral_const_mul,
      ← intervalIntegral.integral_of_le hu₀.le, ← intervalIntegral.integral_of_le hu₀.le,
      integral_rpow (Or.inl h1), integral_rpow (Or.inl h2), Real.zero_rpow (by linarith),
      Real.zero_rpow (by linarith)]
    · simp only [sub_zero]
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have ea : (σ + n) / 2 - 3 / 2 + 1 = (σ - 1 + n) / 2 := by ring
      have eb : (σ + n) / 2 - 1 + 1 = (σ + n) / 2 := by ring
      rw [ea, eb, rpow_half_add_nat hu₀, rpow_half_add_nat hu₀]
      have hc := hD n
      have hm := majCoeff_nonneg hD0 hR hs0 n (D := D) (R := R)
      have hp1 : 0 ≤ u₀ ^ ((σ - 1) / 2) * √u₀ ^ n := by positivity
      have hp2 : 0 ≤ u₀ ^ (σ / 2) * √u₀ ^ n := by positivity
      have hd1 : (σ - 1) / 2 ≤ (σ - 1 + n) / 2 := by linarith
      have hd2 : σ / 2 ≤ (σ + n) / 2 := by linarith
      have q1 : u₀ ^ ((σ - 1) / 2) * √u₀ ^ n / ((σ - 1 + n) / 2) ≤
          2 / (σ - 1) * (u₀ ^ ((σ - 1) / 2) * √u₀ ^ n) := by
        calc _ ≤ u₀ ^ ((σ - 1) / 2) * √u₀ ^ n / ((σ - 1) / 2) :=
              div_le_div_of_nonneg_left hp1 (by linarith) hd1
          _ = _ := by field_simp
      have q2 : u₀ ^ (σ / 2) * √u₀ ^ n / ((σ + n) / 2) ≤
          2 / σ * (u₀ ^ (σ / 2) * √u₀ ^ n) := by
        calc _ ≤ u₀ ^ (σ / 2) * √u₀ ^ n / (σ / 2) :=
              div_le_div_of_nonneg_left hp2 (by linarith) hd2
          _ = _ := by field_simp
      calc _ ≤ majCoeff D R σ n * (1 / 2 * √π * (2 / (σ - 1) * (u₀ ^ ((σ - 1) / 2) * √u₀ ^ n)) +
              (k₀ + 1) * (2 / σ * (u₀ ^ (σ / 2) * √u₀ ^ n))) := by
            apply mul_le_mul hc _ (by positivity) hm
            gcongr
        _ = _ := by ring
    · exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
        (intervalIntegral.intervalIntegrable_rpow' h1)).const_mul _)
    · exact (((intervalIntegrable_iff_integrableOn_Ioc_of_le hu₀.le).1
        (intervalIntegral.intervalIntegrable_rpow' h2)).const_mul _)
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀, ‖(mainWeight k₀ u : ℂ) * kernelTerm a s n u‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => (hnorm_le n).trans (hgval n)) ?_
    have := (summable_majCoeff_mul_pow (D := D) (σ := σ) (q := √u₀) hR hs0
      (Real.sqrt_nonneg _)).mul_left
      (1 / 2 * √π * (2 / (σ - 1)) * u₀ ^ ((σ - 1) / 2) + (k₀ + 1) * (2 / σ) * u₀ ^ (σ / 2))
    refine this.congr fun n => by ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n; exact (integral_mainWeight_mul_kernelTerm hu₀ k₀ n (hx n)).symm
  · unfold mainTerm; congr 1; funext u; rw [kernel, ← tsum_mul_left]

end ZetaF
