/-
# Appendix A (L5): sums of `x^j/Γ(σ+j+1)` and the incomplete gamma function, uniformly in `σ`

Paper, Appendix A, §"Uniformity and memory", paragraphs "k-terms" and "Incomplete gamma functions".
All bounds are explicit in the size `S ≥ 2` of the parameter, in the form `e^{A S log S}` with an
absolute constant `A` (this is the paper's `2^{O(p)}` once `S log S = O(p)`).

* `SLogBound`: the class of functions `f` with `f(S) ≤ e^{A S log S}` for `S ≥ 2`, and its closure
  properties.
* `sum_rpow_div_Gamma_le`: `∑_m x^{c+m}/Γ(c+m+1) ≤ e^x` for real `c > 0` (this is `P(c,x) ≤ 1`).
* **(L5)** `sum_pow_mul_norm_inv_Gamma_le_sharp`:
  `∑_j x^j |1/Γ(σ+j+1)| ≤ e^{A S log S} max(1,x)^{-Re σ} e^x` for `|σ| ≤ S`, `x ≥ 0`,
  and the plan's form `sum_pow_mul_norm_inv_Gamma_le` with `(1+x)^S`.
* **(L5′)** `sum_pow_mul_norm_inv_Gamma_tail_le`, `norm_gammaPTerm_tail_uniform`: uniform tails of the
  incomplete gamma series.  NB: read with a constant uniform in `y`, the paper's bound
  `2^{O(p)} y^S e^y 2^{-i}` for the terms with `i ≥ 2y + 2S` is false (at `a = 0`, `i = 2y` the
  term `y^i/i!` is `≈ e^{(2-2log 2)y}`, while `e^y 2^{-i} = e^{(1-2 log 2)y}`); an extra factor `4^y`
  is needed (and suffices).  Since `y = O(p)` in the paper, `4^y = 2^{O(p)}` and the conclusion
  (`O(p)` terms, `O(p)` guard bits) is unaffected.
* **(L5″)** `norm_upperGamma_le`: `|Γ(w,x)| ≤ 2 x^{Re w - 1} e^{-x}` for `Re w ≤ x/2 + 1`.
-/
import ZetaF.GammaG1
import ZetaF.IncompleteGammaSeries
import Mathlib.Analysis.Complex.ExponentialBounds

open Finset Filter MeasureTheory Set
open scoped Real

namespace ZetaF.AppA

/-! ### Functions bounded by `e^{A S log S}` -/

/-- `f(S) ≤ e^{A S log S}` for all `S ≥ 2`, for some constant `A`. -/
def SLogBound (f : ℝ → ℝ) : Prop :=
  ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → f S ≤ Real.exp (A * S * Real.log S)

lemma half_le_log {S : ℝ} (hS : 2 ≤ S) : 1 / 2 ≤ Real.log S := by
  have h2 := Real.log_two_gt_d9
  have := Real.log_le_log (by norm_num) hS
  linarith

lemma one_le_mul_log {S : ℝ} (hS : 2 ≤ S) : 1 ≤ S * Real.log S := by
  have := half_le_log hS
  nlinarith

lemma mul_log_nonneg {S : ℝ} (hS : 2 ≤ S) : 0 ≤ S * Real.log S :=
  zero_le_one.trans (one_le_mul_log hS)

lemma le_two_mul_mul_log {S : ℝ} (hS : 2 ≤ S) : S ≤ 2 * (S * Real.log S) := by
  have := half_le_log hS
  nlinarith

/-- `(S+1) log(S+1) ≤ 3 S log S` for `S ≥ 2`. -/
lemma add_one_mul_log_le {S : ℝ} (hS : 2 ≤ S) :
    (S + 1) * Real.log (S + 1) ≤ 3 * (S * Real.log S) := by
  have h1 : Real.log (S + 1) ≤ 2 * Real.log S := by
    have h0 : S + 1 ≤ S ^ 2 := by nlinarith
    calc Real.log (S + 1) ≤ Real.log (S ^ 2) := Real.log_le_log (by linarith) h0
      _ = 2 * Real.log S := by rw [Real.log_pow]; norm_num
  have h2 := half_le_log hS
  have h3 : 0 ≤ Real.log (S + 1) := Real.log_nonneg (by linarith)
  nlinarith

lemma exp_mono_A {A A' S : ℝ} (hS : 2 ≤ S) (h : A ≤ A') :
    Real.exp (A * S * Real.log S) ≤ Real.exp (A' * S * Real.log S) := by
  rw [Real.exp_le_exp, mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right h (mul_log_nonneg hS)

namespace SLogBound

variable {f g : ℝ → ℝ}

lemma exists_nonneg (h : SLogBound f) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ S : ℝ, 2 ≤ S → f S ≤ Real.exp (A * S * Real.log S) := by
  obtain ⟨A, hA⟩ := h
  exact ⟨max A 0, le_max_right _ _, fun S hS => (hA S hS).trans (exp_mono_A hS (le_max_left _ _))⟩

lemma of_le (h : SLogBound g) (hfg : ∀ S : ℝ, 2 ≤ S → f S ≤ g S) : SLogBound f := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, fun S hS => (hfg S hS).trans (hA S hS)⟩

/-- `exp(α + β S + γ S log S)` is `e^{O(S log S)}`. -/
lemma exp_lin (α β γ : ℝ) :
    SLogBound fun S => Real.exp (α + β * S + γ * (S * Real.log S)) := by
  refine ⟨|α| + 2 * |β| + |γ|, fun S hS => ?_⟩
  rw [Real.exp_le_exp]
  have h1 := one_le_mul_log hS
  have h2 := le_two_mul_mul_log hS
  have hS0 : 0 ≤ S := by linarith
  have e1 : α ≤ |α| * (S * Real.log S) := (le_abs_self α).trans (le_mul_of_one_le_right
    (abs_nonneg _) h1)
  have e2 : β * S ≤ 2 * |β| * (S * Real.log S) := by
    calc β * S ≤ |β| * S := mul_le_mul_of_nonneg_right (le_abs_self _) hS0
      _ ≤ |β| * (2 * (S * Real.log S)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
      _ = _ := by ring
  have e3 : γ * (S * Real.log S) ≤ |γ| * (S * Real.log S) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) (mul_log_nonneg hS)
  have : (|α| + 2 * |β| + |γ|) * S * Real.log S =
      |α| * (S * Real.log S) + 2 * |β| * (S * Real.log S) + |γ| * (S * Real.log S) := by ring
  rw [this]; linarith

lemma const (c : ℝ) : SLogBound fun _ => c :=
  (exp_lin c 0 0).of_le fun S _ => by simpa using (Real.add_one_le_exp c).trans' (by linarith)

lemma add (hf : SLogBound f) (hg : SLogBound g) : SLogBound fun S => f S + g S := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨max A B + 1, fun S hS => ?_⟩
  have h1 := (hA S hS).trans (exp_mono_A hS (le_max_left A B))
  have h2 := (hB S hS).trans (exp_mono_A hS (le_max_right A B))
  have h3 : 2 ≤ Real.exp (S * Real.log S) := by
    have := Real.add_one_le_exp (S * Real.log S); linarith [one_le_mul_log hS]
  have : Real.exp ((max A B + 1) * S * Real.log S) =
      Real.exp (max A B * S * Real.log S) * Real.exp (S * Real.log S) := by
    rw [← Real.exp_add]; ring_nf
  rw [this]
  nlinarith [Real.exp_pos (max A B * S * Real.log S)]

lemma mul (hf : SLogBound f) (hg : SLogBound g) (hg0 : ∀ S : ℝ, 2 ≤ S → 0 ≤ g S) :
    SLogBound fun S => f S * g S := by
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  refine ⟨A + B, fun S hS => ?_⟩
  calc f S * g S ≤ Real.exp (A * S * Real.log S) * g S :=
        mul_le_mul_of_nonneg_right (hA S hS) (hg0 S hS)
    _ ≤ Real.exp (A * S * Real.log S) * Real.exp (B * S * Real.log S) :=
        mul_le_mul_of_nonneg_left (hB S hS) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; ring_nf

/-- `e^{A (S+1) log (S+1)} ≤ e^{3A S log S}` for `A ≥ 0`. -/
lemma shift {A : ℝ} (hA : 0 ≤ A) :
    SLogBound fun S => Real.exp (A * (S + 1) * Real.log (S + 1)) := by
  refine ⟨3 * A, fun S hS => ?_⟩
  rw [Real.exp_le_exp, mul_assoc, mul_assoc, mul_assoc]
  have := mul_le_mul_of_nonneg_left (add_one_mul_log_le hS) hA
  linarith

/-- `b^N ≤ e^{O(S log S)}` if `1 ≤ b ≤ cS` and `N ≤ dS + e`. -/
lemma pow_of_le {b : ℝ → ℝ} {N : ℝ → ℕ} {c d e : ℝ} (hc : 1 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hb1 : ∀ S : ℝ, 2 ≤ S → 1 ≤ b S) (hbc : ∀ S : ℝ, 2 ≤ S → b S ≤ c * S)
    (hN : ∀ S : ℝ, 2 ≤ S → (N S : ℝ) ≤ d * S + e) : SLogBound fun S => b S ^ N S := by
  refine (exp_lin (e * Real.log c) (d * Real.log c + e) d).of_le fun S hS => ?_
  have hb0 : 0 < b S := lt_of_lt_of_le one_pos (hb1 S hS)
  have hS0 : 0 < S := by linarith
  rw [← Real.exp_log (pow_pos hb0 _), Real.exp_le_exp, Real.log_pow]
  have hlb : 0 ≤ Real.log (b S) := Real.log_nonneg (hb1 S hS)
  have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlS : Real.log S ≤ S := (Real.log_le_sub_one_of_pos hS0).trans (by linarith)
  have hlS0 : 0 ≤ Real.log S := Real.log_nonneg (by linarith)
  have h1 : Real.log (b S) ≤ Real.log c + Real.log S := by
    rw [← Real.log_mul (by linarith) hS0.ne']
    exact Real.log_le_log hb0 (hbc S hS)
  calc (N S : ℝ) * Real.log (b S) ≤ (d * S + e) * (Real.log c + Real.log S) :=
        mul_le_mul (hN S hS) h1 hlb (by positivity)
    _ = e * Real.log c + d * Real.log c * S + d * (S * Real.log S) + e * Real.log S := by ring
    _ ≤ e * Real.log c + (d * Real.log c + e) * S + d * (S * Real.log S) := by nlinarith

end SLogBound

/-- The explicit bound of (G2) (`norm_inv_Gamma_le_G2`): `e · e^{πT/2} (2T+2)^{⌈T⌉+1}`. -/
noncomputable def G2bound (T : ℝ) : ℝ :=
  Real.exp 1 * Real.exp (π * T / 2) * (2 * T + 2) ^ (⌈T⌉₊ + 1)

lemma G2bound_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ G2bound T := by
  unfold G2bound; positivity

/-- (G2) on the disc of radius `pS + q` is `e^{O(S log S)}`. -/
lemma SLogBound.G2bound_lin (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    SLogBound fun S => ZetaF.AppA.G2bound (p * S + q) := by
  have h1 : SLogBound fun S => Real.exp 1 * Real.exp (π * (p * S + q) / 2) :=
    (SLogBound.exp_lin (1 + π * q / 2) (π * p / 2) 0).of_le fun S _ => by
      rw [← Real.exp_add]; apply le_of_eq; congr 1; ring
  have h2 : SLogBound fun S => (2 * (p * S + q) + 2) ^ (⌈p * S + q⌉₊ + 1) := by
    refine SLogBound.pow_of_le (c := 2 * p + 2 * q + 2) (d := p) (e := q + 2) (by linarith)
      hp (by linarith) (fun S _ => by nlinarith) (fun S _ => by nlinarith) fun S hS => ?_
    have := Nat.ceil_lt_add_one (show 0 ≤ p * S + q by nlinarith)
    push_cast; linarith
  exact (h1.mul h2 fun S hS => by have : 0 ≤ p * S + q := by nlinarith
                                  positivity).of_le fun S _ => le_of_eq (by unfold ZetaF.AppA.G2bound; ring)

/-! ### `∑ x^{c+m}/Γ(c+m+1) ≤ e^x` (i.e. `P(c, x) ≤ 1`) -/

lemma norm_lowerGamma_le_Gamma {c : ℝ} (hc : 0 < c) (x : ℝ) :
    ‖lowerGamma (c : ℂ) x‖ ≤ Real.Gamma c := by
  have hint := Real.GammaIntegral_convergent hc
  have hnorm : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ ((c : ℂ) - 1) * (Real.exp (-t) : ℂ)‖ =
      Real.exp (-t) * t ^ (c - 1) := by
    intro t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp [mul_comm]
  calc ‖lowerGamma (c : ℂ) x‖
      ≤ ∫ t in Ioc 0 x, ‖(t : ℂ) ^ ((c : ℂ) - 1) * (Real.exp (-t) : ℂ)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ t in Ioc 0 x, Real.exp (-t) * t ^ (c - 1) :=
        setIntegral_congr_fun measurableSet_Ioc fun t ht => hnorm t ht.1
    _ ≤ ∫ t in Ioi 0, Real.exp (-t) * t ^ (c - 1) := by
        apply setIntegral_mono_set hint
        · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
          exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (le_of_lt ht) _)
        · exact Eventually.of_forall Ioc_subset_Ioi_self
    _ = Real.Gamma c := (Real.Gamma_eq_integral hc).symm

lemma norm_one_sub_gammaQ_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 < x) :
    ‖1 - gammaQ (c : ℂ) x‖ ≤ 1 := by
  have hcre : 0 < (c : ℂ).re := by simpa using hc
  have hG := Gamma_eq_lower_add_upper hcre hx
  have hΓ : 0 < Real.Gamma c := Real.Gamma_pos_of_pos hc
  have hG0 : Complex.Gamma (c : ℂ) ≠ 0 := by
    rw [Complex.Gamma_ofReal]; exact_mod_cast hΓ.ne'
  have : 1 - gammaQ (c : ℂ) x = lowerGamma (c : ℂ) x * (Complex.Gamma (c : ℂ))⁻¹ := by
    rw [gammaQ, ← mul_inv_cancel₀ hG0, hG]; ring
  rw [this, norm_mul, norm_inv, Complex.Gamma_ofReal, Complex.norm_real,
    Real.norm_of_nonneg hΓ.le, ← div_eq_mul_inv, div_le_one hΓ]
  exact norm_lowerGamma_le_Gamma hc x

/-- `∑_{m ≥ 0} x^{c+m}/Γ(c+m+1) ≤ e^x` for real `c > 0`, `x ≥ 0` (this is `P(c,x) ≤ 1`). -/
theorem sum_rpow_div_Gamma_le {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun m : ℕ => x ^ (c + m) / Real.Gamma (c + m + 1)) ∧
      ∑' m : ℕ, x ^ (c + m) / Real.Gamma (c + m + 1) ≤ Real.exp x := by
  rcases eq_or_lt_of_le hx with rfl | hx
  · have h0 : (fun m : ℕ => (0 : ℝ) ^ (c + m) / Real.Gamma (c + m + 1)) = fun _ => 0 := by
      funext m; rw [Real.zero_rpow (by positivity), zero_div]
    rw [h0]; exact ⟨summable_zero, by simp⟩
  set t : ℕ → ℝ := fun m => x ^ (c + m) * Real.exp (-x) / Real.Gamma (c + m + 1) with ht
  have heq : ∀ m : ℕ, gammaPTerm (c : ℂ) x m = ((t m : ℝ) : ℂ) := by
    intro m
    have h1 : ((c : ℂ) + m + 1) = ((c + m + 1 : ℝ) : ℂ) := by push_cast; ring
    have h2 : ((c : ℂ) + m) = ((c + m : ℝ) : ℂ) := by push_cast; ring
    rw [gammaPTerm, h1, h2, Complex.Gamma_ofReal, ← Complex.ofReal_cpow hx.le]
    simp only [ht]; push_cast; ring
  have hs : HasSum (fun m => ((t m : ℝ) : ℂ)) (1 - gammaQ (c : ℂ) x) := by
    have := hasSum_gammaPTerm (c : ℂ) hx
    rwa [show gammaPTerm (c : ℂ) x = fun m => ((t m : ℝ) : ℂ) from funext heq] at this
  have hre : HasSum t (1 - gammaQ (c : ℂ) x).re := by
    simpa using Complex.hasSum_re hs
  have hle : (1 - gammaQ (c : ℂ) x).re ≤ 1 :=
    (Complex.re_le_norm _).trans (norm_one_sub_gammaQ_le hc hx)
  have hfun : (fun m : ℕ => x ^ (c + m) / Real.Gamma (c + m + 1)) =
      fun m => Real.exp x * t m := by
    funext m; simp only [ht]
    rw [mul_div_assoc', mul_comm (Real.exp x), mul_assoc, ← Real.exp_add]; simp
  rw [hfun]
  refine ⟨hre.summable.mul_left _, ?_⟩
  rw [tsum_mul_left, hre.tsum_eq]
  exact mul_le_of_le_one_right (Real.exp_pos _).le hle


/-! ### (L5): `∑_j x^j |1/Γ(σ+j+1)|` -/

/-- (G1) in the form used below: `|1/Γ(w)| ≤ e^{π|Im w|/2}/Γ(Re w)` for `Re w ≥ 1/2`. -/
lemma norm_inv_Gamma_le_G1' {w : ℂ} (hw : 1 / 2 ≤ w.re) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ Real.exp (π * |w.im| / 2) / Real.Gamma w.re := by
  have h := norm_inv_Gamma_le_G1 hw w.im
  rwa [show ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w from Complex.re_add_im w] at h

/-- The index `J` from which on `Re(σ + j + 1) ≥ 1`, chosen so that `c = Re σ + J > 0` and
`j ≤ -Re σ` for `j < J`. -/
noncomputable def splitIdx (τ : ℝ) : ℕ := if 0 < τ then 0 else ⌊-τ⌋₊ + 1

lemma splitIdx_pos (τ : ℝ) : 0 < τ + splitIdx τ := by
  unfold splitIdx
  split_ifs with h
  · simpa using h
  · have := Nat.lt_floor_add_one (-τ); push_cast; linarith

lemma le_of_lt_splitIdx {τ : ℝ} {j : ℕ} (hj : j < splitIdx τ) : (j : ℝ) ≤ -τ := by
  unfold splitIdx at hj
  split_ifs at hj with h
  · omega
  · have h1 : j ≤ ⌊-τ⌋₊ := by omega
    have h2 := Nat.floor_le (show 0 ≤ -τ by linarith)
    exact (Nat.cast_le.2 h1).trans h2

lemma splitIdx_le {τ S : ℝ} (hS : 0 ≤ S) (hτ : -S ≤ τ) : (splitIdx τ : ℝ) ≤ S + 1 := by
  unfold splitIdx
  split_ifs with h
  · push_cast; linarith
  · have := Nat.floor_le (show 0 ≤ -τ by linarith); push_cast; linarith

/-- The constant of (L5) before simplification. -/
noncomputable def L5const (S : ℝ) : ℝ :=
  (S + 1) * G2bound (2 * S + 1) + Real.exp 1 * Real.exp (π * S / 2)

lemma SLogBound.L5const : SLogBound L5const := by
  refine (((SLogBound.exp_lin 0 1 0).mul (SLogBound.G2bound_lin 2 1 (by norm_num) (by norm_num))
    fun S hS => G2bound_nonneg (by linarith)).add
    ((SLogBound.exp_lin (1 : ℝ) (π / 2) 0))).of_le fun S hS => ?_
  unfold ZetaF.AppA.L5const
  have h1 : S + 1 ≤ Real.exp (0 + 1 * S + 0 * (S * Real.log S)) := by
    simpa [add_comm] using Real.add_one_le_exp S
  have h2 : Real.exp 1 * Real.exp (π * S / 2) =
      Real.exp (1 + π / 2 * S + 0 * (S * Real.log S)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  gcongr
  · exact G2bound_nonneg (by linarith)

/-- The core estimate of (L5), with the constant `L5const S`. -/
theorem sum_pow_mul_norm_inv_Gamma_le_aux {S : ℝ} (hS : 0 ≤ S) {σ : ℂ} (hσ : ‖σ‖ ≤ S)
    {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        L5const S * max 1 x ^ (-σ.re) * Real.exp x := by
  set τ := σ.re with hτ
  set J := splitIdx τ with hJ
  set c := τ + J with hc
  have hc0 : 0 < c := splitIdx_pos τ
  have hτS : |τ| ≤ S := (Complex.abs_re_le_norm σ).trans hσ
  have hτS' := abs_le.1 hτS
  have him : |σ.im| ≤ S := (Complex.abs_im_le_norm σ).trans hσ
  set f : ℕ → ℝ := fun j => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ with hf
  set B := max 1 x with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hBτ : 0 < B ^ (-τ) := Real.rpow_pos_of_pos hBpos _
  have hex : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hf0 : ∀ j, 0 ≤ f j := fun j => by positivity
  -- the terms `j ≥ J`, by (G1)
  have hG1 : ∀ m : ℕ, ‖(Complex.Gamma (σ + ((m + J : ℕ) : ℂ) + 1))⁻¹‖ ≤
      Real.exp (π * S / 2) / Real.Gamma (c + m + 1) := by
    intro m
    have hre : (σ + ((m + J : ℕ) : ℂ) + 1).re = c + m + 1 := by
      simp [hc, hτ]; ring
    have hw : 1 / 2 ≤ (σ + ((m + J : ℕ) : ℂ) + 1).re := by
      rw [hre]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith
    refine (norm_inv_Gamma_le_G1' hw).trans ?_
    rw [hre]
    have hΓ := Real.Gamma_pos_of_pos (show 0 < c + m + 1 by positivity)
    gcongr
    simpa using him
  obtain ⟨hA1, hA2⟩ := sum_rpow_div_Gamma_le hc0 hx
  obtain ⟨hA1', hA2'⟩ := sum_rpow_div_Gamma_le hc0 zero_le_one
  simp only [Real.one_rpow] at hA1' hA2'
  have htail : Summable (fun m : ℕ => f (m + J)) ∧
      ∑' m : ℕ, f (m + J) ≤ Real.exp 1 * Real.exp (π * S / 2) * B ^ (-τ) * Real.exp x := by
    rcases le_or_gt 1 x with hx1 | hx1
    · have hxB : B = x := max_eq_right hx1
      have hx0 : 0 < x := by linarith
      have hle : ∀ m : ℕ, f (m + J) ≤ Real.exp (π * S / 2) * x ^ (-τ) *
          (x ^ (c + m) / Real.Gamma (c + m + 1)) := by
        intro m
        have hpow : x ^ (m + J) = x ^ (-τ) * x ^ (c + m) := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hx0]; congr 1; push_cast [hc]; ring
        simp only [hf]
        rw [hpow]
        calc x ^ (-τ) * x ^ (c + m) * ‖(Complex.Gamma (σ + ((m + J : ℕ) : ℂ) + 1))⁻¹‖
            ≤ x ^ (-τ) * x ^ (c + m) * (Real.exp (π * S / 2) / Real.Gamma (c + m + 1)) :=
              mul_le_mul_of_nonneg_left (hG1 m) (by positivity)
          _ = _ := by ring
      have hs := hA1.mul_left (Real.exp (π * S / 2) * x ^ (-τ))
      refine ⟨Summable.of_nonneg_of_le (fun m => hf0 _) hle hs, ?_⟩
      calc ∑' m : ℕ, f (m + J) ≤ ∑' m : ℕ, Real.exp (π * S / 2) * x ^ (-τ) *
            (x ^ (c + m) / Real.Gamma (c + m + 1)) :=
            Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun m => hf0 _) hle hs) hs
        _ ≤ Real.exp (π * S / 2) * x ^ (-τ) * Real.exp x := by
            rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hA2 (by positivity)
        _ ≤ _ := by
            rw [hxB]
            have : 0 ≤ Real.exp (π * S / 2) * x ^ (-τ) * Real.exp x := by positivity
            have h1 := Real.add_one_le_exp 1
            nlinarith
    · have hxB : B = 1 := max_eq_left hx1.le
      have hle : ∀ m : ℕ, f (m + J) ≤ Real.exp (π * S / 2) * (1 / Real.Gamma (c + m + 1)) := by
        intro m
        simp only [hf]
        have hxp : x ^ (m + J) ≤ 1 := pow_le_one₀ hx hx1.le
        calc x ^ (m + J) * ‖(Complex.Gamma (σ + ((m + J : ℕ) : ℂ) + 1))⁻¹‖
            ≤ 1 * (Real.exp (π * S / 2) / Real.Gamma (c + m + 1)) :=
              mul_le_mul hxp (hG1 m) (norm_nonneg _) zero_le_one
          _ = _ := by ring
      have hs := hA1'.mul_left (Real.exp (π * S / 2))
      refine ⟨Summable.of_nonneg_of_le (fun m => hf0 _) hle hs, ?_⟩
      calc ∑' m : ℕ, f (m + J) ≤ ∑' m : ℕ, Real.exp (π * S / 2) * (1 / Real.Gamma (c + m + 1)) :=
            Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun m => hf0 _) hle hs) hs
        _ ≤ Real.exp (π * S / 2) * Real.exp 1 := by
            rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hA2' (by positivity)
        _ ≤ _ := by
            rw [hxB, Real.one_rpow, mul_one]
            have : 0 ≤ Real.exp (π * S / 2) * Real.exp 1 := by positivity
            nlinarith
  -- the terms `j < J`, by (G2)
  have hhead : ∀ j ∈ range J, f j ≤ G2bound (2 * S + 1) * B ^ (-τ) := by
    intro j hj
    have hjJ := le_of_lt_splitIdx (mem_range.1 hj)
    have hxj : x ^ j ≤ B ^ (-τ) := by
      rcases le_or_gt 1 x with hx1 | hx1
      · rw [hB, max_eq_right hx1, ← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx1 hjJ
      · rw [hB, max_eq_left hx1.le, Real.one_rpow]; exact pow_le_one₀ hx hx1.le
    have hnorm : ‖σ + j + 1‖ ≤ 2 * S + 1 := by
      calc ‖σ + j + 1‖ ≤ ‖σ‖ + ‖(j : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add₃_le
        _ ≤ S + S + 1 := by
            rw [Complex.norm_natCast, norm_one]; linarith
        _ = 2 * S + 1 := by ring
    have hG2 := norm_inv_Gamma_le_G2 (by linarith) hnorm
    simp only [hf]
    calc x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤ B ^ (-τ) * G2bound (2 * S + 1) :=
          mul_le_mul hxj hG2 (norm_nonneg _) hBτ.le
      _ = _ := mul_comm _ _
  have hsum : Summable f := (summable_nat_add_iff J).1 htail.1
  refine ⟨hsum, ?_⟩
  rw [← hsum.sum_add_tsum_nat_add J]
  have hJS := splitIdx_le hS hτS'.1
  have hG0 := G2bound_nonneg (show 0 ≤ 2 * S + 1 by linarith)
  calc ∑ j ∈ range J, f j + ∑' m : ℕ, f (m + J)
      ≤ ∑ _j ∈ range J, G2bound (2 * S + 1) * B ^ (-τ) +
          Real.exp 1 * Real.exp (π * S / 2) * B ^ (-τ) * Real.exp x :=
        add_le_add (sum_le_sum hhead) htail.2
    _ = J * G2bound (2 * S + 1) * B ^ (-τ) +
          Real.exp 1 * Real.exp (π * S / 2) * B ^ (-τ) * Real.exp x := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ (S + 1) * G2bound (2 * S + 1) * B ^ (-τ) * Real.exp x +
          Real.exp 1 * Real.exp (π * S / 2) * B ^ (-τ) * Real.exp x := by
        apply add_le_add_left ?_ _
        calc (J : ℝ) * G2bound (2 * S + 1) * B ^ (-τ)
            ≤ (S + 1) * G2bound (2 * S + 1) * B ^ (-τ) := by gcongr
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hex
    _ = L5const S * B ^ (-τ) * Real.exp x := by unfold L5const; ring

/-- **(L5), sharp form.** There is an absolute constant `A` such that for `S ≥ 2`, `|σ| ≤ S`
and `x ≥ 0`, `∑_j x^j |1/Γ(σ+j+1)| ≤ e^{A S log S} max(1,x)^{-Re σ} e^x`.
(Paper: "`∑_j x^j |1/Γ(s/2+j+1)| ≤ 2^{O(p)} x^S e^x`", A.9 "k-terms".) -/
theorem sum_pow_mul_norm_inv_Gamma_le_sharp :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * max 1 x ^ (-σ.re) * Real.exp x := by
  obtain ⟨A, hA⟩ := SLogBound.L5const
  refine ⟨A, fun S hS σ hσ x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sum_pow_mul_norm_inv_Gamma_le_aux (by linarith) hσ hx
  refine ⟨h1, h2.trans ?_⟩
  have : 0 ≤ max 1 x ^ (-σ.re) * Real.exp x :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _) (Real.exp_pos _).le
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right (hA S hS) this

lemma max_one_rpow_neg_re_le {S : ℝ} (hS : 0 ≤ S) {σ : ℂ} (hσ : ‖σ‖ ≤ S) {x : ℝ} (hx : 0 ≤ x) :
    max 1 x ^ (-σ.re) ≤ (1 + x) ^ S := by
  have hτ : -σ.re ≤ S := by
    have := (Complex.abs_re_le_norm σ).trans hσ; have := neg_abs_le σ.re; linarith
  rcases le_or_gt 1 x with hx1 | hx1
  · rw [max_eq_right hx1]
    calc x ^ (-σ.re) ≤ x ^ S := Real.rpow_le_rpow_of_exponent_le hx1 hτ
      _ ≤ (1 + x) ^ S := Real.rpow_le_rpow (by linarith) (by linarith) hS
  · rw [max_eq_left hx1.le, Real.one_rpow]
    exact Real.one_le_rpow (by linarith) hS

/-- **(L5)** (plan's form): `∑_j x^j |1/Γ(σ+j+1)| ≤ e^{A S log S} (1+x)^S e^x` for `S ≥ 2`,
`|σ| ≤ S`, `x ≥ 0`. -/
theorem sum_pow_mul_norm_inv_Gamma_le :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ σ : ℂ, ‖σ‖ ≤ S → ∀ x : ℝ, 0 ≤ x →
      Summable (fun j : ℕ => x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖) ∧
      ∑' j : ℕ, x ^ j * ‖(Complex.Gamma (σ + j + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * (1 + x) ^ S * Real.exp x := by
  obtain ⟨A, hA⟩ := sum_pow_mul_norm_inv_Gamma_le_sharp
  refine ⟨A, fun S hS σ hσ x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hA S hS σ hσ x hx
  refine ⟨h1, h2.trans ?_⟩
  gcongr
  exact max_one_rpow_neg_re_le (by linarith) hσ hx

/-! ### (L5′): uniform tails of the incomplete gamma series -/

/-- Ratio step: if `|a + i + 1| ≥ 2y` then `2 y^{i+1}|1/Γ(a+i+2)| ≤ y^i |1/Γ(a+i+1)|`. -/
lemma two_mul_pow_succ_norm_inv_Gamma_le {a : ℂ} {y : ℝ} (hy : 0 ≤ y) {i : ℕ}
    (hi : 2 * y ≤ ‖a + i + 1‖) :
    2 * (y ^ (i + 1) * ‖(Complex.Gamma (a + ((i + 1 : ℕ) : ℂ) + 1))⁻¹‖) ≤
      y ^ i * ‖(Complex.Gamma (a + i + 1))⁻¹‖ := by
  have h := congrArg norm (mul_inv_Gamma_add_one (a + i + 1))
  rw [norm_mul] at h
  have e : a + ((i + 1 : ℕ) : ℂ) + 1 = a + i + 1 + 1 := by push_cast; ring
  rw [e, ← h, pow_succ]
  have := mul_le_mul_of_nonneg_right hi (norm_nonneg (Complex.Gamma (a + i + 1 + 1))⁻¹)
  have hyi : 0 ≤ y ^ i := pow_nonneg hy i
  nlinarith [mul_le_mul_of_nonneg_left this hyi]

/-- **(L5′), inner sums.** For `S ≥ 2`, `|a| ≤ S`, `y ≥ 0` and `N ≥ 2y + 2S`:
`∑_{i ≥ N} y^i |1/Γ(a+i+1)| ≤ e^{A S log S} (1+y)^S e^y 4^y 2^{-N}`.
(The paper's "`≤ 2^{O(p)} y^S e^y 2^{-i}` for `i ≥ 2y+2S`" needs the factor `4^y`, which is
`2^{O(p)}` only because `y = O(p)`; the plan's version without it is false for large `y`.) -/
theorem sum_pow_mul_norm_inv_Gamma_tail_le :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ a : ℂ, ‖a‖ ≤ S → ∀ y : ℝ, 0 ≤ y → ∀ N : ℕ,
      2 * y + 2 * S ≤ N →
      Summable (fun i : ℕ => y ^ (i + N) * ‖(Complex.Gamma (a + ((i + N : ℕ) : ℂ) + 1))⁻¹‖) ∧
      ∑' i : ℕ, y ^ (i + N) * ‖(Complex.Gamma (a + ((i + N : ℕ) : ℂ) + 1))⁻¹‖ ≤
        Real.exp (A * S * Real.log S) * (1 + y) ^ S * Real.exp y * 4 ^ y * (1 / 2) ^ N := by
  obtain ⟨A₀, hA₀⟩ := sum_pow_mul_norm_inv_Gamma_le
  obtain ⟨A, hA⟩ := (SLogBound.exp_lin (2 * Real.log 4) (Real.log 4) 0).mul
    (show SLogBound fun S => Real.exp (A₀ * S * Real.log S) from ⟨A₀, fun _ _ => le_rfl⟩)
    (fun _ _ => (Real.exp_pos _).le)
  refine ⟨A, fun S hS a ha y hy N hN => ?_⟩
  set r : ℕ → ℝ := fun i => y ^ i * ‖(Complex.Gamma (a + i + 1))⁻¹‖ with hr
  have hr0 : ∀ i, 0 ≤ r i := fun i => by positivity
  obtain ⟨hsr, hsr'⟩ := hA₀ S hS a ha y hy
  set N₀ := ⌈2 * y + 2 * S⌉₊ with hN₀
  have hN₀N : N₀ ≤ N := Nat.ceil_le.2 hN
  have hN₀' : (N₀ : ℝ) ≤ 2 * y + 2 * S + 1 :=
    (Nat.ceil_lt_add_one (by linarith)).le
  have hare : -S ≤ a.re := by
    have := (Complex.abs_re_le_norm a).trans ha; have := neg_abs_le a.re; linarith
  have hstep : ∀ i, N₀ ≤ i → 2 * r (i + 1) ≤ r i := by
    intro i hi
    have hi' : (N₀ : ℝ) ≤ i := Nat.cast_le.2 hi
    have h1 := Nat.le_ceil (2 * y + 2 * S)
    have hre : 2 * y ≤ ‖a + i + 1‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp; linarith
    have := two_mul_pow_succ_norm_inv_Gamma_le hy hre
    simpa [hr] using this
  have hgeom : ∀ i, r (i + N₀) ≤ r N₀ * (1 / 2) ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := hstep (i + N₀) (Nat.le_add_left _ _)
      rw [show i + 1 + N₀ = i + N₀ + 1 by ring, pow_succ]
      linarith
  set d := N - N₀ with hd
  have hNd : N = d + N₀ := by omega
  have hle : ∀ i, r (i + N) ≤ r N₀ * (1 / 2) ^ d * (1 / 2) ^ i := by
    intro i
    rw [hNd, ← add_assoc, mul_assoc, ← pow_add, add_comm d i]
    exact hgeom (i + d)
  have hgs : Summable fun i : ℕ => r N₀ * (1 / 2) ^ d * (1 / 2) ^ i :=
    summable_geometric_two.mul_left _
  have hfun : (fun i : ℕ => y ^ (i + N) * ‖(Complex.Gamma (a + ((i + N : ℕ) : ℂ) + 1))⁻¹‖) =
      fun i => r (i + N) := rfl
  rw [hfun]
  have hs : Summable fun i => r (i + N) := Summable.of_nonneg_of_le (fun i => hr0 _) hle hgs
  refine ⟨hs, ?_⟩
  have hrN₀ : r N₀ ≤ Real.exp (A₀ * S * Real.log S) * (1 + y) ^ S * Real.exp y :=
    (hsr.le_tsum N₀ fun i _ => hr0 i).trans hsr'
  have h2N : (1 / 2 : ℝ) ^ d = 2 ^ N₀ * (1 / 2) ^ N := by
    rw [hNd, pow_add, ← mul_assoc, mul_comm, ← mul_assoc, ← mul_pow]; norm_num
  have h2N₀ : (2 : ℝ) ^ N₀ ≤ 2 * Real.exp (Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S)) *
      4 ^ y := by
    rw [← Real.rpow_natCast]
    calc (2 : ℝ) ^ (N₀ : ℝ) ≤ 2 ^ (2 * y + 2 * S + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hN₀'
      _ = 2 * 4 ^ S * 4 ^ y := by
          rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), Real.rpow_one,
            Real.rpow_mul (by norm_num), Real.rpow_mul (by norm_num)]
          norm_num; ring
      _ ≤ _ := by
          gcongr
          rw [Real.rpow_def_of_pos (by norm_num)]
          apply Real.exp_le_exp.2
          have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          nlinarith
  have hE := hA S hS
  calc ∑' i, r (i + N) ≤ ∑' i : ℕ, r N₀ * (1 / 2) ^ d * (1 / 2) ^ i :=
        Summable.tsum_le_tsum hle hs hgs
    _ = 2 * r N₀ * (1 / 2) ^ d := by rw [tsum_mul_left, tsum_geometric_two]; ring
    _ ≤ 2 * (Real.exp (A₀ * S * Real.log S) * (1 + y) ^ S * Real.exp y) *
          (2 * Real.exp (Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S)) * 4 ^ y *
            (1 / 2) ^ N) := by
        rw [h2N]; gcongr
    _ = (4 * Real.exp (Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S))) *
          Real.exp (A₀ * S * Real.log S) * (1 + y) ^ S * Real.exp y * 4 ^ y *
            (1 / 2) ^ N := by ring
    _ = (Real.exp (2 * Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S)) *
          Real.exp (A₀ * S * Real.log S)) * (1 + y) ^ S * Real.exp y * 4 ^ y *
            (1 / 2) ^ N := by
        congr 1; congr 1; congr 1; congr 1; congr 1
        rw [show 2 * Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S) =
          Real.log 4 + (Real.log 4 + Real.log 4 * S + 0 * (S * Real.log S)) by ring,
          Real.exp_add (Real.log 4), Real.exp_log (by norm_num)]
    _ ≤ _ := by gcongr

/-- **(L5′)** for the terms `t_i = y^{a+i} e^{-y}/Γ(a+i+1)` of `P(a, y)` (`gammaPTerm`): for
`S ≥ 2`, `|a| ≤ S`, `y > 0` and `N ≥ 2y + 2S`, the tail `∑_{i ≥ N} t_i` is at most
`e^{A S log S} y^{Re a} (1+y)^S 4^y 2^{-N}`. -/
theorem norm_gammaPTerm_tail_uniform :
    ∃ A : ℝ, ∀ S : ℝ, 2 ≤ S → ∀ a : ℂ, ‖a‖ ≤ S → ∀ y : ℝ, 0 < y → ∀ N : ℕ,
      2 * y + 2 * S ≤ N →
      ‖∑' i : ℕ, gammaPTerm a y (i + N)‖ ≤
        Real.exp (A * S * Real.log S) * y ^ a.re * (1 + y) ^ S * 4 ^ y * (1 / 2) ^ N := by
  obtain ⟨A, hA⟩ := sum_pow_mul_norm_inv_Gamma_tail_le
  refine ⟨A, fun S hS a ha y hy N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hA S hS a ha y hy.le N hN
  have hnorm : ∀ i : ℕ, ‖gammaPTerm a y (i + N)‖ = y ^ a.re * Real.exp (-y) *
      (y ^ (i + N) * ‖(Complex.Gamma (a + ((i + N : ℕ) : ℂ) + 1))⁻¹‖) := by
    intro i
    rw [gammaPTerm, norm_mul, norm_mul, cpow_ofReal_norm hy, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    have : (a + ((i + N : ℕ) : ℂ)).re = a.re + ((i + N : ℕ) : ℝ) := by simp
    rw [this, Real.rpow_add hy, Real.rpow_natCast]; ring
  have hs := h1.mul_left (y ^ a.re * Real.exp (-y))
  refine (tsum_of_norm_bounded hs.hasSum fun i => (hnorm i).le).trans ?_
  rw [tsum_mul_left]
  calc y ^ a.re * Real.exp (-y) * ∑' i : ℕ, y ^ (i + N) *
        ‖(Complex.Gamma (a + ((i + N : ℕ) : ℂ) + 1))⁻¹‖
      ≤ y ^ a.re * Real.exp (-y) * (Real.exp (A * S * Real.log S) * (1 + y) ^ S * Real.exp y *
          4 ^ y * (1 / 2) ^ N) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by
        have : Real.exp (-y) * Real.exp y = 1 := by rw [← Real.exp_add]; simp
        linear_combination (Real.exp (A * S * Real.log S) * y ^ a.re * (1 + y) ^ S * 4 ^ y *
          (1 / 2) ^ N) * this

/-! ### (L5″): the upper incomplete gamma function -/

/-- **(L5″)** `|Γ(w, x)| ≤ 2 x^{Re w - 1} e^{-x}` for `x > 0` and `Re w ≤ x/2 + 1`.
(Paper, A.9 "Incomplete gamma functions": `|Γ(w,N)| ≤ N^{3S} e^{-N}`, which follows for
`Re w ≤ 3S`, `N ≥ max(2, 6S)`.) -/
theorem norm_upperGamma_le {w : ℂ} {x : ℝ} (hx : 0 < x) (hw : w.re ≤ x / 2 + 1) :
    ‖upperGamma w x‖ ≤ 2 * x ^ (w.re - 1) * Real.exp (-x) := by
  set r := w.re - 1 with hr
  set g : ℝ → ℝ := fun t => x ^ r * Real.exp (-(x / 2)) * Real.exp (-(1 / 2) * t) with hg
  have hgi : IntegrableOn g (Ioi x) :=
    (integrableOn_exp_mul_Ioi (by norm_num : -(1 / 2 : ℝ) < 0) x).const_mul _
  have hbound : ∀ t ∈ Ioi x, ‖(t : ℂ) ^ (w - 1) * (Real.exp (-t) : ℂ)‖ ≤ g t := by
    intro t ht
    have ht0 : 0 < t := hx.trans ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    simp only [Complex.sub_re, Complex.one_re, hg]
    rw [← hr, Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos hx, mul_assoc, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    have hlog : Real.log t - Real.log x ≤ (t - x) / x := by
      rw [← Real.log_div ht0.ne' hx.ne']
      have := Real.log_le_sub_one_of_pos (div_pos ht0 hx)
      rw [sub_div, div_self hx.ne']; linarith
    have hlog0 : 0 ≤ Real.log t - Real.log x :=
      sub_nonneg.2 (Real.log_le_log hx (le_of_lt ht))
    have htx : 0 ≤ t - x := by linarith [show x < t from ht]
    rcases le_or_gt r 0 with hr0 | hr0
    · nlinarith
    · have h1 : r * (Real.log t - Real.log x) ≤ r * ((t - x) / x) :=
        mul_le_mul_of_nonneg_left hlog hr0.le
      have h2 : r * ((t - x) / x) ≤ (x / 2) * ((t - x) / x) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_nonneg htx hx.le)
      have h3 : (x / 2) * ((t - x) / x) = (t - x) / 2 := by field_simp
      nlinarith
  calc ‖upperGamma w x‖ ≤ ∫ t in Ioi x, g t :=
        norm_integral_le_of_norm_le hgi
          ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hbound))
    _ = 2 * x ^ r * Real.exp (-x) := by
        simp only [hg]
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num) x]
        have : Real.exp (-(x / 2)) * Real.exp (-(1 / 2) * x) = Real.exp (-x) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [neg_div_neg_eq]
        calc x ^ r * Real.exp (-(x / 2)) * (Real.exp (-(1 / 2) * x) / (1 / 2))
            = 2 * x ^ r * (Real.exp (-(x / 2)) * Real.exp (-(1 / 2) * x)) := by ring
          _ = _ := by rw [this]

end ZetaF.AppA
