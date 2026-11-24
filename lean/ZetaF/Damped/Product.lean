/-
# The damped zeta function of a regular `F`: termwise forms (Proposition 4.3)

For `F(x) = ∑ a_n x^{-n}` with `|a_n| ≤ C R^n` the kernel of `e^{-τx^r} F(x) x^{-s}` is obtained by
summing the kernels of `e^{-τx^r} x^{-s-n}` (Section 4.2) against `a_n`:
`h(u) = ∑_{n,j} a_n c_{n,j} u^{a_{n,j} - 1}`, `a_{n,j} = (s + n - rj)/2`,
`c_{n,j} = (-τ)^j/(j! Γ(a_{n,j}))`.  The paper writes this as `∑_ℓ b_ℓ u^{w_ℓ-1}/Γ(w_ℓ)` with
`ℓ = qn - j` (for `r = 1/q`), a rearrangement of the double series.

We prove that the termwise `k`-term and dual-term integrals are absolutely summable over `ℕ × ℕ`:
* `hasSum_kTerm_prod`: `I_k = ∑_{n,j} a_n c_{n,j} ∫_{u₀}^∞ e^{-k²u} u^{a_{n,j}-1}` for `0 < r < 2`,
  `k > R`;
* `hasSum_dualTerm_prod`: `J_m = ∑_{n,j} a_n c_{n,j} D_{a_{n,j}-1/2}(π²m²)` for `0 < r < 1`, `m ≥ 1`.

The estimates are uniform in `n`.  Writing `x = Re a_{n,j}`:
* for `x < 1/2` we use the reflection bound `|1/Γ(a)| ≤ Γ(1-x) e^{π|Im a|}/π`; there
  `n < 1 - Re s + rj`, so `R^n` is absorbed into a geometric factor in `j`, and
  `Γ(1 - x) ≤ √π + |Γ(1 - Re s/2 + rj/2)|` by convexity;
* for `x ≥ 1/2` we use `1/Γ(a) = a/Γ(a+1)` and the uniform bound on `Γ(Re w)|1/Γ(w)|`,
  `Re w ≥ 1` (`gammaRatio_bounded`).  For the `k`-terms the factor `Γ(x)` from
  `∫_{u₀}^∞ e^{-k²u}u^{x-1} ≤ Γ(x)k^{-2x}` cancels it and `k > R` gives a geometric series in `n`;
  for the dual terms `∫₀^{u₀} u^{x-3/2}e^{-c/u} ≤ u₀^{x+1/2}/c`, and the decay of `1/Γ(x+1)` beats
  every geometric factor: `(λu₀)^x ≤ e^{λu₀}Γ(x+1)`.
-/
import ZetaF.Damped.Kernel
import ZetaF.Regular

open MeasureTheory Set Filter
open scoped Real Nat Topology

namespace ZetaF

/-! ### Real-variable auxiliaries -/

lemma rpow_lin_split {b : ℝ} (hb : 0 < b) (α β γ : ℝ) (n j : ℕ) :
    b ^ (α + β * n + γ * j) = b ^ α * (b ^ β) ^ n * (b ^ γ) ^ j := by
  rw [Real.rpow_add hb, Real.rpow_add hb, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul hb.le, ← Real.rpow_mul hb.le]

/-- `Γ(y) ≤ Γ(lo) + |Γ(hi)|` for `0 < lo ≤ y ≤ hi` (convexity of `Γ`). -/
lemma Gamma_le_of_mem_Icc {lo y hi : ℝ} (hlo : 0 < lo) (h1 : lo ≤ y) (h2 : y ≤ hi) :
    Real.Gamma y ≤ Real.Gamma lo + |Real.Gamma hi| := by
  have h := Real.convexOn_Gamma.le_max_of_mem_Icc (x := lo) (y := hi) (z := y)
    (show lo ∈ Ioi (0 : ℝ) from hlo) (show hi ∈ Ioi (0 : ℝ) from by simp; linarith) ⟨h1, h2⟩
  have hp := Real.Gamma_pos_of_pos hlo
  refine h.trans (max_le (by linarith [abs_nonneg (Real.Gamma hi)]) ?_)
  linarith [le_abs_self (Real.Gamma hi)]

/-- `(Rv)^n ≤ (1/2)^n L^E` for `n ≤ E`, `L = 2 max(1, Rv)`. -/
lemma geom_absorb {R v E : ℝ} (hR : 0 ≤ R) (hv : 0 ≤ v) {n : ℕ} (hn : (n : ℝ) ≤ E) :
    R ^ n * v ^ n ≤ (1 / 2) ^ n * (2 * max 1 (R * v)) ^ E := by
  set L := 2 * max 1 (R * v)
  have hL : 1 ≤ L := by simp only [L]; linarith [le_max_left 1 (R * v)]
  calc R ^ n * v ^ n = (R * v) ^ n := (mul_pow _ _ _).symm
    _ ≤ (1 / 2 * L) ^ n :=
        pow_le_pow_left₀ (by positivity) (by simp only [L]; linarith [le_max_right 1 (R * v)]) n
    _ = (1 / 2) ^ n * L ^ (n : ℝ) := by rw [mul_pow, Real.rpow_natCast]
    _ ≤ (1 / 2) ^ n * L ^ E :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hn) (by positivity)

/-- `(x + Y) u₀^x / Γ(x+1) ≤ (1 + Y) e^{μ² e u₀} μ^{-2x}` for `x > 0`. -/
lemma mul_rpow_div_Gamma_le {x Y u₀ μ : ℝ} (hx : 0 < x) (hY : 0 ≤ Y) (hu₀ : 0 < u₀)
    (hμ : 0 < μ) :
    (x + Y) * u₀ ^ x / Real.Gamma (x + 1) ≤
      (1 + Y) * rexp (μ ^ 2 * rexp 1 * u₀) * μ ^ (-(2 * x)) := by
  have hΓ : 0 < Real.Gamma (x + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h1 : x + Y ≤ (1 + Y) * rexp x := by
    have := Real.add_one_le_exp x
    nlinarith [Real.exp_pos x]
  have h2 := rpow_le_exp_mul_Gamma hx (show 0 ≤ μ ^ 2 * rexp 1 * u₀ by positivity)
  have e : (μ ^ 2 * rexp 1 * u₀) ^ x = μ ^ (2 * x) * (rexp x * u₀ ^ x) := by
    rw [Real.mul_rpow (by positivity) hu₀.le, Real.mul_rpow (by positivity) (Real.exp_pos _).le,
      Real.exp_one_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hμ.le]
    push_cast; ring
  rw [e] at h2
  have hμx : 0 < μ ^ (2 * x) := Real.rpow_pos_of_pos hμ _
  have h3 : rexp x * u₀ ^ x ≤ rexp (μ ^ 2 * rexp 1 * u₀) * Real.Gamma (x + 1) * μ ^ (-(2 * x)) := by
    rw [Real.rpow_neg hμ.le]
    rw [le_mul_inv_iff₀ hμx]
    linarith
  rw [div_le_iff₀ hΓ]
  calc (x + Y) * u₀ ^ x ≤ (1 + Y) * rexp x * u₀ ^ x := by
        gcongr
    _ = (1 + Y) * (rexp x * u₀ ^ x) := by ring
    _ ≤ (1 + Y) * (rexp (μ ^ 2 * rexp 1 * u₀) * Real.Gamma (x + 1) * μ ^ (-(2 * x))) := by
        gcongr
    _ = _ := by ring

/-- `u^{-1} e^{-c/u} ≤ 1/c`. -/
lemma inv_mul_exp_le {c u : ℝ} (hc : 0 < c) (hu : 0 < u) : u⁻¹ * rexp (-(c / u)) ≤ c⁻¹ := by
  have h := Real.add_one_le_exp (c / u)
  have hpos : 0 < rexp (c / u) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  rw [show u⁻¹ = c⁻¹ * (c / u) by field_simp]
  have : c / u ≤ rexp (c / u) := by linarith
  calc c⁻¹ * (c / u) ≤ c⁻¹ * rexp (c / u) := by gcongr
    _ = _ := by rw [inv_mul_eq_div]

/-- Summability over `ℕ × ℕ` from product bounds in two regimes. -/
lemma summable_of_two_regimes {T : ℕ × ℕ → ℝ} (hT : ∀ p, 0 ≤ T p) (P : ℕ × ℕ → Prop)
    {f₁ g₁ f₂ g₂ : ℕ → ℝ} (hf₁ : Summable f₁) (hg₁ : Summable g₁) (hf₂ : Summable f₂)
    (hg₂ : Summable g₂) (hf₁0 : 0 ≤ f₁) (hg₁0 : 0 ≤ g₁) (hf₂0 : 0 ≤ f₂) (hg₂0 : 0 ≤ g₂)
    (h₁ : ∀ p, P p → T p ≤ f₁ p.1 * g₁ p.2) (h₂ : ∀ p, ¬ P p → T p ≤ f₂ p.1 * g₂ p.2) :
    Summable T := by
  refine Summable.of_nonneg_of_le hT (fun p => ?_)
    ((hf₁.mul_of_nonneg hg₁ hf₁0 hg₁0).add (hf₂.mul_of_nonneg hg₂ hf₂0 hg₂0))
  have a1 := mul_nonneg (hf₁0 p.1) (hg₁0 p.2)
  have a2 := mul_nonneg (hf₂0 p.1) (hg₂0 p.2)
  by_cases hp : P p
  · have := h₁ p hp; linarith
  · have := h₂ p hp; linarith

/-! ### Complex auxiliaries -/

lemma dExp_add_re (s : ℂ) (r : ℝ) (n j : ℕ) :
    (dExp (s + n) r j).re = s.re / 2 + n / 2 - r / 2 * j := by
  rw [dExp_re]; simp; ring

lemma dExp_add_im (s : ℂ) (r : ℝ) (n j : ℕ) : (dExp (s + n) r j).im = s.im / 2 := by
  rw [dExp_im]; simp

lemma norm_dCoeff_eq (τ r : ℝ) (s : ℂ) (j : ℕ) :
    ‖dCoeff τ r s j‖ = |τ| ^ j / ((j ! : ℕ) : ℝ) * ‖(Complex.Gamma (dExp s r j))⁻¹‖ := by
  unfold dCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_pow, abs_neg, Nat.abs_cast]

/-- `|1/Γ(a)| ≤ |a| B/Γ(Re a + 1)` for `Re a ≥ 1/2`, from `1/Γ(a) = a/Γ(a+1)` and a bound `B` on
`Γ(Re w)|1/Γ(w)|`, `Re w ≥ 1`. -/
lemma norm_inv_Gamma_le_of_half {Y B : ℝ}
    (hB : ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ Y → gammaRatio w ≤ B) {a : ℂ} (ha : 1 / 2 ≤ a.re)
    (hY : |a.im| ≤ Y) :
    ‖(Complex.Gamma a)⁻¹‖ ≤ ‖a‖ * B / Real.Gamma (a.re + 1) := by
  have ha0 : a ≠ 0 := by intro h; rw [h] at ha; simp at ha; linarith
  have hΓ : 0 < Real.Gamma (a.re + 1) := Real.Gamma_pos_of_pos (by linarith)
  have h1 : (Complex.Gamma a)⁻¹ = a * (Complex.Gamma (a + 1))⁻¹ := by
    rw [Complex.Gamma_add_one a ha0, mul_inv, ← mul_assoc, mul_inv_cancel₀ ha0, one_mul]
  have h2 := hB (a + 1) (by simp; linarith) (by simpa using hY)
  unfold gammaRatio at h2
  simp only [Complex.add_re, Complex.one_re] at h2
  rw [h1, norm_mul, le_div_iff₀ hΓ, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)

/-- `|1/Γ(a)| Γ(Re a) ≤ (1 + 2Y) B` for `Re a ≥ 1/2`, `|Im a| ≤ Y`. -/
lemma norm_inv_Gamma_mul_Gamma_le {Y B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ Y → gammaRatio w ≤ B) {a : ℂ} (ha : 1 / 2 ≤ a.re)
    (hY : |a.im| ≤ Y) :
    ‖(Complex.Gamma a)⁻¹‖ * Real.Gamma a.re ≤ (1 + 2 * Y) * B := by
  have hpos : 0 < a.re := by linarith
  have h := norm_inv_Gamma_le_of_half hB ha hY
  rw [Real.Gamma_add_one hpos.ne'] at h
  have hΓ : 0 < Real.Gamma a.re := Real.Gamma_pos_of_pos hpos
  have hn : ‖a‖ ≤ a.re + Y := by
    have := Complex.norm_le_abs_re_add_abs_im a
    rw [abs_of_pos hpos] at this; linarith
  have hY0 : 0 ≤ Y := (abs_nonneg _).trans hY
  calc ‖(Complex.Gamma a)⁻¹‖ * Real.Gamma a.re
      ≤ ‖a‖ * B / (a.re * Real.Gamma a.re) * Real.Gamma a.re := by gcongr
    _ = ‖a‖ * B / a.re := by field_simp
    _ ≤ (a.re + Y) * B / a.re := by gcongr
    _ ≤ (1 + 2 * Y) * B := by
        rw [div_le_iff₀ hpos]
        have : Y ≤ 2 * Y * a.re := by nlinarith
        nlinarith

/-! ### Integral bounds -/

lemma integral_norm_upperLaplace_le_of_re_le_one {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 < u₀) {w : ℂ}
    (hw : w.re ≤ 1) :
    ∫ u in Ioi u₀, ‖(u : ℂ) ^ (w - 1) * (rexp (-(κ * u)) : ℂ)‖ ≤
      u₀ ^ (w.re - 1) * ∫ u in Ioi u₀, rexp (-(κ * u)) := by
  have hexpint : IntegrableOn (fun u : ℝ => rexp (-(κ * u))) (Ioi u₀) := by
    simpa [neg_mul] using exp_neg_integrableOn_Ioi u₀ hκ
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun u => norm_nonneg _)
    (hexpint.const_mul _) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
  have hu' : 0 < u := hu₀.trans hu
  dsimp only
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  simp only [Complex.sub_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_nonpos hu₀ (le_of_lt hu) (by linarith)) (Real.exp_pos _).le

lemma integral_norm_lowerDual_le_of_re_lt_half {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) {w : ℂ}
    (hw : w.re < 1 / 2) :
    ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ (w - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ ≤
      u₀ * (Real.Gamma (5 / 2 - w.re) * c ^ (w.re - 3 / 2)) := by
  have hb : w.re - 3 / 2 < 0 := by linarith
  calc _ ≤ ∫ u in Ioc 0 u₀, Real.Gamma (5 / 2 - w.re) * c ^ (w.re - 3 / 2) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrableOn_const (by simp) eNorm_ne_top) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        have hu1 := hu.1
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu1, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu1.le _) (Real.exp_pos _).le)]
        simp only [Complex.sub_re, Complex.one_re]
        have h := rpow_mul_exp_le_Gamma hb hc hu1
        rw [show 1 - (w.re - 3 / 2) = 5 / 2 - w.re by ring] at h
        calc u ^ (w.re - 1) * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))
            = u ^ (w.re - 3 / 2) * rexp (-(c / u)) := by
              rw [← mul_assoc, ← Real.rpow_add hu1]; ring_nf
          _ ≤ _ := h
    _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hu₀.le, smul_eq_mul]

lemma integral_norm_lowerDual_le_of_half_le {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) {w : ℂ}
    (hw : 1 / 2 ≤ w.re) :
    ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ (w - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ ≤
      u₀ * (u₀ ^ (w.re - 1 / 2) * c⁻¹) := by
  calc _ ≤ ∫ u in Ioc 0 u₀, u₀ ^ (w.re - 1 / 2) * c⁻¹ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          (integrableOn_const (by simp) eNorm_ne_top) ?_
        refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun u hu => ?_)
        have hu1 := hu.1
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu1, Complex.norm_real,
          Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hu1.le _) (Real.exp_pos _).le)]
        simp only [Complex.sub_re, Complex.one_re]
        calc u ^ (w.re - 1) * (u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)))
            = u ^ (w.re - 1 / 2) * (u⁻¹ * rexp (-(c / u))) := by
              rw [← mul_assoc, ← Real.rpow_add hu1, ← Real.rpow_neg_one, ← mul_assoc,
                ← Real.rpow_add hu1]; ring_nf
          _ ≤ u₀ ^ (w.re - 1 / 2) * c⁻¹ := by
              gcongr
              · exact hu.2
              · exact inv_mul_exp_le hc hu1
    _ = _ := by
        rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
          ENNReal.toReal_ofReal hu₀.le, smul_eq_mul]

/-! ### The regime bounds, in real variables -/

lemma rpow_add_mul_nat {b : ℝ} (hb : 0 < b) (α γ : ℝ) (j : ℕ) :
    b ^ (α + γ * j) = b ^ α * (b ^ γ) ^ j := by
  rw [Real.rpow_add hb, ← Real.rpow_natCast, ← Real.rpow_mul hb.le]

/-- Regime `x < 1/2` of the `k`-terms. -/
lemma kB_real {R u₀ σ r : ℝ} (hR : 0 ≤ R) (hu₀ : 0 < u₀) {n j : ℕ}
    (hx : σ / 2 + n / 2 - r / 2 * j < 1 / 2) :
    R ^ n * (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) * u₀ ^ ((σ / 2 + n / 2 - r / 2 * j) - 1)) ≤
      u₀ ^ (σ / 2 - 1) * (2 * max 1 (R * u₀ ^ (1 / 2 : ℝ))) ^ (1 - σ) * (1 / 2) ^ n *
        ((u₀ ^ (-(r / 2)) * (2 * max 1 (R * u₀ ^ (1 / 2 : ℝ))) ^ r) ^ j *
          (√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|)) := by
  set L := 2 * max 1 (R * u₀ ^ (1 / 2 : ℝ))
  have hL : 0 < L := by simp only [L]; linarith [le_max_left 1 (R * u₀ ^ (1 / 2 : ℝ))]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hG : Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) ≤ √π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)| := by
    rw [← Real.Gamma_one_half_eq]
    exact Gamma_le_of_mem_Icc (by norm_num) (by linarith) (by linarith)
  have hG0 : 0 ≤ Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hu : u₀ ^ ((σ / 2 + n / 2 - r / 2 * j) - 1) =
      u₀ ^ (σ / 2 - 1) * (u₀ ^ (1 / 2 : ℝ)) ^ n * (u₀ ^ (-(r / 2))) ^ j := by
    rw [← rpow_lin_split hu₀]; congr 1; ring
  have hgeom := geom_absorb (v := u₀ ^ (1 / 2 : ℝ)) (E := 1 - σ + r * j) hR
    (Real.rpow_nonneg hu₀.le _) (n := n) (by linarith)
  rw [rpow_add_mul_nat hL] at hgeom
  rw [hu]
  have h1 : 0 ≤ u₀ ^ (σ / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j := by positivity
  calc R ^ n * (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
        (u₀ ^ (σ / 2 - 1) * (u₀ ^ (1 / 2 : ℝ)) ^ n * (u₀ ^ (-(r / 2))) ^ j))
      = Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) * (R ^ n * (u₀ ^ (1 / 2 : ℝ)) ^ n) *
          (u₀ ^ (σ / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j) := by ring
    _ ≤ (√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|) *
          ((1 / 2) ^ n * (L ^ (1 - σ) * (L ^ r) ^ j)) *
          (u₀ ^ (σ / 2 - 1) * (u₀ ^ (-(r / 2))) ^ j) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Regime `x < 1/2` of the dual terms. -/
lemma dB_real {R c σ r : ℝ} (hR : 0 ≤ R) (hc : 0 < c) {n j : ℕ}
    (hx : σ / 2 + n / 2 - r / 2 * j < 1 / 2) :
    R ^ n * (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
        (Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) *
          c ^ ((σ / 2 + n / 2 - r / 2 * j) - 3 / 2))) ≤
      c ^ (σ / 2 - 3 / 2) * (2 * max 1 (R * c ^ (1 / 2 : ℝ))) ^ (1 - σ) * (1 / 2) ^ n *
        ((c ^ (-(r / 2)) * (2 * max 1 (R * c ^ (1 / 2 : ℝ))) ^ r) ^ j *
          ((√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|) *
            (1 + |Real.Gamma ((5 / 2 - σ / 2) + r / 2 * j)|))) := by
  set L := 2 * max 1 (R * c ^ (1 / 2 : ℝ))
  have hL : 0 < L := by simp only [L]; linarith [le_max_left 1 (R * c ^ (1 / 2 : ℝ))]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hG : Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) ≤ √π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)| := by
    rw [← Real.Gamma_one_half_eq]
    exact Gamma_le_of_mem_Icc (by norm_num) (by linarith) (by linarith)
  have hG0 : 0 ≤ Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hG' : Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) ≤
      1 + |Real.Gamma ((5 / 2 - σ / 2) + r / 2 * j)| := by
    rw [← Real.Gamma_two]
    exact Gamma_le_of_mem_Icc (by norm_num) (by linarith) (by linarith)
  have hG0' : 0 ≤ Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) :=
    (Real.Gamma_pos_of_pos (by linarith)).le
  have hu : c ^ ((σ / 2 + n / 2 - r / 2 * j) - 3 / 2) =
      c ^ (σ / 2 - 3 / 2) * (c ^ (1 / 2 : ℝ)) ^ n * (c ^ (-(r / 2))) ^ j := by
    rw [← rpow_lin_split hc]; congr 1; ring
  have hgeom := geom_absorb (v := c ^ (1 / 2 : ℝ)) (E := 1 - σ + r * j) hR
    (Real.rpow_nonneg hc.le _) (n := n) (by linarith)
  rw [rpow_add_mul_nat hL] at hgeom
  rw [hu]
  have h1 : 0 ≤ c ^ (σ / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j := by positivity
  calc R ^ n * (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
        (Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) *
        (c ^ (σ / 2 - 3 / 2) * (c ^ (1 / 2 : ℝ)) ^ n * (c ^ (-(r / 2))) ^ j)))
      = (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
          Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j))) * (R ^ n * (c ^ (1 / 2 : ℝ)) ^ n) *
          (c ^ (σ / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j) := by ring
    _ ≤ ((√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|) *
            (1 + |Real.Gamma ((5 / 2 - σ / 2) + r / 2 * j)|)) *
          ((1 / 2) ^ n * (L ^ (1 - σ) * (L ^ r) ^ j)) *
          (c ^ (σ / 2 - 3 / 2) * (c ^ (-(r / 2))) ^ j) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-- Regime `x ≥ 1/2` of the dual terms. -/
lemma dA_real {R u₀ σ r Y : ℝ} (hR : 0 ≤ R) (hu₀ : 0 < u₀) (hY : 0 ≤ Y) {n j : ℕ}
    (hx : 1 / 2 ≤ σ / 2 + n / 2 - r / 2 * j) :
    R ^ n * ((σ / 2 + n / 2 - r / 2 * j + Y) * u₀ ^ (σ / 2 + n / 2 - r / 2 * j) /
        Real.Gamma (σ / 2 + n / 2 - r / 2 * j + 1)) ≤
      (1 + Y) * rexp ((2 * (R + 1)) ^ 2 * rexp 1 * u₀) * (2 * (R + 1)) ^ (-σ) *
        (R * (2 * (R + 1)) ^ (-1 : ℝ)) ^ n * ((2 * (R + 1)) ^ r) ^ j := by
  have hμ : 0 < 2 * (R + 1) := by linarith
  have h := mul_rpow_div_Gamma_le (Y := Y) (u₀ := u₀) (show 0 < σ / 2 + n / 2 - r / 2 * j by
    linarith) hY hu₀ hμ
  have e : (2 * (R + 1)) ^ (-(2 * (σ / 2 + n / 2 - r / 2 * j))) =
      (2 * (R + 1)) ^ (-σ) * ((2 * (R + 1)) ^ (-1 : ℝ)) ^ n * ((2 * (R + 1)) ^ r) ^ j := by
    rw [← rpow_lin_split hμ]; congr 1; ring
  rw [e] at h
  calc R ^ n * ((σ / 2 + n / 2 - r / 2 * j + Y) * u₀ ^ (σ / 2 + n / 2 - r / 2 * j) /
        Real.Gamma (σ / 2 + n / 2 - r / 2 * j + 1))
      ≤ R ^ n * ((1 + Y) * rexp ((2 * (R + 1)) ^ 2 * rexp 1 * u₀) *
          ((2 * (R + 1)) ^ (-σ) * ((2 * (R + 1)) ^ (-1 : ℝ)) ^ n * ((2 * (R + 1)) ^ r) ^ j)) := by
        gcongr
    _ = _ := by rw [mul_pow]; ring

/-! ### Summability of the majorants in `j` -/

lemma summable_pow_mul_abs_Gamma_div_factorial {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (β : ℝ)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Summable fun j : ℕ => ρ ^ j * |Real.Gamma (β + b * j)| / ((j ! : ℕ) : ℝ) := by
  refine (summable_pow_mul_Gamma_div_factorial hb0 hb1 β hρ).abs.congr fun j => ?_
  rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hρ, Nat.abs_cast]

lemma summable_pow_mul_abs_Gamma_sq_div_factorial {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1 / 2)
    (β β' : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Summable fun j : ℕ =>
      ρ ^ j * (|Real.Gamma (β + b * j)| * |Real.Gamma (β' + b * j)|) / ((j ! : ℕ) : ℝ) := by
  refine (summable_pow_mul_Gamma_sq_div_factorial hb0 hb1 β β' hρ).abs.congr fun j => ?_
  rw [abs_div, abs_mul, abs_pow, abs_of_nonneg hρ, Nat.abs_cast, abs_mul]

/-! ### The kernel and the `k`-terms -/

/-- The kernel of `e^{-τx^r} F(x) x^{-s}`, `F(x) = ∑ a_n x^{-n}`, as a double series:
`h(u) = ∑_{n,j} a_n c_{n,j} u^{a_{n,j}-1}` with `a_{n,j} = (s + n - rj)/2`,
`c_{n,j} = (-τ)^j/(j! Γ(a_{n,j}))`. -/
noncomputable def prodKernel (a : ℕ → ℂ) (τ r : ℝ) (s : ℂ) (u : ℝ) : ℂ :=
  ∑' p : ℕ × ℕ, a p.1 * dCoeff τ r (s + p.1) p.2 * (u : ℂ) ^ (dExp (s + p.1) r p.2 - 1)

lemma GeomBounded.const_nonneg {a : ℕ → ℂ} {R C : ℝ} (hC : ∀ n, ‖a n‖ ≤ C * R ^ n) : 0 ≤ C := by
  have := hC 0; simp only [pow_zero, mul_one] at this; exact (norm_nonneg _).trans this

/-- **`I_k` termwise, for `0 < r < 2` and `k > R`**: the double series over `(n, j)` of the termwise
integrals converges absolutely to `I_k = ∫_{u₀}^∞ e^{-k²u} h(u) du`. -/
theorem hasSum_kTerm_prod {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {τ r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀) {k : ℕ}
    (hRk : R < k) :
    HasSum (fun p : ℕ × ℕ => a p.1 * dCoeff τ r (s + p.1) p.2 *
        upperLaplace ((k : ℝ) ^ 2) u₀ (dExp (s + p.1) r p.2))
      (kTerm (prodKernel a τ r s) u₀ k) := by
  obtain ⟨C₀, hC₀⟩ := ha
  have hC₀0 : 0 ≤ C₀ := GeomBounded.const_nonneg hC₀
  have hk : (0 : ℝ) < k := hR.trans_lt hRk
  set κ := (k : ℝ) ^ 2 with hκ_def
  have hκ : 0 < κ := by positivity
  set σ := s.re with hσ
  set Y := |s.im / 2| with hY
  obtain ⟨B₀, hB₀⟩ := gammaRatio_bounded Y
  set B := max B₀ 0
  have hB : ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ Y → gammaRatio w ≤ B :=
    fun w h1 h2 => (hB₀ w h1 h2).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  set g : ℕ × ℕ → ℝ → ℂ := fun p u =>
    (u : ℂ) ^ (dExp (s + p.1) r p.2 - 1) * (rexp (-(κ * u)) : ℂ) with hg
  set F : ℕ × ℕ → ℝ → ℂ := fun p u => a p.1 * dCoeff τ r (s + p.1) p.2 * g p u with hF
  have hint : ∀ p, IntegrableOn (F p) (Ioi u₀) := fun p =>
    (integrableOn_upperLaplace hκ hu₀ _).const_mul _
  have hnormeq : ∀ p, ∫ u in Ioi u₀, ‖F p u‖ =
      ‖a p.1‖ * ‖dCoeff τ r (s + p.1) p.2‖ * ∫ u in Ioi u₀, ‖g p u‖ := by
    intro p; rw [← integral_const_mul]; congr 1; funext u; simp only [F, norm_mul]
  set K := ∫ u in Ioi u₀, rexp (-(κ * u)) with hK_def
  have hK : 0 ≤ K := setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le
  set E := rexp (π * |s.im / 2|) / π with hE
  have hE0 : 0 ≤ E := by positivity
  set L := 2 * max 1 (R * u₀ ^ (1 / 2 : ℝ)) with hL
  have hL0 : 0 < L := by simp only [L]; linarith [le_max_left 1 (R * u₀ ^ (1 / 2 : ℝ))]
  set q₁ := R * (1 / κ) ^ (1 / 2 : ℝ) with hq₁
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁1 : q₁ < 1 := by
    have : (1 / κ) ^ (1 / 2 : ℝ) = (k : ℝ)⁻¹ := by
      rw [← Real.sqrt_eq_rpow, one_div, Real.sqrt_inv, hκ_def, Real.sqrt_sq hk.le]
    rw [hq₁, this, ← div_eq_mul_inv, div_lt_one hk]; exact hRk
  set ρ₁ := |τ| * (1 / κ) ^ (-(r / 2)) with hρ₁
  set ρ₂ := |τ| * (u₀ ^ (-(r / 2)) * L ^ r) with hρ₂
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  have hsum : Summable fun p => ∫ u in Ioi u₀, ‖F p u‖ := by
    refine summable_of_two_regimes (fun p => integral_nonneg fun _ => norm_nonneg _)
      (fun p : ℕ × ℕ => 1 / 2 ≤ (dExp (s + p.1) r p.2).re)
      (f₁ := fun n => C₀ * ((1 + 2 * Y) * B) * (1 / κ) ^ (σ / 2) * q₁ ^ n)
      (g₁ := fun j => ρ₁ ^ j / ((j ! : ℕ) : ℝ))
      (f₂ := fun n => C₀ * E * K * (u₀ ^ (σ / 2 - 1) * L ^ (1 - σ)) * (1 / 2) ^ n)
      (g₂ := fun j => √π * (ρ₂ ^ j / ((j ! : ℕ) : ℝ)) +
        ρ₂ ^ j * |Real.Gamma ((1 - σ / 2) + r / 2 * j)| / ((j ! : ℕ) : ℝ))
      ((summable_geometric_of_lt_one hq₁0 hq₁1).mul_left _)
      (Real.summable_pow_div_factorial ρ₁)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
      (((Real.summable_pow_div_factorial ρ₂).mul_left _).add
        (summable_pow_mul_abs_Gamma_div_factorial (by linarith) (by linarith) _ hρ₂0))
      (fun n => by positivity) (fun j => by positivity) (fun n => by positivity)
      (fun j => by positivity) ?_ ?_
    · rintro ⟨n, j⟩ hP
      simp only at hP ⊢
      have hxe := dExp_add_re s r n j
      have hI := integral_norm_upperLaplace_le hκ hu₀ (w := dExp (s + n) r j) (by linarith)
      have hΓ := norm_inv_Gamma_mul_Gamma_le hB0 hB hP (by rw [dExp_add_im])
      rw [hxe] at hI hΓ
      have he : (1 / κ) ^ (σ / 2 + n / 2 - r / 2 * j) =
          (1 / κ) ^ (σ / 2) * ((1 / κ) ^ (1 / 2 : ℝ)) ^ n * ((1 / κ) ^ (-(r / 2))) ^ j := by
        rw [← rpow_lin_split (by positivity)]; congr 1; ring
      rw [he] at hI
      rw [hnormeq, norm_dCoeff_eq]
      have hRn : ‖a n‖ ≤ C₀ * R ^ n := hC₀ n
      calc ‖a n‖ * (|τ| ^ j / ((j ! : ℕ) : ℝ) * ‖(Complex.Gamma (dExp (s + n) r j))⁻¹‖) *
            ∫ u in Ioi u₀, ‖g (n, j) u‖
          ≤ (C₀ * R ^ n) * (|τ| ^ j / ((j ! : ℕ) : ℝ) *
              ‖(Complex.Gamma (dExp (s + n) r j))⁻¹‖) *
            (Real.Gamma (σ / 2 + n / 2 - r / 2 * j) *
              ((1 / κ) ^ (σ / 2) * ((1 / κ) ^ (1 / 2 : ℝ)) ^ n * ((1 / κ) ^ (-(r / 2))) ^ j)) := by
            gcongr
        _ = C₀ * (|τ| ^ j / ((j ! : ℕ) : ℝ)) *
              (‖(Complex.Gamma (dExp (s + n) r j))⁻¹‖ * Real.Gamma (σ / 2 + n / 2 - r / 2 * j)) *
              (R ^ n * ((1 / κ) ^ (σ / 2) * ((1 / κ) ^ (1 / 2 : ℝ)) ^ n *
                ((1 / κ) ^ (-(r / 2))) ^ j)) := by ring
        _ ≤ C₀ * (|τ| ^ j / ((j ! : ℕ) : ℝ)) * ((1 + 2 * Y) * B) *
              (R ^ n * ((1 / κ) ^ (σ / 2) * ((1 / κ) ^ (1 / 2 : ℝ)) ^ n *
                ((1 / κ) ^ (-(r / 2))) ^ j)) := by gcongr
        _ = _ := by simp only [q₁, ρ₁]; rw [mul_pow, mul_pow]; ring
    · rintro ⟨n, j⟩ hP
      simp only [not_le] at hP ⊢
      have hxe := dExp_add_re s r n j
      have hI := integral_norm_upperLaplace_le_of_re_le_one hκ hu₀ (w := dExp (s + n) r j)
        (by linarith)
      have hc := norm_dCoeff_le (τ := τ) (s := s + n) (j := j) (by linarith)
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im,
        add_zero] at hc
      rw [hxe] at hI hP
      have hb := kB_real hR hu₀ (σ := σ) (r := r) hP
      have hΓ0 : 0 ≤ Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) :=
        (Real.Gamma_pos_of_pos (by linarith)).le
      rw [hnormeq]
      have hRn : ‖a n‖ ≤ C₀ * R ^ n := hC₀ n
      calc ‖a n‖ * ‖dCoeff τ r (s + n) j‖ * ∫ u in Ioi u₀, ‖g (n, j) u‖
          ≤ (C₀ * R ^ n) * (E * (|τ| ^ j * Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) /
              ((j ! : ℕ) : ℝ))) * (u₀ ^ ((σ / 2 + n / 2 - r / 2 * j) - 1) * K) := by
            gcongr
        _ = C₀ * E * K * (|τ| ^ j / ((j ! : ℕ) : ℝ)) * (R ^ n *
              (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
                u₀ ^ ((σ / 2 + n / 2 - r / 2 * j) - 1))) := by ring
        _ ≤ C₀ * E * K * (|τ| ^ j / ((j ! : ℕ) : ℝ)) *
              (u₀ ^ (σ / 2 - 1) * L ^ (1 - σ) * (1 / 2) ^ n *
                ((u₀ ^ (-(r / 2)) * L ^ r) ^ j * (√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|))) := by
            gcongr
        _ = _ := by simp only [ρ₂]; rw [mul_pow]; ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext p; simp only [F, g]; rw [integral_const_mul]; rfl
  · unfold kTerm prodKernel
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [F, g]
    rw [← tsum_mul_left]
    exact tsum_congr fun p => by ring

/-! ### The dual terms -/

/-- **`J_m` termwise, for `0 < r < 1` and `m ≥ 1`**: the double series over `(n, j)` of
`a_n c_{n,j} D_{a_{n,j}-1/2}(π²m²)` converges absolutely to
`J_m = ∫₀^{u₀} u^{-1/2} e^{-π²m²/u} h(u) du`.  No condition relating `R` and `m` is needed: for
`Re a_{n,j} ≥ 1/2` the factor `1/Γ(a_{n,j})` beats every geometric growth in `n`. -/
theorem hasSum_dualTerm_prod {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {τ r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀) {m : ℕ} (hm : 0 < m) :
    HasSum (fun p : ℕ × ℕ => a p.1 * dCoeff τ r (s + p.1) p.2 *
        lowerDual (π ^ 2 * (m : ℝ) ^ 2) u₀ (dExp (s + p.1) r p.2))
      (dualTerm (prodKernel a τ r s) u₀ m) := by
  obtain ⟨C₀, hC₀⟩ := ha
  have hC₀0 : 0 ≤ C₀ := GeomBounded.const_nonneg hC₀
  set c := π ^ 2 * (m : ℝ) ^ 2 with hc_def
  have hc : 0 < c := by positivity
  set σ := s.re with hσ
  set Y := |s.im / 2| with hY
  have hY0 : 0 ≤ Y := abs_nonneg _
  obtain ⟨B₀, hB₀⟩ := gammaRatio_bounded Y
  set B := max B₀ 0
  have hB : ∀ w : ℂ, 1 ≤ w.re → |w.im| ≤ Y → gammaRatio w ≤ B :=
    fun w h1 h2 => (hB₀ w h1 h2).trans (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  set g : ℕ × ℕ → ℝ → ℂ := fun p u =>
    (u : ℂ) ^ (dExp (s + p.1) r p.2 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)
    with hg
  set G : ℕ × ℕ → ℝ → ℂ := fun p u => a p.1 * dCoeff τ r (s + p.1) p.2 * g p u with hG
  have hint : ∀ p, IntegrableOn (G p) (Ioc 0 u₀) := fun p =>
    (integrableOn_lowerDual hc hu₀ _).const_mul _
  have hnormeq : ∀ p, ∫ u in Ioc 0 u₀, ‖G p u‖ =
      ‖a p.1‖ * ‖dCoeff τ r (s + p.1) p.2‖ * ∫ u in Ioc 0 u₀, ‖g p u‖ := by
    intro p; rw [← integral_const_mul]; congr 1; funext u; simp only [G, norm_mul]
  set E := rexp (π * |s.im / 2|) / π with hE
  have hE0 : 0 ≤ E := by positivity
  set μ := 2 * (R + 1) with hμ_def
  have hμ : 0 < μ := by linarith
  set D := (1 + Y) * rexp (μ ^ 2 * rexp 1 * u₀) * μ ^ (-σ) with hD
  set q₁ := R * μ ^ (-1 : ℝ) with hq₁
  have hq₁0 : 0 ≤ q₁ := by positivity
  have hq₁1 : q₁ < 1 := by
    rw [hq₁, Real.rpow_neg_one, ← div_eq_mul_inv, div_lt_one hμ]; linarith
  set ρ₁ := |τ| * μ ^ r with hρ₁
  set L := 2 * max 1 (R * c ^ (1 / 2 : ℝ)) with hL
  have hL0 : 0 < L := by simp only [L]; linarith [le_max_left 1 (R * c ^ (1 / 2 : ℝ))]
  set ρ₂ := |τ| * (c ^ (-(r / 2)) * L ^ r) with hρ₂
  have hρ₂0 : 0 ≤ ρ₂ := by positivity
  set β₁ := 1 - σ / 2
  set β₂ := 5 / 2 - σ / 2
  have hsum : Summable fun p => ∫ u in Ioc 0 u₀, ‖G p u‖ := by
    refine summable_of_two_regimes (fun p => integral_nonneg fun _ => norm_nonneg _)
      (fun p : ℕ × ℕ => 1 / 2 ≤ (dExp (s + p.1) r p.2).re)
      (f₁ := fun n => C₀ * B * c⁻¹ * (u₀ / u₀ ^ (1 / 2 : ℝ)) * D * q₁ ^ n)
      (g₁ := fun j => ρ₁ ^ j / ((j ! : ℕ) : ℝ))
      (f₂ := fun n => C₀ * E * u₀ * (c ^ (σ / 2 - 3 / 2) * L ^ (1 - σ)) * (1 / 2) ^ n)
      (g₂ := fun j => √π * (ρ₂ ^ j / ((j ! : ℕ) : ℝ)) +
        √π * (ρ₂ ^ j * |Real.Gamma (β₂ + r / 2 * j)| / ((j ! : ℕ) : ℝ)) +
        ρ₂ ^ j * |Real.Gamma (β₁ + r / 2 * j)| / ((j ! : ℕ) : ℝ) +
        ρ₂ ^ j * (|Real.Gamma (β₁ + r / 2 * j)| * |Real.Gamma (β₂ + r / 2 * j)|) /
          ((j ! : ℕ) : ℝ))
      ((summable_geometric_of_lt_one hq₁0 hq₁1).mul_left _)
      (Real.summable_pow_div_factorial ρ₁)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
      ((((Real.summable_pow_div_factorial ρ₂).mul_left _).add
        ((summable_pow_mul_abs_Gamma_div_factorial (by linarith) (by linarith) _ hρ₂0).mul_left
          _)).add
        (summable_pow_mul_abs_Gamma_div_factorial (by linarith) (by linarith) _ hρ₂0) |>.add
        (summable_pow_mul_abs_Gamma_sq_div_factorial (by linarith) (by linarith) _ _ hρ₂0))
      (fun n => by positivity) (fun j => by positivity) (fun n => by positivity)
      (fun j => by positivity) ?_ ?_
    · rintro ⟨n, j⟩ hP
      simp only at hP ⊢
      have hxe := dExp_add_re s r n j
      have hI := integral_norm_lowerDual_le_of_half_le hc hu₀ (w := dExp (s + n) r j) hP
      have hΓ := norm_inv_Gamma_le_of_half hB hP (by rw [dExp_add_im])
      have hnorm : ‖dExp (s + n) r j‖ ≤ (dExp (s + n) r j).re + Y := by
        have := Complex.norm_le_abs_re_add_abs_im (dExp (s + n) r j)
        rw [abs_of_pos (by linarith), dExp_add_im] at this; exact this
      rw [hxe] at hI hΓ hnorm hP
      have hx0 : 0 < σ / 2 + n / 2 - r / 2 * j := by linarith
      have hΓ' : ‖(Complex.Gamma (dExp (s + n) r j))⁻¹‖ ≤
          (σ / 2 + n / 2 - r / 2 * j + Y) * B / Real.Gamma (σ / 2 + n / 2 - r / 2 * j + 1) := by
        refine hΓ.trans ?_
        have := Real.Gamma_pos_of_pos (show 0 < σ / 2 + n / 2 - r / 2 * j + 1 by linarith)
        gcongr
      have hb := dA_real hR hu₀ hY0 (σ := σ) (r := r) hP
      have hsplit : u₀ * (u₀ ^ (σ / 2 + n / 2 - r / 2 * j - 1 / 2) * c⁻¹) =
          c⁻¹ * (u₀ / u₀ ^ (1 / 2 : ℝ)) * u₀ ^ (σ / 2 + n / 2 - r / 2 * j) := by
        rw [Real.rpow_sub hu₀]; ring
      rw [hsplit] at hI
      rw [hnormeq, norm_dCoeff_eq]
      have hRn : ‖a n‖ ≤ C₀ * R ^ n := hC₀ n
      have hΓp := Real.Gamma_pos_of_pos (show 0 < σ / 2 + n / 2 - r / 2 * j + 1 by linarith)
      calc ‖a n‖ * (|τ| ^ j / ((j ! : ℕ) : ℝ) * ‖(Complex.Gamma (dExp (s + n) r j))⁻¹‖) *
            ∫ u in Ioc 0 u₀, ‖g (n, j) u‖
          ≤ (C₀ * R ^ n) * (|τ| ^ j / ((j ! : ℕ) : ℝ) *
              ((σ / 2 + n / 2 - r / 2 * j + Y) * B / Real.Gamma (σ / 2 + n / 2 - r / 2 * j + 1))) *
            (c⁻¹ * (u₀ / u₀ ^ (1 / 2 : ℝ)) * u₀ ^ (σ / 2 + n / 2 - r / 2 * j)) := by
            gcongr
        _ = C₀ * B * c⁻¹ * (u₀ / u₀ ^ (1 / 2 : ℝ)) * (|τ| ^ j / ((j ! : ℕ) : ℝ)) *
              (R ^ n * ((σ / 2 + n / 2 - r / 2 * j + Y) * u₀ ^ (σ / 2 + n / 2 - r / 2 * j) /
                Real.Gamma (σ / 2 + n / 2 - r / 2 * j + 1))) := by ring
        _ ≤ C₀ * B * c⁻¹ * (u₀ / u₀ ^ (1 / 2 : ℝ)) * (|τ| ^ j / ((j ! : ℕ) : ℝ)) *
              ((1 + Y) * rexp ((2 * (R + 1)) ^ 2 * rexp 1 * u₀) * (2 * (R + 1)) ^ (-σ) *
                (R * (2 * (R + 1)) ^ (-1 : ℝ)) ^ n * ((2 * (R + 1)) ^ r) ^ j) := by gcongr
        _ = _ := by simp only [q₁, ρ₁, D, μ]; rw [mul_pow]; ring
    · rintro ⟨n, j⟩ hP
      simp only [not_le] at hP ⊢
      have hxe := dExp_add_re s r n j
      have hI := integral_norm_lowerDual_le_of_re_lt_half hc hu₀ (w := dExp (s + n) r j) hP
      have hcoef := norm_dCoeff_le (τ := τ) (s := s + n) (j := j) (by linarith)
      simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im,
        add_zero] at hcoef
      rw [hxe] at hI hP
      have hb := dB_real hR hc (σ := σ) (r := r) hP
      have hΓ0 : 0 ≤ Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) :=
        (Real.Gamma_pos_of_pos (by linarith)).le
      have hΓ0' : 0 ≤ Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) :=
        (Real.Gamma_pos_of_pos (by linarith)).le
      rw [hnormeq]
      have hRn : ‖a n‖ ≤ C₀ * R ^ n := hC₀ n
      calc ‖a n‖ * ‖dCoeff τ r (s + n) j‖ * ∫ u in Ioc 0 u₀, ‖g (n, j) u‖
          ≤ (C₀ * R ^ n) * (E * (|τ| ^ j * Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) /
              ((j ! : ℕ) : ℝ))) * (u₀ * (Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) *
                c ^ ((σ / 2 + n / 2 - r / 2 * j) - 3 / 2))) := by
            gcongr
        _ = C₀ * E * u₀ * (|τ| ^ j / ((j ! : ℕ) : ℝ)) * (R ^ n *
              (Real.Gamma ((1 - (σ + n) / 2) + r / 2 * j) *
                (Real.Gamma (5 / 2 - (σ / 2 + n / 2 - r / 2 * j)) *
                  c ^ ((σ / 2 + n / 2 - r / 2 * j) - 3 / 2)))) := by ring
        _ ≤ C₀ * E * u₀ * (|τ| ^ j / ((j ! : ℕ) : ℝ)) *
              (c ^ (σ / 2 - 3 / 2) * L ^ (1 - σ) * (1 / 2) ^ n *
                ((c ^ (-(r / 2)) * L ^ r) ^ j *
                  ((√π + |Real.Gamma ((1 - σ / 2) + r / 2 * j)|) *
                    (1 + |Real.Gamma ((5 / 2 - σ / 2) + r / 2 * j)|)))) := by
            gcongr
        _ = _ := by simp only [ρ₂, β₁, β₂]; rw [mul_pow]; ring
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext p; simp only [G, g]; rw [integral_const_mul]; rfl
  · unfold dualTerm prodKernel
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    simp only [G, g]
    rw [← tsum_mul_left]
    exact tsum_congr fun p => by ring

/-! ### Regrouping: the paper's `∑_ℓ b_ℓ (⋯)` with `ℓ = qn - j`

Since the double series converge unconditionally, they may be summed along the fibres of any map;
for `r = 1/q` and `ℓ(n, j) = qn - j` this is the paper's grouping into `b_ℓ/Γ(w_ℓ)`. -/

theorem hasSum_kTerm_prod_fiberwise {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {τ r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀) {k : ℕ}
    (hRk : R < k) {ι : Type*} (ℓ : ℕ × ℕ → ι) :
    HasSum (fun i : ι => ∑' p : ℓ ⁻¹' {i}, a p.1.1 * dCoeff τ r (s + p.1.1) p.1.2 *
        upperLaplace ((k : ℝ) ^ 2) u₀ (dExp (s + p.1.1) r p.1.2))
      (kTerm (prodKernel a τ r s) u₀ k) :=
  (hasSum_kTerm_prod hR ha hr0 hr2 s hu₀ hRk).tsum_fiberwise ℓ

theorem hasSum_dualTerm_prod_fiberwise {a : ℕ → ℂ} {R : ℝ} (hR : 0 ≤ R) (ha : GeomBounded a R)
    {τ r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℂ) {u₀ : ℝ} (hu₀ : 0 < u₀) {m : ℕ} (hm : 0 < m)
    {ι : Type*} (ℓ : ℕ × ℕ → ι) :
    HasSum (fun i : ι => ∑' p : ℓ ⁻¹' {i}, a p.1.1 * dCoeff τ r (s + p.1.1) p.1.2 *
        lowerDual (π ^ 2 * (m : ℝ) ^ 2) u₀ (dExp (s + p.1.1) r p.1.2))
      (dualTerm (prodKernel a τ r s) u₀ m) :=
  (hasSum_dualTerm_prod hR ha hr0 hr1 s hu₀ hm).tsum_fiberwise ℓ

end ZetaF
