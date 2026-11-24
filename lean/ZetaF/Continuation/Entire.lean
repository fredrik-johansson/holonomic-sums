/-
# The `k`-terms and dual terms are entire functions of `s` (Theorem 3.2)

`I_k(s) = ∑_n a_n/Γ((s+n)/2) · ∫_{u₀}^∞ u^{(s+n)/2-1} e^{-k²u} du` and
`J_m(s) = ∑_n a_n/Γ((s+n)/2) · ∫₀^{u₀} u^{(s+n)/2-1} u^{-1/2} e^{-π²m²/u} du`
for **every** `s ∈ ℂ`; each term is entire and the series converge locally uniformly.
-/
import ZetaF.Continuation.Basic
import ZetaF.Open

open MeasureTheory Set Filter Finset
open scoped Real Topology

namespace ZetaF

variable {a : ℕ → ℂ} {R : ℝ}

/-- A term of the series for `I_k(s)` (with `κ = k²`). -/
noncomputable def kSeriesTerm (a : ℕ → ℂ) (κ u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * (Complex.Gamma ((s + n) / 2))⁻¹ * upperLaplace κ u₀ ((s + n) / 2)

/-- A term of the series for `J_m(s)` (with `c = π²m²`). -/
noncomputable def dSeriesTerm (a : ℕ → ℂ) (c u₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  a n * (Complex.Gamma ((s + n) / 2))⁻¹ * lowerDual c u₀ ((s + n) / 2)

lemma differentiable_half_shift (n : ℕ) : Differentiable ℂ fun s : ℂ => (s + n) / 2 := by fun_prop

lemma differentiable_kSeriesTerm {κ u₀ : ℝ} (hκ : 0 < κ) (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (kSeriesTerm a κ u₀ n) :=
  ((differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp
    (differentiable_half_shift n))).mul ((differentiable_upperLaplace hκ hu₀).comp
      (differentiable_half_shift n))

lemma differentiable_dSeriesTerm {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀) (n : ℕ) :
    Differentiable ℂ (dSeriesTerm a c u₀ n) :=
  ((differentiable_const _).mul (Complex.differentiable_one_div_Gamma.comp
    (differentiable_half_shift n))).mul ((differentiable_lowerDual hc hu₀).comp
      (differentiable_half_shift n))

/-- Near `s₀`, for `n ≥ N`: `Re((s+n)/2) ≥ 1` and `|Im((s+n)/2)| ≤ Y`, so `|1/Γ| ≤ C/Γ(Re)`. -/
lemma local_gamma_control (s₀ : ℂ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      1 ≤ ((s + n) / 2).re ∧ (s₀.re - 1 + n) / 2 ≤ ((s + n) / 2).re ∧
      ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * Real.Gamma ((s + n) / 2).re ≤ C := by
  obtain ⟨C, hC⟩ := gammaRatio_bounded ((|s₀.im| + 1) / 2)
  refine ⟨⌈3 - s₀.re⌉₊, max C 0, le_max_right _ _, fun n hn s hs => ?_⟩
  have hn' : 3 - s₀.re ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [Metric.mem_ball, dist_eq_norm] at hs
  have hre : |s.re - s₀.re| < 1 := (Complex.abs_re_le_norm _).trans_lt (by simpa using hs)
  have him : |s.im - s₀.im| < 1 := (Complex.abs_im_le_norm _).trans_lt (by simpa using hs)
  have e : ((s + n) / 2).re = (s.re + n) / 2 := by simp
  have h1 : 1 ≤ ((s + n) / 2).re := by rw [e]; have := abs_lt.1 hre; linarith
  refine ⟨h1, by rw [e]; have := abs_lt.1 hre; linarith, ?_⟩
  have h2 : |((s + n) / 2).im| ≤ (|s₀.im| + 1) / 2 := by
    have : ((s + n) / 2).im = s.im / 2 := by simp
    rw [this, abs_div, abs_two]
    have := abs_sub_abs_le_abs_sub s.im s₀.im
    linarith
  have := hC _ h1 h2
  unfold gammaRatio at this
  rw [mul_comm]; exact this.trans (le_max_left _ _)

/-- Locally uniform bound for the `k`-series. -/
lemma kSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {k : ℝ} (hk : R < k) (hk1 : 1 ≤ k)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
        ∫ u in Ioi u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-(k ^ 2 * u)) : ℂ)‖ ≤ b n := by
  obtain ⟨N, C, hC0, hN⟩ := local_gamma_control s₀
  obtain ⟨Ca, hCa⟩ := ha
  have hk0 : 0 < k := lt_of_le_of_lt hR hk
  have hCa0 : 0 ≤ Ca := le_trans (norm_nonneg _) (by simpa using hCa 0)
  refine ⟨N, fun n => Ca * C * (1 / k) ^ (s₀.re - 1) * (R / k) ^ n, ?_, fun n hn s hs => ?_⟩
  · exact (summable_geometric_of_lt_one (div_nonneg hR hk0.le) ((div_lt_one hk0).2 hk)).mul_left _
  obtain ⟨h1, h2, h3⟩ := hN n hn s hs
  set x := ((s + n) / 2).re
  have hx : 0 < x := by linarith
  have hI := integral_norm_upperLaplace_le (κ := k ^ 2) (by positivity) hu₀ (w := (s + n) / 2) hx
  have hpow : (1 / k ^ 2) ^ x ≤ (1 / k) ^ (s₀.re - 1) * (1 / k) ^ n := by
    rw [← one_div_sq_rpow hk0]
    apply Real.rpow_le_rpow_of_exponent_ge (by positivity) _ h2
    rw [div_le_one (by positivity)]; nlinarith
  have hG := Real.Gamma_pos_of_pos hx
  calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
        ∫ u in Ioi u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-(k ^ 2 * u)) : ℂ)‖
      ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * (Real.Gamma x * (1 / k ^ 2) ^ x) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ‖a n‖ * (‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * Real.Gamma x) * (1 / k ^ 2) ^ x := by ring
    _ ≤ (Ca * R ^ n) * C * ((1 / k) ^ (s₀.re - 1) * (1 / k) ^ n) := by
        apply mul_le_mul (mul_le_mul (hCa n) h3 (by positivity) (by positivity)) hpow
          (by positivity) (by positivity)
    _ = Ca * C * (1 / k) ^ (s₀.re - 1) * (R / k) ^ n := by
        simp only [div_pow, one_pow]; field_simp

/-- **`I_k(s)` as a series, for every `s ∈ ℂ`.** -/
theorem hasSum_kSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {k : ℝ} (hk : R < k) (hk1 : 1 ≤ k)
    {u₀ : ℝ} (hu₀ : 0 < u₀) (s : ℂ) :
    HasSum (fun n => kSeriesTerm a (k ^ 2) u₀ n s)
      (∫ u in Ioi u₀, (rexp (-(k ^ 2 * u)) : ℂ) * kernel a s u) := by
  obtain ⟨N, b, hb, hbn⟩ := kSeries_local_bound ha hR hk hk1 hu₀ s
  have hκ : 0 < k ^ 2 := by have := lt_of_le_of_lt hR hk; positivity
  have e : ∀ n (u : ℝ), (rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u =
      (a n * (Complex.Gamma ((s + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-(k ^ 2 * u)) : ℂ)) := by
    intro n u; unfold kernelTerm; ring
  have hint : ∀ n, IntegrableOn (fun u => (rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u)
      (Ioi u₀) := fun n => by
    simp_rw [e]; exact (integrableOn_upperLaplace hκ hu₀ _).const_mul _
  have hnorm : ∀ n, ∫ u in Ioi u₀, ‖(rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u‖ =
      ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
        ∫ u in Ioi u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) * (rexp (-(k ^ 2 * u)) : ℂ)‖ := fun n => by
    simp_rw [e, norm_mul]; rw [integral_const_mul]
  have hsum : Summable fun n => ∫ u in Ioi u₀, ‖(rexp (-(k ^ 2 * u)) : ℂ) * kernelTerm a s n u‖ := by
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff N).2 hb)
    rw [hnorm]; exact hbn (n + N) (Nat.le_add_left _ _) s (Metric.mem_ball_self one_pos)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n; simp_rw [e]; rw [integral_const_mul]; rfl
  · congr 1; funext u; rw [kernel, ← tsum_mul_left]

/-- **The `k`-terms are entire** (`KTermEntire` of `ZetaF/Open.lean`). -/
theorem kTermEntire : KTermEntire := by
  intro a R hR ha u₀ hu₀ k hk
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast lt_of_le_of_lt hR hk
    exact_mod_cast this
  have hκ : 0 < (k : ℝ) ^ 2 := by positivity
  have e : (fun s => kTerm (kernel a s) u₀ k) = fun s => ∑' n, kSeriesTerm a ((k : ℝ) ^ 2) u₀ n s :=
    funext fun s => ((hasSum_kSeries ha hR hk hk1 hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_kSeriesTerm hκ hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := kSeries_local_bound ha hR hk hk1 hu₀ s₀
  refine ⟨N, b, hb, fun n hn s hs => ?_⟩
  refine le_trans ?_ (hbn n hn s hs)
  unfold kSeriesTerm upperLaplace
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

lemma rpow_half_add_nat {l : ℝ} (hl : 0 < l) (σ : ℝ) (n : ℕ) :
    l ^ ((σ + n) / 2) = l ^ (σ / 2) * (√l) ^ n := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hl.le, ← Real.rpow_add hl]
  congr 1; ring

/-- `u₀^x / Γ(x+1) ≤ e^{u₀/λ} λ^x`. -/
lemma rpow_div_Gamma_le {x u₀ l : ℝ} (hx : 0 < x) (hu₀ : 0 ≤ u₀) (hl : 0 < l) :
    u₀ ^ x / Real.Gamma (x + 1) ≤ rexp (u₀ / l) * l ^ x := by
  have h := rpow_le_exp_mul_Gamma hx (div_nonneg hu₀ hl.le)
  rw [Real.div_rpow hu₀ hl.le, div_le_iff₀ (by positivity)] at h
  rw [div_le_iff₀ (Real.Gamma_pos_of_pos (by linarith))]
  linarith [h]

/-- Locally uniform bound for the dual series. -/
lemma dSeries_local_bound (ha : GeomBounded a R) (hR : 0 ≤ R) {c u₀ S : ℝ} (hu₀ : 0 < u₀)
    (hS0 : 0 ≤ S) (hS : ∀ u ∈ Ioc 0 u₀, u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) ≤ S) (s₀ : ℂ) :
    ∃ N : ℕ, ∃ b : ℕ → ℝ, Summable b ∧ ∀ n ≥ N, ∀ s ∈ Metric.ball s₀ 1,
      ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ *
        ∫ u in Ioc 0 u₀, ‖(u : ℂ) ^ ((s + n) / 2 - 1) *
          ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ ≤ b n := by
  obtain ⟨N, C, hC0, hN⟩ := local_gamma_control s₀
  obtain ⟨Ca, hCa⟩ := ha
  have hCa0 : 0 ≤ Ca := le_trans (norm_nonneg _) (by simpa using hCa 0)
  set l : ℝ := 1 / (4 * (R ^ 2 + 1)) with hl
  have hl0 : 0 < l := by positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one (by positivity)]; nlinarith
  have hq : R * √l < 1 := by
    have h1 : (R * √l) ^ 2 < 1 := by
      rw [mul_pow, Real.sq_sqrt hl0.le, hl]
      rw [← mul_div_assoc, mul_one, div_lt_one (by positivity)]; nlinarith
    nlinarith [Real.sqrt_nonneg l, mul_nonneg hR (Real.sqrt_nonneg l)]
  refine ⟨N, fun n => Ca * C * S * rexp (u₀ / l) * l ^ ((s₀.re - 1) / 2) * (R * √l) ^ n, ?_,
    fun n hn s hs => ?_⟩
  · exact (summable_geometric_of_lt_one (mul_nonneg hR (Real.sqrt_nonneg _)) hq).mul_left _
  obtain ⟨h1, h2, h3⟩ := hN n hn s hs
  set x := ((s + n) / 2).re
  have hx : 0 < x := by linarith
  have hG := Real.Gamma_pos_of_pos hx
  have hI := integral_norm_lowerDual_le hu₀ (w := (s + n) / 2) hx hS
  have hΓ : ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ ≤ C / Real.Gamma x := by
    rw [le_div_iff₀ hG]; exact h3
  have hE := rpow_div_Gamma_le hx hu₀.le hl0
  have hpow : l ^ x ≤ l ^ ((s₀.re - 1) / 2) * (√l) ^ n := by
    rw [← rpow_half_add_nat hl0]
    exact Real.rpow_le_rpow_of_exponent_ge hl0 hl1 (by linarith)
  rw [Real.Gamma_add_one hx.ne'] at hE
  calc ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀, _
      ≤ ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * (S * (u₀ ^ x / x)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ ≤ (Ca * R ^ n) * (C / Real.Gamma x) * (S * (u₀ ^ x / x)) :=
        mul_le_mul (mul_le_mul (hCa n) hΓ (by positivity) (by positivity)) le_rfl
          (by positivity) (by positivity)
    _ = Ca * R ^ n * C * S * (u₀ ^ x / (x * Real.Gamma x)) := by field_simp
    _ ≤ Ca * R ^ n * C * S * (rexp (u₀ / l) * (l ^ ((s₀.re - 1) / 2) * (√l) ^ n)) := by
        apply mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left hpow (by positivity)))
        positivity
    _ = _ := by simp only [mul_pow]; ring

/-- **`J`-type terms as a series, for every `s ∈ ℂ`.** -/
theorem hasSum_dSeries (ha : GeomBounded a R) (hR : 0 ≤ R) {c u₀ : ℝ} (hc : 0 < c) (hu₀ : 0 < u₀)
    (s : ℂ) :
    HasSum (fun n => dSeriesTerm a c u₀ n s)
      (∫ u in Ioc 0 u₀, ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernel a s u) := by
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS c le_rfl) s
  have e : ∀ n (u : ℝ), ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a s n u =
      (a n * (Complex.Gamma ((s + n) / 2))⁻¹) *
        ((u : ℂ) ^ ((s + n) / 2 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)) := by
    intro n u; unfold kernelTerm; ring
  have hint : ∀ n, IntegrableOn
      (fun u => ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a s n u)
      (Ioc 0 u₀) := fun n => by
    simp_rw [e]; exact (integrableOn_lowerDual hc hu₀ _).const_mul _
  have hnorm : ∀ n, ∫ u in Ioc 0 u₀,
      ‖((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a s n u‖ =
      ‖a n‖ * ‖(Complex.Gamma ((s + n) / 2))⁻¹‖ * ∫ u in Ioc 0 u₀,
        ‖(u : ℂ) ^ ((s + n) / 2 - 1) * ((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ)‖ :=
    fun n => by simp_rw [e, norm_mul]; rw [integral_const_mul]
  have hsum : Summable fun n => ∫ u in Ioc 0 u₀,
      ‖((u ^ (-(1 / 2 : ℝ)) * rexp (-(c / u)) : ℝ) : ℂ) * kernelTerm a s n u‖ := by
    rw [← summable_nat_add_iff N]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_nat_add_iff N).2 hb)
    rw [hnorm]; exact hbn (n + N) (Nat.le_add_left _ _) s (Metric.mem_ball_self one_pos)
  have := hasSum_integral_of_summable_integral_norm hint hsum
  convert this using 1
  · funext n; simp_rw [e]; rw [integral_const_mul]; rfl
  · congr 1; funext u; rw [kernel, ← tsum_mul_left]

/-- **The dual terms are entire** (`DualTermEntire` of `ZetaF/Open.lean`). -/
theorem dualTermEntire : DualTermEntire := by
  intro a R hR ha u₀ hu₀ m hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 < π ^ 2 * (m : ℝ) ^ 2 := by positivity
  obtain ⟨S, hS0, hS⟩ := exists_bound_rpow_neg_half_mul_exp hc u₀
  have e : (fun s => dualTerm (kernel a s) u₀ m) =
      fun s => ∑' n, dSeriesTerm a (π ^ 2 * (m : ℝ) ^ 2) u₀ n s :=
    funext fun s => ((hasSum_dSeries ha hR hc hu₀ s).tsum_eq).symm
  rw [e]
  refine differentiable_tsum_of_local_bound (fun n => differentiable_dSeriesTerm hc hu₀ n)
    fun s₀ => ?_
  obtain ⟨N, b, hb, hbn⟩ := dSeries_local_bound ha hR hu₀ hS0 (hS _ le_rfl) s₀
  refine ⟨N, b, hb, fun n hn s hs => ?_⟩
  refine le_trans ?_ (hbn n hn s hs)
  unfold dSeriesTerm lowerDual
  rw [norm_mul, norm_mul]
  gcongr
  exact norm_integral_le_integral_norm _

end ZetaF
