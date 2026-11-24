/-
# The Khinchin zeta function (Section 6.1)

`Z(s) = ∑_{k ≥ 1} μ_k k^{-s}`, `μ_k = log₂(1 + 1/(k(k+2)))` (the Gauss–Kuzmin probabilities).
We prove
* `hasSum_mu`: `Z(0) = ∑ μ_k = 1` (the product `∏ (k+1)²/(k(k+2))` telescopes to `2`);
* `hasSum_k_mu_sub`: `∑_k (kμ_k - 1/(k log 2)) = -(1+γ)/log 2` (the summation by parts of the proof
  of Proposition 6.1);
* `khinchinZ_constant_term` (**Proposition 6.1**): `Z(s) - 1/((s+1) log 2) → -1/log 2` as `s → -1`
  (from `Re s > -1`), and `holderMean_asymptotic`: `log 2 · ∑ k^q μ_k - 1/(1-q) → -1` as `q → 1⁻`.
-/
import ZetaF.Deps
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.PSeriesComplex

open Filter Topology Real Finset

namespace ZetaF

/-- The Gauss–Kuzmin probability `μ_k = log₂(1 + 1/(k(k+2)))`. -/
noncomputable def gkMu (k : ℕ) : ℝ := Real.log (1 + 1 / ((k : ℝ) * (k + 2))) / Real.log 2

lemma log_gk (k : ℕ) :
    Real.log (1 + 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 2))) =
      2 * Real.log (k + 2) - Real.log (k + 1) - Real.log (k + 3) := by
  have h1 : (0 : ℝ) < k + 1 := by positivity
  have h2 : (0 : ℝ) < k + 2 := by positivity
  have h3 : (0 : ℝ) < k + 3 := by positivity
  have e : 1 + 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 2)) = (k + 2) ^ 2 / ((k + 1) * (k + 3)) := by
    push_cast; field_simp; ring
  rw [e, Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul h1.ne' h3.ne']
  push_cast; ring

/-- **`Z(0) = 1`.** -/
theorem hasSum_mu : HasSum (fun k : ℕ => gkMu (k + 1)) 1 := by
  have hpart : ∀ N : ℕ, ∑ k ∈ range N, gkMu (k + 1) =
      (Real.log 2 + Real.log (N + 1) - Real.log (N + 2)) / Real.log 2 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_range_succ, ih, gkMu, log_gk]
      push_cast
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      field_simp
      ring
  have hlim : Tendsto (fun N : ℕ => (Real.log 2 + Real.log (N + 1) - Real.log (N + 2)) / Real.log 2)
      atTop (𝓝 1) := by
    have h := (tendsto_log_comp_add_sub_log 1).comp tendsto_natCast_atTop_atTop
    have h' : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log ((N : ℝ) + 2)) atTop (𝓝 0) := by
      have := ((tendsto_log_comp_add_sub_log 1).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)).neg
      simp only [neg_zero] at this
      refine this.congr fun N => ?_
      simp only [Function.comp]; ring_nf
    have := ((tendsto_const_nhds (x := Real.log 2)).add h').div_const (Real.log 2)
    rw [add_zero, div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'] at this
    exact this.congr fun N => by ring
  have hnonneg : ∀ k, 0 ≤ gkMu (k + 1) := fun k => by
    unfold gkMu
    have h0 : (0 : ℝ) ≤ 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 2)) := by positivity
    exact div_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by norm_num))
  rw [← funext hpart] at hlim
  exact (hasSum_iff_tendsto_nat_of_nonneg hnonneg 1).2 hlim

/-- The summation by parts: `∑_{k ≤ N} k (2 log(k+1) - log k - log(k+2)) = log(N+1) - N log((N+2)/(N+1))`. -/
lemma sum_k_log_gk (N : ℕ) :
    ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) * Real.log (1 + 1 / (((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) + 2))) =
      Real.log (N + 1) - N * (Real.log (N + 2) - Real.log (N + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih, log_gk]
    push_cast
    ring_nf

/-- `|kμ_k - 1/(k log 2)| ≤ 3/(k² log 2)`. -/
lemma abs_k_mu_sub_le (k : ℕ) :
    |((k + 1 : ℕ) : ℝ) * gkMu (k + 1) - 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2)| ≤
      3 / (((k + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set n : ℝ := ((k + 1 : ℕ) : ℝ)
  have hn : 1 ≤ n := by simp [n]
  set x := 1 / (n * (n + 2)) with hx_def
  have hx : 0 < x := by positivity
  have hup : Real.log (1 + x) ≤ x := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith); linarith
  have hlo : x / (1 + x) ≤ Real.log (1 + x) := by
    have := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + x by linarith)
    calc x / (1 + x) = 1 - (1 + x)⁻¹ := by field_simp; ring
      _ ≤ _ := this
  have key : |n * Real.log (1 + x) - 1 / n| ≤ 3 / n ^ 2 := by
    rw [abs_le]
    constructor
    · have h1 : n * (x / (1 + x)) = n / (n + 1) ^ 2 := by
        simp only [hx_def]; field_simp; ring
      have h2 : n / (n + 1) ^ 2 - 1 / n = -((2 * n + 1) / (n * (n + 1) ^ 2)) := by
        field_simp; ring
      have h3 : (2 * n + 1) / (n * (n + 1) ^ 2) ≤ 3 / n ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
      have h4 : n * (x / (1 + x)) ≤ n * Real.log (1 + x) :=
        mul_le_mul_of_nonneg_left hlo (by linarith)
      linarith
    · have h1 : n * x = 1 / (n + 2) := by simp only [hx_def]; field_simp
      have h2 : 1 / (n + 2) ≤ 1 / n := one_div_le_one_div_of_le (by linarith) (by linarith)
      have h4 : n * Real.log (1 + x) ≤ n * x := mul_le_mul_of_nonneg_left hup (by linarith)
      have : 0 ≤ 3 / n ^ 2 := by positivity
      linarith
  unfold gkMu
  rw [show n * (Real.log (1 + 1 / (n * (n + 2))) / Real.log 2) - 1 / (n * Real.log 2) =
      (n * Real.log (1 + x) - 1 / n) / Real.log 2 by simp only [hx_def]; field_simp]
  rw [abs_div, abs_of_pos hl]
  exact (div_le_div_of_nonneg_right key hl.le).trans_eq (by rw [div_div])

lemma summable_k_mu_sub :
    Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) * gkMu (k + 1) - 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2) := by
  have hs : Summable fun k : ℕ => 3 / (((k + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) := by
    have := ((summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)).mul_left
      (3 / Real.log 2)
    refine this.congr fun k => ?_
    field_simp
  exact Summable.of_norm_bounded hs fun k => by rw [Real.norm_eq_abs]; exact abs_k_mu_sub_le k

/-- **`∑_k (kμ_k - 1/(k log 2)) = -(1+γ)/log 2`** (proof of Proposition 6.1). -/
theorem hasSum_k_mu_sub :
    HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * gkMu (k + 1) - 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2))
      (-(1 + eulerMascheroniConstant) / Real.log 2) := by
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hpart : ∀ N : ℕ, ∑ k ∈ range N, (((k + 1 : ℕ) : ℝ) * gkMu (k + 1) -
      1 / (((k + 1 : ℕ) : ℝ) * Real.log 2)) =
      (-((harmonic N : ℝ) - Real.log (N + 1)) -
        N * (Real.log (N + 2) - Real.log (N + 1))) / Real.log 2 := by
    intro N
    rw [sum_sub_distrib]
    have e1 : ∑ k ∈ range N, ((k + 1 : ℕ) : ℝ) * gkMu (k + 1) =
        (Real.log (N + 1) - N * (Real.log (N + 2) - Real.log (N + 1))) / Real.log 2 := by
      rw [← sum_k_log_gk, sum_div]
      refine sum_congr rfl fun k _ => ?_
      unfold gkMu; ring
    have e2 : ∑ k ∈ range N, 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2) = (harmonic N : ℝ) / Real.log 2 := by
      rw [harmonic]; push_cast; rw [sum_div]
      refine sum_congr rfl fun k _ => ?_
      field_simp
    rw [e1, e2]; ring
  have hlog : Tendsto (fun N : ℕ => (N : ℝ) * (Real.log (N + 2) - Real.log (N + 1))) atTop (𝓝 1) := by
    have hlow : ∀ N : ℕ, (N : ℝ) / (N + 2) ≤ (N : ℝ) * (Real.log (N + 2) - Real.log (N + 1)) := by
      intro N
      have h1 : (0 : ℝ) < N + 1 := by positivity
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < (N + 2) / (N + 1) by positivity)
      rw [Real.log_div (by positivity) h1.ne'] at h
      have e : (1 : ℝ) - (((N : ℝ) + 2) / ((N : ℝ) + 1))⁻¹ = 1 / ((N : ℝ) + 2) := by
        field_simp; ring
      rw [e] at h
      calc (N : ℝ) / (N + 2) = N * (1 / (N + 2)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
    have hupp : ∀ N : ℕ, (N : ℝ) * (Real.log (N + 2) - Real.log (N + 1)) ≤ (N : ℝ) / (N + 1) := by
      intro N
      have h1 : (0 : ℝ) < N + 1 := by positivity
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N + 2) / (N + 1) by positivity)
      rw [Real.log_div (by positivity) h1.ne'] at h
      have e : ((N : ℝ) + 2) / ((N : ℝ) + 1) - 1 = 1 / ((N : ℝ) + 1) := by field_simp; ring
      rw [e] at h
      calc (N : ℝ) * (Real.log (N + 2) - Real.log (N + 1)) ≤ N * (1 / (N + 1)) :=
            mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N)
        _ = _ := by ring
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le (tendsto_natCast_div_add_atTop (2 : ℝ))
      (tendsto_natCast_div_add_atTop (1 : ℝ)) hlow hupp
  have hlim := ((tendsto_harmonic_sub_log_add_one.neg).sub hlog).div_const (Real.log 2)
  rw [← funext hpart] at hlim
  have hs := summable_k_mu_sub.hasSum
  rw [tendsto_nhds_unique hs.tendsto_sum_nat hlim] at hs
  convert hs using 1
  ring

/-! ### The Khinchin zeta function near `s = -1` -/

/-- `Z(s) = ∑_{k ≥ 1} μ_k k^{-s}` (converges for `Re s > -1`). -/
noncomputable def khinchinZ (s : ℂ) : ℂ := ∑' k : ℕ, (gkMu (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (-s)

/-- The correction `e_k = μ_k - 1/(k² log 2) = (kμ_k - 1/(k log 2))/k`. -/
noncomputable def gkErr (k : ℕ) : ℝ :=
  (((k + 1 : ℕ) : ℝ) * gkMu (k + 1) - 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2)) / ((k + 1 : ℕ) : ℝ)

/-- `E(s) = ∑ e_k k^{-s}` (converges for `Re s > -2`). -/
noncomputable def khinchinE (s : ℂ) : ℂ := ∑' k : ℕ, (gkErr k : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (-s)

lemma norm_gkErr_term_le (k : ℕ) (s : ℂ) :
    ‖(gkErr k : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (-s)‖ ≤
      3 / Real.log 2 * ((k + 1 : ℕ) : ℝ) ^ (-3 - s.re) := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hl := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [norm_mul, Complex.norm_real, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k)]
  simp only [Complex.neg_re]
  have h := abs_k_mu_sub_le k
  rw [Real.norm_eq_abs, gkErr, abs_div, abs_of_pos hn]
  have e : ((k + 1 : ℕ) : ℝ) ^ (-3 - s.re) =
      ((k + 1 : ℕ) : ℝ) ^ (-s.re) / ((k + 1 : ℕ) : ℝ) ^ 3 := by
    rw [show -3 - s.re = -s.re - ((3 : ℕ) : ℝ) by push_cast; ring, Real.rpow_sub hn, Real.rpow_natCast]
  rw [e]
  calc |((k + 1 : ℕ) : ℝ) * gkMu (k + 1) - 1 / (((k + 1 : ℕ) : ℝ) * Real.log 2)| /
        ((k + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ (-s.re)
      ≤ 3 / (((k + 1 : ℕ) : ℝ) ^ 2 * Real.log 2) / ((k + 1 : ℕ) : ℝ) *
          ((k + 1 : ℕ) : ℝ) ^ (-s.re) := by gcongr
    _ = _ := by field_simp

lemma summable_gkErr_term {s : ℂ} (hs : -2 < s.re) :
    Summable fun k : ℕ => (gkErr k : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded ?_ fun k => norm_gkErr_term_le k s
  have : Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) ^ (-3 - s.re) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (show -3 - s.re < -1 by linarith))
    exact h.congr fun k => by push_cast; rfl
  exact this.mul_left _

lemma continuousAt_khinchinE : ContinuousAt khinchinE (-1) := by
  have hopen : IsOpen {s : ℂ | -3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hc : ContinuousOn khinchinE {s : ℂ | -3 / 2 < s.re} := by
    have hsum : Summable fun k : ℕ => 3 / Real.log 2 * ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
      have h := (summable_nat_add_iff 1).2
        (Real.summable_nat_rpow.2 (show -(3 / 2 : ℝ) < -1 by norm_num))
      exact (h.congr fun k => by push_cast; rfl).mul_left _
    refine continuousOn_tsum (fun k => ?_) hsum fun k s hs => ?_
    · exact (continuous_const.mul (continuous_neg.const_cpow
        (Or.inl (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k))))).continuousOn
    · refine (norm_gkErr_term_le k s).trans ?_
      have hs : -3 / 2 < s.re := hs
      gcongr
      · exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      · linarith
  exact hc.continuousAt (hopen.mem_nhds (by norm_num))

lemma khinchinE_neg_one :
    khinchinE (-1) = ((-(1 + eulerMascheroniConstant) / Real.log 2 : ℝ) : ℂ) := by
  rw [khinchinE, ← hasSum_k_mu_sub.tsum_eq, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [neg_neg, Complex.cpow_one, gkErr]
  have hn : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

lemma khinchinZ_eq {s : ℂ} (hs : -1 < s.re) :
    khinchinZ s = riemannZeta (s + 2) / Real.log 2 + khinchinE s := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.log_pos (by norm_num)).ne'
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow (s := s + 2) (by simp; linarith)
  have hzs : Summable fun n : ℕ => 1 / (n + 1 : ℂ) ^ (s + 2) := by
    have := (Complex.summable_one_div_nat_cpow.2 (show 1 < (s + 2).re by simp; linarith))
    exact (summable_nat_add_iff 1).2 this |>.congr fun n => by push_cast; rfl
  rw [hz, khinchinE, ← tsum_div_const, ← (hzs.div_const _).tsum_add
    (summable_gkErr_term (by linarith)), khinchinZ]
  refine tsum_congr fun k => ?_
  have hn : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  have hn' : ((k + 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero k)
  rw [gkErr]
  have e : ((k : ℂ) + 1) ^ (s + 2) = ((k + 1 : ℕ) : ℂ) ^ s * ((k + 1 : ℕ) : ℂ) ^ 2 := by
    push_cast
    rw [Complex.cpow_add _ _ (by exact_mod_cast hn), Complex.cpow_two]
  rw [e, Complex.cpow_neg]
  push_cast
  field_simp
  ring

/-- **Proposition 6.1**: `Z(s) = 1/((s+1) log 2) - 1/log 2 + o(1)` as `s → -1`. -/
theorem khinchinZ_constant_term :
    Tendsto (fun s : ℂ => khinchinZ s - 1 / ((s + 1) * Real.log 2))
      (𝓝[{s | -1 < s.re}] (-1)) (𝓝 (-1 / Real.log 2 : ℝ)) := by
  have hl : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.log_pos (by norm_num)).ne'
  have hshift : Tendsto (fun s : ℂ => s + 2) (𝓝[{s | -1 < s.re}] (-1)) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 : Tendsto (fun s : ℂ => s + 2) (𝓝 (-1)) (𝓝 ((-1 : ℂ) + 2)) :=
        (continuous_id.add continuous_const).tendsto (-1 : ℂ)
      rw [show (-1 : ℂ) + 2 = 1 by norm_num] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      intro h
      have := congrArg Complex.re h
      simp at this
      have hs' : -1 < s.re := hs
      linarith
  have hζ := (tendsto_riemannZeta_sub_one_div.comp hshift).div_const (Real.log 2 : ℂ)
  have hE := (continuousAt_khinchinE.tendsto).mono_left (nhdsWithin_le_nhds (s := {s | -1 < s.re}))
  have hsum := hζ.add hE
  rw [khinchinE_neg_one] at hsum
  have hval : (eulerMascheroniConstant : ℂ) / (Real.log 2 : ℂ) +
      ((-(1 + eulerMascheroniConstant) / Real.log 2 : ℝ) : ℂ) = ((-1 / Real.log 2 : ℝ) : ℂ) := by
    push_cast; field_simp; ring
  rw [hval] at hsum
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : -1 < s.re := hs
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  simp only [Function.comp]
  rw [khinchinZ_eq hs', show s + 2 - 1 = s + 1 by ring]
  field_simp
  ring

/-- **Hölder means** (Proposition 6.1): `log 2 · K_q^q - 1/(1-q) → -1` as `q → 1⁻`,
where `K_q^q = ∑_k k^q μ_k`. -/
theorem holderMean_asymptotic :
    Tendsto (fun q : ℝ => Real.log 2 * (∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ q * gkMu (k + 1)) - 1 / (1 - q))
      (𝓝[<] 1) (𝓝 (-1)) := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hmap : Tendsto (fun q : ℝ => -(q : ℂ)) (𝓝[<] 1) (𝓝[{s | -1 < s.re}] (-1)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h1 := (Complex.continuous_ofReal.tendsto (1 : ℝ)).neg
      rw [Complex.ofReal_one] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with q hq
      show -1 < (-(q : ℂ)).re
      simp only [Complex.neg_re, Complex.ofReal_re]
      have : q < 1 := hq
      linarith
  have h := ((khinchinZ_constant_term.comp hmap).const_mul (Real.log 2 : ℂ))
  have h' := (Complex.continuous_re.tendsto _).comp h
  have hlim : (((Real.log 2 : ℂ) * ((-1 / Real.log 2 : ℝ) : ℂ))).re = -1 := by
    rw [← Complex.ofReal_mul, Complex.ofReal_re]; field_simp
  rw [hlim] at h'
  refine h'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  have hq : q < 1 := hq
  have hq1 : (1 : ℝ) - q ≠ 0 := by linarith
  simp only [Function.comp, khinchinZ, neg_neg]
  have e : ∀ k : ℕ, (gkMu (k + 1) : ℂ) * ((k + 1 : ℕ) : ℂ) ^ (q : ℂ) =
      ((((k + 1 : ℕ) : ℝ) ^ q * gkMu (k + 1) : ℝ) : ℂ) := fun k => by
    rw [Complex.ofReal_mul, Complex.ofReal_cpow (by positivity)]; push_cast; ring
  simp_rw [e]
  rw [← Complex.ofReal_tsum]
  have e2 : (1 : ℂ) / ((-(q : ℂ) + 1) * (Real.log 2 : ℂ)) = ((1 / ((1 - q) * Real.log 2) : ℝ) : ℂ) := by
    push_cast; ring_nf
  rw [e2, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
  field_simp

/-! ### The `O(s+1)` remainder -/

/-- `ζ(s) - 1/(s-1)`, extended by `γ` at `s = 1`, is differentiable at `1` (removable singularity). -/
lemma exists_zeta_reg : ∃ g : ℂ → ℂ, DifferentiableAt ℂ g 1 ∧ g 1 = eulerMascheroniConstant ∧
    ∀ s, s ≠ 1 → g s = riemannZeta s - 1 / (s - 1) := by
  set f : ℂ → ℂ := fun s => riemannZeta s - 1 / (s - 1)
  have ht := tendsto_riemannZeta_sub_one_div
  have hev : ∀ᶠ z in 𝓝[≠] (1 : ℂ), ‖f z‖ ≤ ‖(eulerMascheroniConstant : ℂ)‖ + 1 := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds _ one_pos)] with z hz
    have := norm_le_norm_add_norm_sub' (f z) (eulerMascheroniConstant : ℂ)
    rw [dist_eq_norm] at hz
    simp only [f] at this ⊢
    linarith
  obtain ⟨U, hU, hUb⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hev
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hd : DifferentiableOn ℂ f (Metric.ball 1 r \ {1}) := fun z hz =>
    ((differentiableAt_riemannZeta hz.2).sub ((differentiableAt_const _).div
      (differentiableAt_id.sub_const _) (sub_ne_zero.2 hz.2))).differentiableWithinAt
  have hb : BddAbove (norm ∘ f '' (Metric.ball 1 r \ {1})) :=
    ⟨‖(eulerMascheroniConstant : ℂ)‖ + 1, by
      rintro _ ⟨z, hz, rfl⟩; exact hUb ⟨hrU hz.1, hz.2⟩⟩
  have hD := Complex.differentiableOn_update_limUnder_of_bddAbove (Metric.ball_mem_nhds 1 hr) hd hb
  have hlim : limUnder (𝓝[≠] (1 : ℂ)) f = eulerMascheroniConstant := ht.limUnder_eq
  refine ⟨Function.update f 1 (limUnder (𝓝[≠] (1 : ℂ)) f),
    hD.differentiableAt (Metric.ball_mem_nhds 1 hr), by rw [Function.update_self, hlim],
    fun s hs => by rw [Function.update_of_ne hs]⟩

lemma differentiableAt_khinchinE : DifferentiableAt ℂ khinchinE (-1) := by
  have hopen : IsOpen {s : ℂ | -3 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hsum : Summable fun k : ℕ => 3 / Real.log 2 * ((k + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h := (summable_nat_add_iff 1).2
      (Real.summable_nat_rpow.2 (show -(3 / 2 : ℝ) < -1 by norm_num))
    exact (h.congr fun k => by push_cast; rfl).mul_left _
  have hd : DifferentiableOn ℂ khinchinE {s : ℂ | -3 / 2 < s.re} := by
    refine Complex.differentiableOn_tsum_of_summable_norm hsum (fun k => ?_) hopen
      fun k s hs => ?_
    · exact ((differentiable_const _).mul (differentiable_neg.const_cpow
        (Or.inl (Nat.cast_ne_zero.2 (Nat.succ_ne_zero k))))).differentiableOn
    · refine (norm_gkErr_term_le k s).trans ?_
      have hs : -3 / 2 < s.re := hs
      gcongr
      · exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      · linarith
  exact hd.differentiableAt (hopen.mem_nhds (by norm_num))

/-- **Proposition 6.1 with the remainder**: `Z(s) = 1/((s+1) log 2) - 1/log 2 + O(s+1)`. -/
theorem khinchinZ_isBigO :
    (fun s : ℂ => khinchinZ s - 1 / ((s + 1) * Real.log 2) - ((-1 / Real.log 2 : ℝ) : ℂ))
      =O[𝓝[{s | -1 < s.re}] (-1)] fun s => s + 1 := by
  obtain ⟨g, hg, hg1, hgf⟩ := exists_zeta_reg
  have hl : (Real.log 2 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.log_pos (by norm_num)).ne'
  have h1 : (fun s : ℂ => g (s + 2) - g 1) =O[𝓝 (-1)] fun s => s + 1 := by
    have hc : Tendsto (fun s : ℂ => s + 2) (𝓝 (-1)) (𝓝 1) := by
      have h := (continuous_id.add continuous_const).tendsto (x := (-1 : ℂ)) (f := fun s : ℂ => s + 2)
      simpa [show (-1 : ℂ) + 2 = 1 by norm_num] using h
    have := (hg.hasFDerivAt.isBigO_sub).comp_tendsto hc
    refine this.congr_right fun s => ?_
    simp only [Function.comp]; ring
  have h2 : (fun s : ℂ => khinchinE s - khinchinE (-1)) =O[𝓝 (-1)] fun s => s + 1 := by
    have := differentiableAt_khinchinE.hasFDerivAt.isBigO_sub
    refine this.congr_right fun s => ?_
    ring
  have h := ((h1.const_mul_left ((Real.log 2 : ℂ))⁻¹).add h2).mono
    (nhdsWithin_le_nhds (s := {s : ℂ | -1 < s.re}))
  refine h.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : -1 < s.re := hs
  have hs1 : s + 1 ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hs2 : s + 2 ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  rw [hgf _ hs2, hg1, khinchinZ_eq hs', khinchinE_neg_one, show s + 2 - 1 = s + 1 by ring]
  push_cast
  field_simp
  ring

end ZetaF
