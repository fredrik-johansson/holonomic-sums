/-
Copyright (c) 2026. Released under Apache 2.0 license.

# Starting values for the moment systems (Section 5 / Section 6.4.2)

The starting values of the bit-burst evaluation are built from the integrals
`D_a(c) = ∫_0^U u^{a-1} e^{-c/u} du`. This file proves

* the integration-by-parts recurrence `a D_a + c D_{a-1} = E U^a` (`E = e^{-c/U}`), for every real
  `a` (equation `(Drec)` of the paper);
* `0 < D_a ≤ E U^a / a` for `a > 0`;
* the reduction `D_{n-1/2} = α_n D_{-1/2} + β_n E` with `α_n = (-4c)^n n!/(2n)!`, so that with
  `b_n = 4^n/n!` one has `|b_n α_n| = (16c)^n/(2n)!`;
* the tail bounds of Section 6.4.2: if `16c ≤ (2N+1)(2N+2)/2` and `4U ≤ (N+1)/2` (`N ≥ 1`), every
  tail of the `α`- and `β`-series is at most twice its first term (for the `β`-series, twice the
  first term of its majorant `E b_n U^{n-1/2}/(n-1/2) + |b_n α_n| D_{-1/2}`).
-/
import ZetaF.Bounds.ErrorProp

open Real Set Filter Topology MeasureTheory intervalIntegral
open scoped Nat

namespace ZetaF.StartVals

/-- `u^b e^{-c/u}` for `u > 0`, extended by `0`. -/
noncomputable def kx (c b u : ℝ) : ℝ := if 0 < u then u ^ b * rexp (-(c / u)) else 0

lemma kx_of_pos {c b u : ℝ} (hu : 0 < u) : kx c b u = u ^ b * rexp (-(c / u)) := by simp [kx, hu]

lemma kx_nonneg (c b u : ℝ) : 0 ≤ kx c b u := by
  unfold kx; split_ifs with h
  · exact mul_nonneg (rpow_nonneg h.le _) (exp_pos _).le
  · exact le_rfl

lemma tendsto_kx_zero {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Tendsto (fun u => u ^ b * rexp (-(c / u))) (𝓝[>] 0) (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-b) c hc).comp tendsto_inv_nhdsGT_zero
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
  simp only [Function.comp]
  rw [inv_rpow hu.le, rpow_neg hu.le, inv_inv, div_eq_mul_inv, neg_mul]

lemma continuousAt_kx {c b u : ℝ} (hu : 0 < u) : ContinuousAt (kx c b) u := by
  have h : ContinuousAt (fun u => u ^ b * rexp (-(c / u))) u :=
    ((continuousAt_id.rpow_const (Or.inl hu.ne')).mul
      (continuous_exp.continuousAt.comp ((continuousAt_const.div continuousAt_id hu.ne').neg)))
  refine h.congr ?_
  filter_upwards [lt_mem_nhds hu] with v hv
  rw [kx_of_pos hv]

lemma continuousOn_kx {c : ℝ} (hc : 0 < c) (b : ℝ) : ContinuousOn (kx c b) (Ici 0) := by
  intro u hu
  rcases (mem_Ici.1 hu).eq_or_lt with h | h
  · subst h
    rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt]
    have : kx c b 0 = 0 := by simp [kx]
    rw [this]
    refine (tendsto_kx_zero hc b).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with v (hv : 0 < v)
    rw [kx_of_pos hv]
  · exact (continuousAt_kx h).continuousWithinAt

lemma intervalIntegrable_kx {c : ℝ} (hc : 0 < c) (b : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    IntervalIntegrable (kx c b) volume 0 U :=
  ((continuousOn_kx hc b).mono (by
    rw [uIcc_of_le hU]; exact Icc_subset_Ici_self)).intervalIntegrable

/-- `D_a(c) = ∫_0^U u^{a-1} e^{-c/u} du`. -/
noncomputable def Dint (c U a : ℝ) : ℝ := ∫ u in (0 : ℝ)..U, kx c (a - 1) u

lemma hasDerivAt_kx {c a u : ℝ} (hu : 0 < u) :
    HasDerivAt (kx c a) (a * kx c (a - 1) u + c * kx c (a - 2) u) u := by
  have h1 := hasDerivAt_rpow_const (p := a) (Or.inl hu.ne')
  have h2 : HasDerivAt (fun u : ℝ => -(c / u)) (c / u ^ 2) u := by
    have := (hasDerivAt_inv hu.ne').const_mul c
    convert this.neg using 1
    · ext v; simp [div_eq_mul_inv]
    · field_simp
  have h3 := h1.mul (h2.exp)
  have heq : a * u ^ (a - 1) * rexp (-(c / u)) + u ^ a * (rexp (-(c / u)) * (c / u ^ 2)) =
      a * kx c (a - 1) u + c * kx c (a - 2) u := by
    rw [kx_of_pos hu, kx_of_pos hu, rpow_sub hu a 2, rpow_two]
    field_simp
  rw [← heq]
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hu] with v hv
  rw [kx_of_pos hv]; rfl

/-- **The recurrence `(Drec)`**: `a D_a + c D_{a-1} = e^{-c/U} U^a`, for every real `a`. -/
theorem Drec {c U : ℝ} (hc : 0 < c) (hU : 0 < U) (a : ℝ) :
    a * Dint c U a + c * Dint c U (a - 1) = rexp (-(c / U)) * U ^ a := by
  have hcont : ContinuousOn (kx c a) (Icc 0 U) :=
    (continuousOn_kx hc a).mono Icc_subset_Ici_self
  have hint : IntervalIntegrable (fun u => a * kx c (a - 1) u + c * kx c (a - 2) u) volume 0 U :=
    ((intervalIntegrable_kx hc _ hU.le).const_mul a).add
      ((intervalIntegrable_kx hc _ hU.le).const_mul c)
  have h := integral_eq_sub_of_hasDerivAt_of_le hU.le hcont
    (fun u hu => hasDerivAt_kx hu.1) hint
  rw [intervalIntegral.integral_add ((intervalIntegrable_kx hc _ hU.le).const_mul a)
      ((intervalIntegrable_kx hc _ hU.le).const_mul c),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h
  have h0 : kx c a 0 = 0 := by simp [kx]
  unfold Dint
  rw [show a - 1 - 1 = a - 2 by ring, h, h0, sub_zero, kx_of_pos hU, mul_comm]

/-- `0 < D_a`. -/
theorem Dint_pos {c U : ℝ} (hc : 0 < c) (hU : 0 < U) (a : ℝ) : 0 < Dint c U a :=
  intervalIntegral_pos_of_pos_on (intervalIntegrable_kx hc _ hU.le)
    (fun u hu => by rw [kx_of_pos hu.1]; exact mul_pos (rpow_pos_of_pos hu.1 _) (exp_pos _)) hU

/-- `D_a ≤ e^{-c/U} U^a / a` for `a > 0`. -/
theorem Dint_le {c U a : ℝ} (hc : 0 < c) (hU : 0 < U) (ha : 0 < a) :
    Dint c U a ≤ rexp (-(c / U)) * U ^ a / a := by
  have hr : -1 < a - 1 := by linarith
  have hpow : IntervalIntegrable (fun u : ℝ => u ^ (a - 1)) volume 0 U :=
    intervalIntegral.intervalIntegrable_rpow' hr
  have hmono : Dint c U a ≤ ∫ u in (0 : ℝ)..U, rexp (-(c / U)) * u ^ (a - 1) := by
    refine integral_mono_on hU.le (intervalIntegrable_kx hc _ hU.le) (hpow.const_mul _) ?_
    intro u hu
    rcases hu.1.eq_or_lt with h | h
    · subst h; simp only [kx, lt_irrefl, ite_false]
      exact mul_nonneg (exp_pos _).le (rpow_nonneg le_rfl _)
    · rw [kx_of_pos h, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ (rpow_nonneg h.le _)
      refine exp_le_exp.2 (neg_le_neg ?_)
      exact div_le_div_of_nonneg_left hc.le h hu.2
  refine hmono.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr), sub_add_cancel,
    zero_rpow ha.ne', sub_zero]
  ring

/-! ### Reduction to `D_{-1/2}` -/

/-- `α_n = (-4c)^n n!/(2n)!`. -/
noncomputable def alphaS (c : ℝ) (n : ℕ) : ℝ := (-4 * c) ^ n * (n ! : ℝ) / ((2 * n)! : ℝ)

/-- `β_0 = 0`, `β_{n+1} = (U^{n+1/2} - c β_n)/(n+1/2)`. -/
noncomputable def betaS (c U : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (U ^ ((n : ℝ) + 1 / 2) - c * betaS c U n) / ((n : ℝ) + 1 / 2)

lemma alphaS_succ (c : ℝ) (n : ℕ) :
    alphaS c (n + 1) = -c * alphaS c n / ((n : ℝ) + 1 / 2) := by
  unfold alphaS
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
    Nat.factorial_succ]
  have h1 : ((2 * n)! : ℝ) ≠ 0 := by positivity
  have h2 : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- **`D_{n-1/2} = α_n D_{-1/2} + β_n E`.** -/
theorem Dint_half_eq {c U : ℝ} (hc : 0 < c) (hU : 0 < U) (n : ℕ) :
    Dint c U ((n : ℝ) - 1 / 2) =
      alphaS c n * Dint c U (-(1 / 2)) + betaS c U n * rexp (-(c / U)) := by
  induction n with
  | zero => simp [alphaS, betaS]
  | succ n ih =>
    have hrec := Drec hc hU ((n : ℝ) + 1 / 2)
    rw [show (n : ℝ) + 1 / 2 - 1 = (n : ℝ) - 1 / 2 by ring, ih] at hrec
    have h2 : (n : ℝ) + 1 / 2 ≠ 0 := by positivity
    have hD : Dint c U ((n : ℝ) + 1 / 2) = (rexp (-(c / U)) * U ^ ((n : ℝ) + 1 / 2) -
        c * (alphaS c n * Dint c U (-(1 / 2)) + betaS c U n * rexp (-(c / U)))) / ((n : ℝ) + 1 / 2) := by
      rw [eq_div_iff h2]; linarith [hrec]
    rw [show ((n + 1 : ℕ) : ℝ) - 1 / 2 = (n : ℝ) + 1 / 2 by push_cast; ring, alphaS_succ, betaS, hD]
    ring

/-- `b_n = 4^n/n!`. -/
noncomputable def bS (n : ℕ) : ℝ := 4 ^ n / (n ! : ℝ)

/-- **`|b_n α_n| = (16c)^n/(2n)!`.** -/
theorem abs_bS_mul_alphaS {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    |bS n * alphaS c n| = (16 * c) ^ n / ((2 * n)! : ℝ) := by
  unfold bS alphaS
  have h1 : (n ! : ℝ) ≠ 0 := by positivity
  have : 4 ^ n / (n ! : ℝ) * ((-4 * c) ^ n * (n ! : ℝ) / ((2 * n)! : ℝ)) =
      (-1) ^ n * ((16 * c) ^ n / ((2 * n)! : ℝ)) := by
    rw [show (-4 * c) = (-1) * (4 * c) by ring, mul_pow, mul_pow, show (16 : ℝ) = 4 * 4 by norm_num,
      mul_assoc, mul_pow]
    field_simp
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n 2]; ring
  rw [this, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by positivity)]

/-! ### Tails of the `α`- and `β`-series -/

/-- The `α`-series terms `(16c)^n/(2n)!` halve from `N` on once `16c ≤ (2N+1)(2N+2)/2`. -/
lemma alpha_ratio {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hN : 16 * c ≤ (2 * N + 1) * (2 * N + 2) / 2) {n : ℕ} (hn : N ≤ n) :
    (16 * c) ^ (n + 1) / ((2 * (n + 1))! : ℝ) ≤ (16 * c) ^ n / ((2 * n)! : ℝ) / 2 := by
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hle : 16 * c ≤ (2 * n + 1) * (2 * n + 2) / 2 := hN.trans (by nlinarith)
  rw [show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, pow_succ]
  have h1 : (0 : ℝ) < ((2 * n)! : ℝ) := by positivity
  push_cast
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hp : 0 ≤ (16 * c) ^ n := by positivity
  have : (16 * c) ^ n * (16 * c) * ((2 * n)! * 2) ≤
      (16 * c) ^ n * ((2 * n + 1 + 1) * ((2 * n + 1) * (2 * n)!)) := by
    rw [show (16 * c) ^ n * (16 * c) * ((2 * n)! * 2) = (16 * c) ^ n * (2 * n)! * (16 * c * 2) by
      ring, show (16 * c) ^ n * ((2 * n + 1 + 1) * ((2 * n + 1) * (2 * n)!)) =
        (16 * c) ^ n * (2 * n)! * ((2 * n + 1) * (2 * n + 2)) by ring]
    exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hp h1.le)
  linarith

/-- **Tail of the `α`-series**: at most twice its first term. -/
theorem alpha_tail {c : ℝ} (hc : 0 ≤ c) {N : ℕ}
    (hN : 16 * c ≤ (2 * N + 1) * (2 * N + 2) / 2) :
    Summable (fun k => bS (N + k) * alphaS c (N + k)) ∧
      |∑' k, bS (N + k) * alphaS c (N + k)| ≤ 2 * ((16 * c) ^ N / ((2 * N)! : ℝ)) := by
  have h := tail_le_two_mul (fun n => bS n * alphaS c n) N (fun n hn => by
    simp only [Real.norm_eq_abs, abs_bS_mul_alphaS hc]
    exact alpha_ratio hc hN hn)
  simp only [Real.norm_eq_abs, abs_bS_mul_alphaS hc] at h
  exact h

/-- The majorant `b_n U^{n-1/2}/(n-1/2)` of `b_n D_{n-1/2}/E`. -/
noncomputable def gS (U : ℝ) (n : ℕ) : ℝ := bS n * (U ^ ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1 / 2))

lemma gS_nonneg {U : ℝ} (hU : 0 < U) {n : ℕ} (hn : 1 ≤ n) : 0 ≤ gS U n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold gS bS
  exact mul_nonneg (by positivity) (div_nonneg (rpow_nonneg hU.le _) (by linarith))

/-- `0 < b_n D_{n-1/2} ≤ E gS U n` for `n ≥ 1`. -/
lemma bS_Dint_le {c U : ℝ} (hc : 0 < c) (hU : 0 < U) {n : ℕ} (hn : 1 ≤ n) :
    bS n * Dint c U ((n : ℝ) - 1 / 2) ≤ rexp (-(c / U)) * gS U n := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hD := Dint_le hc hU (a := (n : ℝ) - 1 / 2) (by linarith)
  unfold gS
  have hb : 0 ≤ bS n := by unfold bS; positivity
  calc bS n * Dint c U ((n : ℝ) - 1 / 2) ≤ bS n * (rexp (-(c / U)) * U ^ ((n : ℝ) - 1 / 2) /
        ((n : ℝ) - 1 / 2)) := mul_le_mul_of_nonneg_left hD hb
    _ = _ := by ring

lemma gS_ratio {U : ℝ} (hU : 0 < U) {N : ℕ} (hN1 : 1 ≤ N) (hN : 4 * U ≤ ((N : ℝ) + 1) / 2)
    {n : ℕ} (hn : N ≤ n) : gS U (n + 1) ≤ gS U n / 2 := by
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hN1.trans hn
  unfold gS bS
  push_cast
  rw [show (n : ℝ) + 1 - 1 / 2 = ((n : ℝ) - 1 / 2) + 1 by ring, rpow_add hU, rpow_one,
    Nat.factorial_succ, pow_succ]
  push_cast
  have hpos : 0 < (n : ℝ) - 1 / 2 := by linarith
  have hP : 0 < U ^ ((n : ℝ) - 1 / 2) := rpow_pos_of_pos hU _
  have hF : (0 : ℝ) < (n ! : ℝ) := by positivity
  have h4 : (0 : ℝ) < 4 ^ n := by positivity
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have key : 4 * U * ((n : ℝ) - 1 / 2) * 2 ≤ ((n : ℝ) + 1) * ((n : ℝ) - 1 / 2 + 1) := by
    nlinarith
  have lhs : 4 ^ n * 4 / ((n + 1) * (n ! : ℝ)) * (U ^ ((n : ℝ) - 1 / 2) * U /
      ((n : ℝ) - 1 / 2 + 1)) * 2 =
      (4 ^ n / (n ! : ℝ) * (U ^ ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1 / 2))) *
        (4 * U * ((n : ℝ) - 1 / 2) * 2 / (((n : ℝ) + 1) * ((n : ℝ) - 1 / 2 + 1))) := by
    have hne : (n : ℝ) * 2 - 1 ≠ 0 := by linarith
    have hne2 : (n : ℝ) * 2 - 1 + 2 ≠ 0 := by linarith
    field_simp
  rw [lhs]
  have hq : 4 * U * ((n : ℝ) - 1 / 2) * 2 / (((n : ℝ) + 1) * ((n : ℝ) - 1 / 2 + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact key
  have hg : 0 ≤ 4 ^ n / (n ! : ℝ) * (U ^ ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1 / 2)) := by positivity
  calc _ ≤ (4 ^ n / (n ! : ℝ) * (U ^ ((n : ℝ) - 1 / 2) / ((n : ℝ) - 1 / 2))) * 1 :=
        mul_le_mul_of_nonneg_left hq hg
    _ = _ := mul_one _

/-- **Tail of the `β`-series** (Section 6.4.2): with `E β_n = D_{n-1/2} - α_n D_{-1/2}`, if
`16c ≤ (2N+1)(2N+2)/2`, `4U ≤ (N+1)/2` and `N ≥ 1`, then `∑_{n ≥ N} b_n E β_n` converges and is at
most twice the first term `E gS U N + |b_N α_N| D_{-1/2}` of its majorant. -/
theorem beta_tail {c U : ℝ} (hc : 0 < c) (hU : 0 < U) {N : ℕ} (hN1 : 1 ≤ N)
    (hNc : 16 * c ≤ (2 * N + 1) * (2 * N + 2) / 2) (hNU : 4 * U ≤ ((N : ℝ) + 1) / 2) :
    Summable (fun k => bS (N + k) * (betaS c U (N + k) * rexp (-(c / U)))) ∧
      |∑' k, bS (N + k) * (betaS c U (N + k) * rexp (-(c / U)))| ≤
        2 * (rexp (-(c / U)) * gS U N +
          (16 * c) ^ N / ((2 * N)! : ℝ) * Dint c U (-(1 / 2))) := by
  set E := rexp (-(c / U))
  set D0 := Dint c U (-(1 / 2))
  have hD0 : 0 < D0 := Dint_pos hc hU _
  have hE : 0 < E := exp_pos _
  -- the two majorant tails
  have hg := tail_le_two_mul (fun n => gS U n) N (fun n hn => by
    have := gS_ratio hU hN1 hNU hn
    rwa [Real.norm_of_nonneg (gS_nonneg hU (hN1.trans (Nat.le_succ_of_le hn))),
      Real.norm_of_nonneg (gS_nonneg hU (hN1.trans hn))])
  have ha := alpha_tail hc.le hNc
  have hf : Summable (fun k => (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ)) := by
    have := ha.1.abs
    simpa [abs_bS_mul_alphaS hc.le] using this
  -- termwise bound
  have hterm : ∀ k, |bS (N + k) * (betaS c U (N + k) * E)| ≤
      E * gS U (N + k) + (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ) * D0 := by
    intro k
    have hk : 1 ≤ N + k := hN1.trans (Nat.le_add_right _ _)
    have heq : bS (N + k) * (betaS c U (N + k) * E) =
        bS (N + k) * Dint c U (((N + k : ℕ) : ℝ) - 1 / 2) - bS (N + k) * alphaS c (N + k) * D0 := by
      rw [Dint_half_eq hc hU]; ring
    rw [heq]
    have hb : 0 ≤ bS (N + k) := by unfold bS; positivity
    have h1 : |bS (N + k) * Dint c U (((N + k : ℕ) : ℝ) - 1 / 2)| ≤ E * gS U (N + k) := by
      rw [abs_of_nonneg (mul_nonneg hb (Dint_pos hc hU _).le)]
      exact bS_Dint_le hc hU hk
    have h2 : |bS (N + k) * alphaS c (N + k) * D0| =
        (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ) * D0 := by
      rw [abs_mul, abs_bS_mul_alphaS hc.le, abs_of_pos hD0]
    exact (abs_sub _ _).trans (by rw [h2]; linarith)
  have hmaj : Summable (fun k => E * gS U (N + k) +
      (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ) * D0) :=
    (hg.1.mul_left E).add (hf.mul_right D0)
  have hs : Summable (fun k => bS (N + k) * (betaS c U (N + k) * E)) :=
    Summable.of_norm_bounded hmaj (fun k => by rw [Real.norm_eq_abs]; exact hterm k)
  refine ⟨hs, ?_⟩
  have hgsum : ∑' k, gS U (N + k) ≤ 2 * gS U N := by
    have := hg.2
    rwa [Real.norm_of_nonneg (tsum_nonneg (fun k => gS_nonneg hU
      (hN1.trans (Nat.le_add_right _ _)))), Real.norm_of_nonneg (gS_nonneg hU hN1)] at this
  have hfsum : ∑' k, (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ) ≤
      2 * ((16 * c) ^ N / ((2 * N)! : ℝ)) := by
    have h := tail_le_two_mul (fun n => (16 * c) ^ n / ((2 * n)! : ℝ)) N (fun n hn => by
      rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
      exact alpha_ratio hc.le hNc hn)
    rw [Real.norm_of_nonneg (tsum_nonneg (fun k => by positivity)),
      Real.norm_of_nonneg (by positivity)] at h
    exact h.2
  calc |∑' k, bS (N + k) * (betaS c U (N + k) * E)|
      ≤ ∑' k, (E * gS U (N + k) + (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ) * D0) := by
        rw [← Real.norm_eq_abs]
        exact tsum_of_norm_bounded hmaj.hasSum (fun k => by rw [Real.norm_eq_abs]; exact hterm k)
    _ = E * ∑' k, gS U (N + k) + (∑' k, (16 * c) ^ (N + k) / ((2 * (N + k))! : ℝ)) * D0 := by
        rw [(hg.1.mul_left E).tsum_add (hf.mul_right D0), tsum_mul_left, tsum_mul_right]
    _ ≤ E * (2 * gS U N) + (2 * ((16 * c) ^ N / ((2 * N)! : ℝ))) * D0 := by
        gcongr
    _ = _ := by ring

end ZetaF.StartVals
