/-
# The irrationality bound for Khinchin's constant (Proposition 6.4)

The proposition rests on two facts about the convergents, which we prove:
* `farey_denom_ge`: a rational strictly between Farey neighbours `a/b < c/e` (`bc - ae = 1`) has
  denominator at least `b + e`;
* `den_ge_of_between`: if `x_t = (t p_N + p_{N-1})/(t q_N + q_{N-1})` with
  `p_N q_{N-1} - p_{N-1} q_N = ±1`, then every rational strictly between `x_{T₀}` and `x_{T₁}`
  (`1 ≤ T₀ < T₁`) has denominator at least `(T₀+1) q_N + q_{N-1}`.
With `T₀ = 9` this is the step "its denominator is at least `q(x_{10}) = 10 q_N + q_{N-1}`".
The numerical inputs (the `10⁷` digits and the interval `I`) are of course not formalized.
-/
import ZetaF.Deps

namespace ZetaF

/-- **Farey neighbours.** -/
theorem farey_denom_ge {a b c e p q : ℤ} (hb : 0 < b) (he : 0 < e) (hq : 0 < q)
    (hdet : b * c - a * e = 1) (h1 : (a : ℚ) / b < p / q) (h2 : (p : ℚ) / q < c / e) :
    b + e ≤ q := by
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have he' : (0 : ℚ) < e := by exact_mod_cast he
  have hq' : (0 : ℚ) < q := by exact_mod_cast hq
  rw [div_lt_div_iff₀ hb' hq'] at h1
  rw [div_lt_div_iff₀ hq' he'] at h2
  have h1' : a * q < p * b := by exact_mod_cast h1
  have h2' : p * e < c * q := by exact_mod_cast h2
  have e1 : q = b * (c * q - p * e) + e * (p * b - a * q) := by linear_combination (-q) * hdet
  nlinarith

section Convergents

variable (pN pN1 qN qN1 : ℤ)

/-- `x_t = (t p_N + p_{N-1})/(t q_N + q_{N-1})`. -/
def xt (t : ℕ) : ℚ := ((t : ℤ) * pN + pN1 : ℤ) / ((t : ℤ) * qN + qN1 : ℤ)

variable {pN pN1 qN qN1}

lemma den_pos (hq : 0 < qN) (hq1 : 0 ≤ qN1) {t : ℕ} (ht : 1 ≤ t) : 0 < (t : ℤ) * qN + qN1 := by
  have : (1 : ℤ) ≤ t := by exact_mod_cast ht
  nlinarith

lemma xt_succ_sub (hq : 0 < qN) (hq1 : 0 ≤ qN1) {t : ℕ} (ht : 1 ≤ t) :
    xt pN pN1 qN qN1 (t + 1) - xt pN pN1 qN qN1 t =
      ((pN * qN1 - pN1 * qN : ℤ) : ℚ) /
        ((((t + 1 : ℕ) : ℤ) * qN + qN1 : ℤ) * (((t : ℤ) * qN + qN1 : ℤ)) : ℚ) := by
  have h0 := den_pos hq hq1 ht
  have h1 := den_pos hq hq1 (show 1 ≤ t + 1 by omega)
  have h0' : ((t : ℤ) * qN + qN1 : ℚ) ≠ 0 := by exact_mod_cast h0.ne'
  have h1' : ((((t + 1 : ℕ) : ℤ) * qN + qN1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast h1.ne'
  unfold xt
  push_cast at h0' h1' ⊢
  field_simp
  ring

/-- With `p_N q_{N-1} - p_{N-1} q_N = 1`, the `x_t` increase. -/
lemma xt_strictMono (hq : 0 < qN) (hq1 : 0 ≤ qN1) (hdet : pN * qN1 - pN1 * qN = 1) {s t : ℕ}
    (hs : 1 ≤ s) (hst : s < t) : xt pN pN1 qN qN1 s < xt pN pN1 qN qN1 t := by
  induction t with
  | zero => omega
  | succ t ih =>
    have hstep : xt pN pN1 qN qN1 t < xt pN pN1 qN qN1 (t + 1) := by
      have ht : 1 ≤ t := by omega
      rw [← sub_pos, xt_succ_sub hq hq1 ht, hdet]
      have h0 := den_pos hq hq1 ht
      have h1 := den_pos hq hq1 (show 1 ≤ t + 1 by omega)
      apply div_pos (by norm_num)
      exact_mod_cast mul_pos h1 h0
    rcases (Nat.lt_succ_iff.1 hst).lt_or_eq with h | h
    · exact (ih h).trans hstep
    · subst h; exact hstep

/-- `x_t` in lowest terms has denominator `t q_N + q_{N-1}`. -/
lemma den_xt (hq : 0 < qN) (hq1 : 0 ≤ qN1) (hdet : pN * qN1 - pN1 * qN = 1) {t : ℕ} (ht : 1 ≤ t) :
    ((xt pN pN1 qN qN1 t).den : ℤ) = (t : ℤ) * qN + qN1 := by
  have h0 := den_pos hq hq1 ht
  have hcop : IsCoprime ((t : ℤ) * pN + pN1) ((t : ℤ) * qN + qN1) :=
    ⟨-qN, pN, by linear_combination hdet⟩
  unfold xt
  rw [Rat.den_div_eq_of_coprime h0 (Int.isCoprime_iff_gcd_eq_one.1 hcop)]

lemma den_ge_of_xt_lt_lt (hq : 0 < qN) (hq1 : 0 ≤ qN1) (hdet : pN * qN1 - pN1 * qN = 1)
    {t : ℕ} (ht : 1 ≤ t) {x : ℚ} (h1 : xt pN pN1 qN qN1 t < x)
    (h2 : x < xt pN pN1 qN qN1 (t + 1)) :
    (t : ℤ) * qN + qN1 + ((((t + 1 : ℕ) : ℤ) * qN + qN1)) ≤ x.den := by
  have h0 := den_pos hq hq1 ht
  have h1' := den_pos hq hq1 (show 1 ≤ t + 1 by omega)
  have hx : x = (x.num : ℚ) / ((x.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den x).symm
  rw [hx] at h1 h2
  unfold xt at h1 h2
  exact farey_denom_ge h0 h1' (by exact_mod_cast x.den_pos) (by push_cast; linear_combination hdet)
    h1 h2

/-- The increasing case. -/
lemma den_ge_of_between_mono (hq : 0 < qN) (hq1 : 0 ≤ qN1) (hdet : pN * qN1 - pN1 * qN = 1)
    {T₀ T₁ : ℕ} (hT₀ : 1 ≤ T₀) (hT : T₀ < T₁) {x : ℚ} (h1 : xt pN pN1 qN qN1 T₀ < x)
    (h2 : x < xt pN pN1 qN qN1 T₁) : ((T₀ + 1 : ℕ) : ℤ) * qN + qN1 ≤ x.den := by
  classical
  have hex : ∃ t, T₀ < t ∧ x ≤ xt pN pN1 qN qN1 t := ⟨T₁, hT, h2.le⟩
  set t₁ := Nat.find hex
  obtain ⟨ht₁, hx₁⟩ := Nat.find_spec hex
  have hprev : xt pN pN1 qN qN1 (t₁ - 1) < x := by
    by_cases h : t₁ - 1 = T₀
    · rw [h]; exact h1
    · have := Nat.find_min hex (show t₁ - 1 < t₁ by omega)
      push Not at this
      exact this (by omega)
  have hmono : ∀ s t : ℕ, 1 ≤ s → s ≤ t → ((s : ℤ) * qN + qN1) ≤ (t : ℤ) * qN + qN1 := by
    intro s t _ hst
    have : (s : ℤ) ≤ t := by exact_mod_cast hst
    nlinarith
  rcases hx₁.lt_or_eq with hlt | heq
  · have := den_ge_of_xt_lt_lt hq hq1 hdet (show 1 ≤ t₁ - 1 by omega) hprev
      (by rw [show t₁ - 1 + 1 = t₁ by omega]; exact hlt)
    have h3 := hmono (T₀ + 1) t₁ (by omega) (by omega)
    have h4 := den_pos hq hq1 (show 1 ≤ t₁ - 1 by omega)
    rw [show t₁ - 1 + 1 = t₁ by omega] at this
    linarith
  · rw [heq, den_xt hq hq1 hdet (by omega)]
    exact hmono (T₀ + 1) t₁ (by omega) (by omega)

/-- **Proposition 6.4, the denominator bound.** If `p_N q_{N-1} - p_{N-1} q_N = ±1`, `q_N > 0`,
`q_{N-1} ≥ 0`, `1 ≤ T₀ < T₁`, then every rational strictly between `x_{T₀}` and `x_{T₁}` has
denominator at least `(T₀+1) q_N + q_{N-1}`. -/
theorem den_ge_of_between (hq : 0 < qN) (hq1 : 0 ≤ qN1)
    (hdet : pN * qN1 - pN1 * qN = 1 ∨ pN * qN1 - pN1 * qN = -1)
    {T₀ T₁ : ℕ} (hT₀ : 1 ≤ T₀) (hT : T₀ < T₁) {x : ℚ}
    (hx : min (xt pN pN1 qN qN1 T₀) (xt pN pN1 qN qN1 T₁) < x ∧
      x < max (xt pN pN1 qN qN1 T₀) (xt pN pN1 qN qN1 T₁)) :
    ((T₀ + 1 : ℕ) : ℤ) * qN + qN1 ≤ x.den := by
  rcases hdet with hdet | hdet
  · have hlt := xt_strictMono hq hq1 hdet (by omega) hT
    rw [min_eq_left hlt.le, max_eq_right hlt.le] at hx
    exact den_ge_of_between_mono hq hq1 hdet hT₀ hT hx.1 hx.2
  · have hdet' : (-pN) * qN1 - (-pN1) * qN = 1 := by linear_combination -hdet
    have hneg : ∀ t, xt (-pN) (-pN1) qN qN1 t = -xt pN pN1 qN qN1 t := fun t => by
      unfold xt; push_cast; ring
    have hlt := xt_strictMono hq hq1 hdet' (by omega) hT
    rw [hneg, hneg, neg_lt_neg_iff] at hlt
    rw [min_eq_right hlt.le, max_eq_left hlt.le] at hx
    have := den_ge_of_between_mono hq hq1 hdet' hT₀ hT (x := -x)
      (by rw [hneg]; exact neg_lt_neg hx.2) (by rw [hneg]; exact neg_lt_neg hx.1)
    rwa [Rat.den_neg_eq_den] at this

end Convergents

end ZetaF
