/-
# Even and odd parts of Fuchsian-holonomic sequences (first paragraph of the proof of Lemma 3.1)

The paper argues: the LCLM of `L` and `L⁻` (`x ↦ -x`) annihilates `f(x) ± f(-x)` and is Fuchsian by
Fuchs's criterion; then the even powers of the operator annihilate the even part, which in
`y = x²` gives an operator with (H).  We formalize every step except the Fuchs step, which we isolate
as the hypothesis `FuchsianAddClosed K` (the sum of two Fuchsian-holonomic sequences is
Fuchsian-holonomic, i.e. the LCLM of two (H)-operators can be chosen with (H)):
* `IsFuchsianHolonomic.alternate`: `n ↦ (-1)^n a_n` (the operator `L⁻`),
* `IsFuchsianHolonomic.shift`: `n ↦ a_{n+1}` when `a_0 = 0` (the paper's `L x = x L|_{θ ↦ θ+1}`),
* `IsFuchsianHolonomic.halve`: `m ↦ e_{2m}` when `e` vanishes at odd indices (`y = x²`),
and hence `evenPartFuchsian_of_addClosed`, `oddPartFuchsian_of_addClosed`.
-/
import ZetaF.Open
import ZetaF.Holonomic.GammaTwist

open Polynomial Finset Filter

namespace ZetaF

/-- **The Fuchs step**, as a hypothesis: Fuchsian-holonomic sequences (over `K`) are closed under
addition. -/
def FuchsianAddClosed (K : Subfield ℂ) : Prop :=
  ∀ a b : ℕ → ℂ, IsFuchsianHolonomic K a → IsFuchsianHolonomic K b →
    IsFuchsianHolonomic K (a + b)

lemma coeff_comp_mem {K : Subfield ℂ} {p q : ℂ[X]} (hp : ∀ i, p.coeff i ∈ K)
    (hq : ∀ i, q.coeff i ∈ K) (i : ℕ) : (p.comp q).coeff i ∈ K := by
  have hp' : p ∈ lifts (K.subtype : K →+* ℂ) :=
    (lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, hp n⟩, rfl⟩
  have hq' : q ∈ lifts (K.subtype : K →+* ℂ) :=
    (lifts_iff_coeff_lifts _).2 fun n => ⟨⟨_, hq n⟩, rfl⟩
  obtain ⟨p', rfl⟩ := (mem_lifts _).1 hp'
  obtain ⟨q', rfl⟩ := (mem_lifts _).1 hq'
  rw [← map_comp, coeff_map]
  exact SetLike.coe_mem _

namespace ThetaOp

/-- Build an operator from its coefficients `j ↦ c j` for `j ≤ r`. -/
noncomputable def ofCoeffs (r : ℕ) (c : ℕ → ℂ[X]) : ThetaOp ℂ :=
  ∑ j ∈ range (r + 1), monomial j (c j)

lemma coeff_ofCoeffs (r : ℕ) (c : ℕ → ℂ[X]) (j : ℕ) :
    (ofCoeffs r c).coeff j = if j ≤ r then c j else 0 := by
  rw [ofCoeffs, finsetSum_coeff]
  split_ifs with hj
  · rw [sum_eq_single j]
    · simp
    · intro b _ hb; simp [coeff_monomial, hb]
    · intro h; simp at h; omega
  · rw [sum_eq_zero]
    intro b hb; simp only [mem_range] at hb
    rw [Polynomial.coeff_monomial, Finsupp.single_apply, ite_eq_right (by omega)]

lemma isFuchsian_ofCoeffs {L : ThetaOp ℂ} (hL : L.IsFuchsian) (c : ℕ → ℂ[X])
    (h0 : c 0 ≠ 0) (hd0 : (c 0).natDegree = (L.coeff 0).natDegree)
    (hd : ∀ j ≤ L.natDegree, (c j).natDegree ≤ (L.coeff j).natDegree) :
    (ofCoeffs L.natDegree c).IsFuchsian := by
  refine ⟨by rw [coeff_ofCoeffs, ite_eq_left (Nat.zero_le _)]; exact h0, fun j => ?_⟩
  rw [coeff_ofCoeffs, coeff_ofCoeffs, ite_eq_left (Nat.zero_le _), hd0]
  split_ifs with hj
  · exact (hd j hj).trans (hL.2 j)
  · simp

end ThetaOp

open ThetaOp

lemma IsFuchsianHolonomic.smul {K : Subfield ℂ} {a : ℕ → ℂ} (h : IsFuchsianHolonomic K a)
    (c : ℂ) : IsFuchsianHolonomic K (c • a) := by
  obtain ⟨L, hL, hann, hK⟩ := h
  refine ⟨L, hL, ?_, hK⟩
  filter_upwards [hann] with n hn
  rw [applySeq_smul, hn, mul_zero]

/-- `n ↦ (-1)^n a_n`, via the operator `L⁻` with coefficients `(-1)^j q_j`. -/
theorem IsFuchsianHolonomic.alternate {K : Subfield ℂ} {a : ℕ → ℂ}
    (h : IsFuchsianHolonomic K a) : IsFuchsianHolonomic K fun n => (-1) ^ n * a n := by
  obtain ⟨L, hL, hann, hK⟩ := h
  set c : ℕ → ℂ[X] := fun j => C ((-1 : ℂ) ^ j) * L.coeff j
  have hc : ∀ j, (c j).natDegree = (L.coeff j).natDegree := fun j => by
    simp only [c]; rw [natDegree_C_mul (pow_ne_zero _ (by norm_num))]
  refine ⟨ofCoeffs L.natDegree c, isFuchsian_ofCoeffs hL c (by simpa [c] using hL.1) (hc 0)
    (fun j _ => (hc j).le), ?_, fun j i => ?_⟩
  · filter_upwards [hann] with n hn
    unfold applySeq at hn ⊢
    have : ∀ j ∈ range (n + 1), ((ofCoeffs L.natDegree c).coeff j).eval ((n - j : ℕ) : ℂ) *
        ((-1) ^ (n - j) * a (n - j)) =
        (-1) ^ n * ((L.coeff j).eval ((n - j : ℕ) : ℂ) * a (n - j)) := by
      intro j hj
      simp only [mem_range] at hj
      rw [coeff_ofCoeffs]
      split_ifs with hjr
      · simp only [c, eval_mul, eval_C]
        rw [show (-1 : ℂ) ^ n = (-1) ^ j * (-1) ^ (n - j) by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]]
        ring
      · rw [show L.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]; simp
    rw [sum_congr rfl this, ← mul_sum, hn, mul_zero]
  · rw [coeff_ofCoeffs]
    split_ifs
    · simp only [c, coeff_C_mul]
      exact K.mul_mem (K.pow_mem (K.neg_mem K.one_mem) _) (hK j i)
    · simp [K.zero_mem]

/-- `n ↦ a_{n+1}` when `a_0 = 0`, via the coefficients `q_j(θ + 1)`. -/
theorem IsFuchsianHolonomic.shift {K : Subfield ℂ} {a : ℕ → ℂ} (h : IsFuchsianHolonomic K a)
    (ha0 : a 0 = 0) : IsFuchsianHolonomic K fun n => a (n + 1) := by
  obtain ⟨L, hL, hann, hK⟩ := h
  set c : ℕ → ℂ[X] := fun j => (L.coeff j).comp (X + 1)
  have hc : ∀ j, (c j).natDegree = (L.coeff j).natDegree := fun j => by
    simp only [c]; rw [natDegree_comp]; simp
  have hc0 : c 0 ≠ 0 := by
    intro h0
    have := congrArg natDegree h0
    simp only [c] at h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h0⟩
    · exact hL.1 h0
    · have := congrArg natDegree h0; simp at this
  refine ⟨ofCoeffs L.natDegree c, isFuchsian_ofCoeffs hL c hc0 (hc 0) (fun j _ => (hc j).le),
    ?_, fun j i => ?_⟩
  · filter_upwards [hann.filter_mono (tendsto_add_atTop_nat 1)] with n hn
    have hn : L.applySeq a (n + 1) = 0 := hn
    unfold applySeq at hn ⊢
    rw [sum_range_succ, Nat.sub_self, ha0, mul_zero, add_zero] at hn
    rw [← hn]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    have e : n + 1 - j = n - j + 1 := by omega
    rw [coeff_ofCoeffs, e]
    split_ifs with hjr
    · simp only [c, eval_comp, eval_add, eval_X, eval_one]; push_cast; ring_nf
    · rw [show L.coeff j = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · rw [coeff_ofCoeffs]
    split_ifs
    · exact coeff_comp_mem (hK j) (fun i => by
        rw [coeff_add, coeff_X, coeff_one]
        split_ifs <;> simp [K.zero_mem, K.one_mem, K.add_mem]) i
    · simp [K.zero_mem]

lemma sum_range_two_mul_add_one {g : ℕ → ℂ} (M : ℕ) (hg : ∀ i < M, g (2 * i + 1) = 0) :
    ∑ j ∈ range (2 * M + 1), g j = ∑ i ∈ range (M + 1), g (2 * i) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) + 1 = 2 * M + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      ih (fun i hi => hg i (by omega)), hg M (by omega), add_zero, sum_range_succ (n := M + 1)]
    ring_nf

/-- `m ↦ e_{2m}` when `e` vanishes at odd indices, via the coefficients `q_{2i}(2θ)` (`y = x²`). -/
theorem IsFuchsianHolonomic.halve {K : Subfield ℂ} {e : ℕ → ℂ} (h : IsFuchsianHolonomic K e)
    (he : ∀ n, Odd n → e n = 0) : IsFuchsianHolonomic K fun m => e (2 * m) := by
  obtain ⟨L, hL, hann, hK⟩ := h
  set c : ℕ → ℂ[X] := fun i => (L.coeff (2 * i)).comp (C 2 * X)
  have hc : ∀ i, (c i).natDegree = (L.coeff (2 * i)).natDegree := fun i => by
    simp only [c]; rw [natDegree_comp]
    rw [natDegree_C_mul_X _ (by norm_num), mul_one]
  have hc0 : c 0 ≠ 0 := by
    intro h0
    simp only [c, mul_zero] at h0
    rw [comp_eq_zero_iff] at h0
    rcases h0 with h0 | ⟨-, h0⟩
    · exact hL.1 h0
    · have := congrArg natDegree h0
      rw [natDegree_C_mul_X _ (by norm_num), natDegree_C] at this; exact one_ne_zero this
  have hL' : (ofCoeffs L.natDegree c).IsFuchsian := by
    refine ⟨by rw [coeff_ofCoeffs, ite_eq_left (Nat.zero_le _)]; exact hc0, fun i => ?_⟩
    rw [coeff_ofCoeffs, coeff_ofCoeffs, ite_eq_left (Nat.zero_le _), hc 0]
    split_ifs
    · rw [hc i]; exact hL.2 _
    · simp
  refine ⟨ofCoeffs L.natDegree c, hL', ?_, fun j i => ?_⟩
  · filter_upwards [hann.filter_mono (Filter.tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))]
      with m hm
    have hm : L.applySeq e (2 * m) = 0 := hm
    unfold applySeq at hm ⊢
    set g : ℕ → ℂ := fun j => (L.coeff j).eval ((2 * m - j : ℕ) : ℂ) * e (2 * m - j)
    have hg : ∀ i < m, g (2 * i + 1) = 0 := fun i hi => by
      simp only [g]
      rw [he _ (by rw [show 2 * m - (2 * i + 1) = 2 * (m - i - 1) + 1 by omega]; exact odd_two_mul_add_one _),
        mul_zero]
    have := sum_range_two_mul_add_one m hg
    simp only [g] at this
    rw [show 2 * m + 1 = 2 * m + 1 from rfl] at this
    rw [← hm, this]
    refine sum_congr rfl fun i hi => ?_
    simp only [mem_range] at hi
    rw [coeff_ofCoeffs]
    have e2 : 2 * m - 2 * i = 2 * (m - i) := by omega
    split_ifs with hir
    · simp only [c, eval_comp, eval_mul, eval_C, eval_X, e2]; push_cast; ring_nf
    · rw [show L.coeff (2 * i) = 0 from coeff_eq_zero_of_natDegree_lt (by omega)]; simp
  · rw [coeff_ofCoeffs]
    split_ifs
    · have two_mem : (2 : ℂ) ∈ K := by
        norm_num
      exact coeff_comp_mem (hK _) (fun i => by
        rw [coeff_C_mul, coeff_X]
        split_ifs
        · rw [mul_one]; exact two_mem
        · rw [mul_zero]; exact K.zero_mem) i
    · simp [K.zero_mem]

lemma even_part_eq (a : ℕ → ℂ) :
    (2 : ℂ)⁻¹ • (a + fun n => (-1) ^ n * a n) = fun n => if Even n then a n else 0 := by
  funext n
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow]; ring

lemma odd_part_eq (a : ℕ → ℂ) :
    (2 : ℂ)⁻¹ • (a + (-1 : ℂ) • fun n => (-1) ^ n * a n) = fun n => if Even n then 0 else a n := by
  funext n
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  split_ifs with h
  · rw [h.neg_one_pow]; ring
  · rw [(Nat.not_even_iff_odd.1 h).neg_one_pow]; ring

/-- **Even part**, given the Fuchs step. -/
theorem IsFuchsianHolonomic.evenPart {K : Subfield ℂ} (hadd : FuchsianAddClosed K) {a : ℕ → ℂ}
    (h : IsFuchsianHolonomic K a) : IsFuchsianHolonomic K fun m => a (2 * m) := by
  have he := (hadd _ _ h h.alternate).smul (2 : ℂ)⁻¹
  rw [even_part_eq] at he
  have := he.halve fun n hn => by simp [Nat.not_even_iff_odd.2 hn]
  simpa using this

/-- **Odd part**, given the Fuchs step. -/
theorem IsFuchsianHolonomic.oddPart {K : Subfield ℂ} (hadd : FuchsianAddClosed K) {a : ℕ → ℂ}
    (h : IsFuchsianHolonomic K a) : IsFuchsianHolonomic K fun m => a (2 * m + 1) := by
  have ho := (hadd _ _ h (h.alternate.smul (-1))).smul (2 : ℂ)⁻¹
  rw [odd_part_eq] at ho
  have hs := ho.shift (by simp)
  have := hs.halve fun n hn => by
    show (if Even (n + 1) then (0 : ℂ) else a (n + 1)) = 0
    rw [ite_eq_left (by rcases hn with ⟨k, rfl⟩; exact ⟨k + 1, by ring⟩)]
  have e : (fun m => if Even (2 * m + 1) then (0 : ℂ) else a (2 * m + 1)) =
      fun m => a (2 * m + 1) := funext fun m => by
    rw [ite_eq_right (Nat.not_even_iff_odd.2 (odd_two_mul_add_one m))]
  exact e ▸ this

theorem evenPartFuchsian_of_addClosed (h : FuchsianAddClosed ⊤) : EvenPartFuchsian :=
  fun _ ha => ha.evenPart h

theorem oddPartFuchsian_of_addClosed (h : FuchsianAddClosed ⊤) : OddPartFuchsian :=
  fun _ ha => ha.oddPart h

/-- **Lemma 3.1 (recurrence form), given the Fuchs step.** If `f = ∑ a_n x^n` is Fuchsian-holonomic,
then for every `σ₀` the coefficients `γ_m = a_{2m}/Γ(m+σ₀)` of `G₀` (and `a_{2m+1}/Γ(m+σ₀)` of `G₁`)
are annihilated by an (H)-operator `∑_j u^j Q̃_j(θ)` in which the top power of `θ` has a nonzero
constant coefficient (so that dividing by it gives the system (10) with polynomial coefficients). -/
theorem lemma31_recurrence {K : Subfield ℂ} (hadd : FuchsianAddClosed K) {a : ℕ → ℂ}
    (ha : IsFuchsianHolonomic K a) (σ₀ : ℂ) (δ : ℕ) (hδ : δ ≤ 1) :
    ∃ L : ThetaOp ℂ, L.IsFuchsian ∧
      L.AnnihilatesEventually (fun m => a (2 * m + δ) * (Complex.Gamma (m + σ₀))⁻¹) ∧
      ∃ d : ℕ, ((L.coeff 0).coeff d ≠ 0 ∧ ∀ j, 1 ≤ j → (L.coeff j).coeff d = 0) ∧
        ∀ j, (L.coeff j).natDegree ≤ d := by
  have hpart : IsFuchsianHolonomic K fun m => a (2 * m + δ) := by
    interval_cases δ
    · simpa using ha.evenPart hadd
    · exact ha.oddPart hadd
  obtain ⟨L, hL, hann, -⟩ := hpart
  refine ⟨L.gammaTwist σ₀, hL.gammaTwist σ₀, annihilatesEventually_gammaTwist σ₀ hann,
    (L.coeff 0).natDegree + L.natDegree, ?_, fun j => ?_⟩
  · obtain ⟨h1, h2⟩ := gammaTwist_top_coeff hL σ₀
    exact ⟨by rw [h1]; exact leadingCoeff_ne_zero.2 hL.1, h2⟩
  · have := (hL.gammaTwist σ₀).2 j
    rw [(natDegree_coeff_zero_gammaTwist L σ₀ hL.1).1] at this
    exact this

end ZetaF
