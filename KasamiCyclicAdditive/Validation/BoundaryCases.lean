import Mathlib
import KasamiCyclicAdditive.Main

/-!
# Boundary cases for the main theorem

This file complements the headline proof with statement-level audits.

It records four kinds of boundary information:

* the hypotheses of the theorem are jointly satisfiable, with concrete
  Galois-field instances, including cases outside the easy branch
  `k ≡ ±1 (mod n)`; the executable audit separately records the
  trace-hyperplane behavior of the checked easy-branch cases;
* the bound `2 ≤ n` needed internally is derived from two distinct nonzero
  coefficients and `|K| = 2^n`, rather than assumed in the Challenge;
* the coefficient hypotheses are sharp: if the coefficients coincide, or if
  one vanishes, the triple equation degenerates and the count becomes
  `|Δ|^2` rather than the Carlet value;
* the small concrete instances used here are mirrored by the executable exact
  computation in `scripts/check_boundary_cases.py`.

The point is not merely to show that the main theorem is non-vacuous, but to
formalize nearby statements that the theorem deliberately does *not* claim.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ## Satisfiability of the coefficient hypotheses -/

/-- Any field with more than two elements contains two distinct nonzero
coefficients. -/
theorem exists_two_distinct_nonzero
    (h : 2 < Fintype.card K) : ∃ v₁ v₂ : K, v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ := by
  have hcard : 1 < (Finset.univ.erase (0 : K)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
  exact ⟨a, b, Finset.ne_of_mem_erase ha, Finset.ne_of_mem_erase hb, hab⟩

noncomputable local instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 2) := Classical.decEq _
noncomputable local instance : Fintype (GaloisField 2 3) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 3) := Classical.decEq _
noncomputable local instance : Fintype (GaloisField 2 4) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 4) := Classical.decEq _
noncomputable local instance : Fintype (GaloisField 2 5) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 5) := Classical.decEq _
noncomputable local instance : Fintype (GaloisField 2 7) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 7) := Classical.decEq _

/-- Non-vacuity witness: over `𝔽₄`, with `n = 2`, `k = 1`, the
main theorem gives the concrete count `2`. -/
theorem carlet_f4_instance : ∃ v₁ v₂ : GaloisField 2 2,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 1 v₁ v₂ = 2 := by
  have hcard : Fintype.card (GaloisField 2 2) = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 2) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 2) (n := 2) (k := 1)
    le_rfl (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-- A nontrivial odd-dimensional instance is inhabited as well: over `𝔽₈`,
`n = 3`, `k = 1`, the count is `8`. -/
theorem carlet_f8_k1_instance : ∃ v₁ v₂ : GaloisField 2 3,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 1 v₁ v₂ = 8 := by
  have hcard : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 3 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 3) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 3) (n := 3) (k := 1)
    le_rfl (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-- The complementary-parameter normalization is inhabited: over `𝔽₈`, the
even parameter `k = 2` also gives the count `8`. -/
theorem carlet_f8_k2_instance : ∃ v₁ v₂ : GaloisField 2 3,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 2 v₁ v₂ = 8 := by
  have hcard : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 3 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 3) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 3) (n := 3) (k := 2)
    (by norm_num) (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-- The even-dimensional geometric branch is inhabited: over `𝔽₁₆`,
`n = 4`, `k = 1`, the count is `32`. -/
theorem carlet_f16_instance : ∃ v₁ v₂ : GaloisField 2 4,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 1 v₁ v₂ = 32 := by
  have hcard : Fintype.card (GaloisField 2 4) = 2 ^ 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 4 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 4) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 4) (n := 4) (k := 1)
    le_rfl (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-! ### Instances outside the easy branch

Every instance above has `k ≡ ±1 (mod n)`.  In the easy-branch instances
checked in `Validation/BoundaryComputations.lean`, `Δ` is the trace hyperplane, so the
count is forced by hyperplane geometry.  The two instances below do not lie in
that branch; the executable audit verifies that their derivative images are
not even additive subspaces. -/

/-- The smallest instance with `k ≢ ±1 (mod n)`, where `Δ` is not a subspace:
over `𝔽₃₂`, `n = 5`, `k = 2`, the count is `128`. -/
theorem carlet_f32_k2_instance : ∃ v₁ v₂ : GaloisField 2 5,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 2 v₁ v₂ = 128 := by
  have hcard : Fintype.card (GaloisField 2 5) = 2 ^ 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 5 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 5) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 5) (n := 5) (k := 2)
    (by norm_num) (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-- An instance outside the congruence classes covered by the general
Nagy--Vajda proof, where `k mod n ∉ {1, 2, n-2, n-1}`: over `𝔽₁₂₈`,
`n = 7`, `k = 3`, the count is `2048`.  (Their exhaustive computation
for `n ≤ 13` also covers this finite case.) -/
theorem carlet_f128_k3_instance : ∃ v₁ v₂ : GaloisField 2 7,
    v₁ ≠ 0 ∧ v₂ ≠ 0 ∧ v₁ ≠ v₂ ∧
      coefficientTripleCount 3 v₁ v₂ = 2048 := by
  have hcard : Fintype.card (GaloisField 2 7) = 2 ^ 7 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 7 (by norm_num)
  have h2 : 2 < Fintype.card (GaloisField 2 7) := by rw [hcard]; norm_num
  obtain ⟨v₁, v₂, hv₁, hv₂, hne⟩ := exists_two_distinct_nonzero h2
  refine ⟨v₁, v₂, hv₁, hv₂, hne, ?_⟩
  have h := carlet_kasami_cyclic_additive_core (K := GaloisField 2 7) (n := 7) (k := 3)
    (by norm_num) (by norm_num) (by norm_num) hcard hv₁ hv₂ hne
  simpa using h

/-! ## Sharpness of the coefficient hypotheses -/

omit [Field K] [Fintype K] in
/-- The triples in `Δ³` with `x = y` number `|Δ|²`. -/
private lemma first_eq_second_card (Delta : Finset K) :
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.1 = p.2.1)).card = Delta.card ^ 2 := by
  calc
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.1 = p.2.1)).card
        = (Delta ×ˢ Delta).card := by
          refine Finset.card_nbij' (fun p => (p.1, p.2.2))
            (fun q => (q.1, q.1, q.2)) ?_ ?_ ?_ ?_ <;>
            simp +contextual [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Prod.ext_iff]
    _ = Delta.card ^ 2 := by simp [pow_two]

omit [Field K] [Fintype K] in
/-- The triples in `Δ³` with `y = z` number `|Δ|²`. -/
private lemma second_eq_third_card (Delta : Finset K) :
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.2.1 = p.2.2)).card = Delta.card ^ 2 := by
  calc
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.2.1 = p.2.2)).card
        = (Delta ×ˢ Delta).card := by
          refine Finset.card_nbij' (fun p => (p.1, p.2.1))
            (fun q => (q.1, q.2, q.2)) ?_ ?_ ?_ ?_ <;>
            simp +contextual [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Prod.ext_iff]
    _ = Delta.card ^ 2 := by simp [pow_two]

omit [Field K] [Fintype K] in
/-- The triples in `Δ³` with `x = z` number `|Δ|²`. -/
private lemma first_eq_third_card (Delta : Finset K) :
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.1 = p.2.2)).card = Delta.card ^ 2 := by
  calc
    ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p => p.1 = p.2.2)).card
        = (Delta ×ˢ Delta).card := by
          refine Finset.card_nbij' (fun p => (p.1, p.2.1))
            (fun q => (q.1, q.2, q.1)) ?_ ?_ ?_ ?_ <;>
            simp +contextual [Set.MapsTo, Set.LeftInvOn, Set.RightInvOn, Prod.ext_iff]
    _ = Delta.card ^ 2 := by simp [pow_two]

omit [Fintype K] [DecidableEq K] in
/-- With `v₁ = v₂ = v ≠ 0` the third coefficient vanishes and the coefficient
equation reduces to `x = y`. -/
private lemma same_coeff_equation [CharP K 2] {v x y z : K} (hv : v ≠ 0) :
    v * x + v * y + (v + v) * z = 0 ↔ x = y := by
  rw [CharTwo.add_self_eq_zero, zero_mul, add_zero, ← mul_add, mul_eq_zero]
  simp [hv, CharTwo.add_eq_zero]

omit [Fintype K] [DecidableEq K] in
/-- With `v₁ = 0` and `v₂ = v ≠ 0` it reduces to `y = z`. -/
private lemma zero_left_equation [CharP K 2] {v x y z : K} (hv : v ≠ 0) :
    0 * x + v * y + (0 + v) * z = 0 ↔ y = z := by
  simp only [zero_mul, zero_add, ← mul_add]
  rw [mul_eq_zero]
  simp [hv, CharTwo.add_eq_zero]

omit [Fintype K] [DecidableEq K] in
/-- With `v₂ = 0` and `v₁ = v ≠ 0` it reduces to `x = z`. -/
private lemma zero_right_equation [CharP K 2] {v x y z : K} (hv : v ≠ 0) :
    v * x + 0 * y + (v + 0) * z = 0 ↔ x = z := by
  simp only [zero_mul, add_zero, ← mul_add]
  rw [mul_eq_zero]
  simp [hv, CharTwo.add_eq_zero]

/-- If the two nonzero coefficients are equal, the third coefficient vanishes
and the equation is just `x = y`. Hence the count is `|Δ|^2`, not the Carlet
count. -/
theorem coefficientTripleCount_same [CharP K 2]
    (k : ℕ) {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k v v = (derivativeImage k K).card ^ 2 := by
  unfold coefficientTripleCount
  have hfilter :
      ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
        (fun p => v * p.1 + v * p.2.1 + (v + v) * p.2.2 = 0))
        = ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
          (fun p => p.1 = p.2.1)) := by
    apply Finset.filter_congr
    intro p hp
    exact same_coeff_equation hv
  rw [hfilter]
  exact first_eq_second_card (derivativeImage k K)

/-- If the first coefficient is zero and the second is nonzero, the equation
is just `y = z`, so the count is again `|Δ|^2`. -/
theorem coefficientTripleCount_zero_left [CharP K 2]
    (k : ℕ) {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k 0 v = (derivativeImage k K).card ^ 2 := by
  unfold coefficientTripleCount
  have hfilter :
      ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
        (fun p => 0 * p.1 + v * p.2.1 + (0 + v) * p.2.2 = 0))
        = ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
          (fun p => p.2.1 = p.2.2)) := by
    apply Finset.filter_congr
    intro p hp
    exact zero_left_equation hv
  rw [hfilter]
  exact second_eq_third_card (derivativeImage k K)

/-- If the second coefficient is zero and the first is nonzero, the equation
is just `x = z`, so the count is again `|Δ|^2`. -/
theorem coefficientTripleCount_zero_right [CharP K 2]
    (k : ℕ) {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k v 0 = (derivativeImage k K).card ^ 2 := by
  unfold coefficientTripleCount
  have hfilter :
      ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
        (fun p => v * p.1 + 0 * p.2.1 + (v + 0) * p.2.2 = 0))
        = ((derivativeImage k K ×ˢ derivativeImage k K ×ˢ derivativeImage k K).filter
          (fun p => p.1 = p.2.2)) := by
    apply Finset.filter_congr
    intro p hp
    exact zero_right_equation hv
  rw [hfilter]
  exact first_eq_third_card (derivativeImage k K)

/-- For every admissible literature parameter, the square of the derivative
image size is a factor two larger than the Carlet target.  Thus the degenerate
coefficient count `|Δ|^2` can never accidentally equal `2^(2n-3)`. -/
theorem derivativeImage_sq_ne_carlet_value [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n) :
    (derivativeImage k K).card ^ 2 ≠ 2 ^ (2 * n - 3) := by
  obtain ⟨hrpos, hrlt, hrcoprime⟩ := mod_parameter_admissible hn hkn
  have hhalf :=
    kasami_half_size (K := K) (n := n) (k := k % n)
      hrpos hrlt hrcoprime hcard
  have himage :
      (derivativeImage k K).card = (derivativeImage (k % n) K).card := by
    rw [derivativeImage_mod_degree (K := K) (n := n) (k := k) hcard]
  rw [hcard] at hhalf
  have hpow : 2 * 2 ^ (n - 1) = 2 ^ n := by
    have hpred := Nat.two_pow_pred_add_two_pow_pred (show 0 < n by omega)
    omega
  have himg_norm : (derivativeImage (k % n) K).card = 2 ^ (n - 1) := by
    omega
  have himg : (derivativeImage k K).card = 2 ^ (n - 1) := by
    rw [himage, himg_norm]
  rw [himg]
  intro h
  have hpoweq : 2 ^ ((n - 1) * 2) = 2 ^ (2 * n - 3) := by
    simpa [pow_mul] using h
  have hexp : (n - 1) * 2 = 2 * n - 3 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hpoweq
  omega

/-- The distinctness hypothesis is sharp in every admissible field: if
`v₁ = v₂ ≠ 0`, the count is not the Carlet value. -/
theorem coefficientTripleCount_same_ne_carlet [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k v v ≠ 2 ^ (2 * n - 3) := by
  rw [coefficientTripleCount_same k hv]
  exact derivativeImage_sq_ne_carlet_value hkn hn hcard

/-- The first nonzero hypothesis is sharp in every admissible field. -/
theorem coefficientTripleCount_zero_left_ne_carlet [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k 0 v ≠ 2 ^ (2 * n - 3) := by
  rw [coefficientTripleCount_zero_left k hv]
  exact derivativeImage_sq_ne_carlet_value hkn hn hcard

/-- The second nonzero hypothesis is sharp in every admissible field. -/
theorem coefficientTripleCount_zero_right_ne_carlet [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    {v : K} (hv : v ≠ 0) :
    coefficientTripleCount k v 0 ≠ 2 ^ (2 * n - 3) := by
  rw [coefficientTripleCount_zero_right k hv]
  exact derivativeImage_sq_ne_carlet_value hkn hn hcard

/-- Concrete failure of the distinctness hypothesis over `𝔽₄`: with the two
coefficients both equal to `1`, the count is `4`, whereas the Carlet value for
`n = 2` is `2`. -/
theorem coefficientTripleCount_f4_same : coefficientTripleCount (K := GaloisField 2 2) 1 1 1 = 4 := by
  rw [coefficientTripleCount_same 1 one_ne_zero]
  have hcard : Fintype.card (GaloisField 2 2) = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  have hhalf := kasami_half_size (K := GaloisField 2 2) (n := 2) (k := 1)
    le_rfl (by norm_num) (by norm_num) hcard
  rw [hcard] at hhalf
  have himg : (derivativeImage 1 (GaloisField 2 2)).card = 2 := by omega
  rw [himg]
  norm_num

/-- Concrete failure of the nonzero hypothesis over `𝔽₄`: the distinct pair
`(0,1)` gives count `4`, again not the Carlet value `2`. -/
theorem coefficientTripleCount_f4_zero_left : coefficientTripleCount (K := GaloisField 2 2) 1 0 1 = 4 := by
  rw [coefficientTripleCount_zero_left 1 one_ne_zero]
  have hcard : Fintype.card (GaloisField 2 2) = 2 ^ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by norm_num)
  have hhalf := kasami_half_size (K := GaloisField 2 2) (n := 2) (k := 1)
    le_rfl (by norm_num) (by norm_num) hcard
  rw [hcard] at hhalf
  have himg : (derivativeImage 1 (GaloisField 2 2)).card = 2 := by omega
  rw [himg]
  norm_num

end KasamiCyclicAdditive
