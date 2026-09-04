import KasamiCyclicAdditive.Main
import KasamiCyclicAdditive.Validation.LiteratureSpecification

/-!
# Semantic audit bridge for the literature specification

`Validation/LiteratureSpecification.lean` deliberately restates the target without using
the implementation definitions.  This file is the bridge: it proves that the
independent, source-shaped objects encode exactly the same derivative image and
coefficient triple count as the definitions used by the proof.

The important theorem here is not another proof of the conjecture; it is the
equivalence of two differently structured specifications.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The independently restated Kasami exponent agrees with the implementation
exponent. -/
theorem literatureKasamiExponent_eq (k : ℕ) :
    LiteratureSpecification.kasamiExponent k = kasamiExponent k := by
  rfl

omit [Fintype K] [DecidableEq K] in
/-- The independently restated derivative value agrees pointwise with the
implementation derivative. -/
theorem literatureDerivativeValue_eq (k : ℕ) (b : K) :
    LiteratureSpecification.derivativeValue k b = kasamiDerivative k b := by
  rfl

/-- Existential derivative-image membership in the literature specification is
equivalent to membership in the implementation `Finset.image`. -/
theorem literatureInDerivativeImage_iff_mem_derivativeImage
    (k : ℕ) (x : K) :
    LiteratureSpecification.InDerivativeImage k x ↔
      x ∈ derivativeImage k K := by
  simp [LiteratureSpecification.InDerivativeImage,
    LiteratureSpecification.derivativeValue,
    LiteratureSpecification.kasamiExponent,
    derivativeImage, kasamiDerivative, kasamiExponent]

/-- The independently specified solution set over all of `K³` is exactly the
implementation solution set obtained by first forming `Δ³`.  This checks both
the derivative-image membership encoding and the coordinate projections
`p.1`, `p.2.1`, `p.2.2`. -/
theorem literatureCoefficientTriples_eq
    (k : ℕ) (v₁ v₂ : K) :
    LiteratureSpecification.coefficientTriples k v₁ v₂ =
      ((derivativeImage k K) ×ˢ (derivativeImage k K) ×ˢ (derivativeImage k K)).filter
        (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0) := by
  classical
  ext p
  simp [LiteratureSpecification.coefficientTriples,
    LiteratureSpecification.IsCoefficientTriple,
    literatureInDerivativeImage_iff_mem_derivativeImage]
  tauto

/-- Consequently the independently specified cardinality is exactly
`coefficientTripleCount`. -/
theorem literatureCoefficientTripleCount_eq
    (k : ℕ) (v₁ v₂ : K) :
    LiteratureSpecification.coefficientTripleCount k v₁ v₂ =
      coefficientTripleCount k v₁ v₂ := by
  unfold LiteratureSpecification.coefficientTripleCount coefficientTripleCount
  rw [literatureCoefficientTriples_eq]

/-- The source-shaped conclusion is logically equivalent to the implementation
conclusion for every choice of parameters. -/
theorem literatureCarletConclusion_iff
    (n k : ℕ) (v₁ v₂ : K) :
    LiteratureSpecification.CarletKasamiConclusion n k v₁ v₂ ↔
      coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  unfold LiteratureSpecification.CarletKasamiConclusion
  rw [literatureCoefficientTripleCount_eq]

/-- The proved main theorem therefore also discharges the independently
restated literature specification. -/
theorem carlet_kasami_cyclic_additive_literature_spec
    [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    LiteratureSpecification.CarletKasamiConclusion n k v₁ v₂ := by
  apply (literatureCarletConclusion_iff n k v₁ v₂).2
  exact carlet_kasami_cyclic_additive_literature
    hkn hcard hv₁ hv₂ hne

end KasamiCyclicAdditive
