import Mathlib

/-!
# Literature-shaped specification of Carlet's Kasami cyclic-additive count

This file is intentionally independent of the proof development.  It imports
only Mathlib and restates the mathematical objects in a source-shaped form.

In particular, it does **not** use `KasamiCyclicAdditive.kasamiDerivative`,
`derivativeImage`, or `coefficientTripleCount`.  Membership in the derivative
image is expressed existentially, and the triple count ranges over all of
`K × K × K` with explicit membership predicates.  This gives the subsequent
audit bridge a different encoding to compare against the implementation.
-/

namespace KasamiCyclicAdditive.LiteratureSpecification

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The Kasami exponent as written in the literature. -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The normalized derivative value
`(b+1)^d + b^d + 1`, with `d = 4^k - 2^k + 1`. -/
def derivativeValue (k : ℕ) (b : K) : K :=
  (b + 1) ^ kasamiExponent k + b ^ kasamiExponent k + 1

/-- Source-shaped membership in the derivative image: `x` lies in `Δ`
iff it is attained by the normalized derivative at some field element. -/
def InDerivativeImage (k : ℕ) (x : K) : Prop :=
  ∃ b : K, derivativeValue k b = x

/-- A triple is a Carlet solution when all three entries lie in `Δ` and the
coefficient relation vanishes.  The product type is right-associated, so
`p.1`, `p.2.1`, and `p.2.2` are respectively `x`, `y`, and `z`. -/
def IsCoefficientTriple
    (k : ℕ) (v₁ v₂ : K) (p : K × K × K) : Prop :=
  InDerivativeImage k p.1 ∧
  InDerivativeImage k p.2.1 ∧
  InDerivativeImage k p.2.2 ∧
  v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0

/-- The finite set of all literature-shaped coefficient triples.  Unlike the
implementation definition, this ranges over all of `K³` and filters by
explicit existential derivative-image membership. -/
noncomputable def coefficientTriples (k : ℕ) (v₁ v₂ : K) :
    Finset (K × K × K) := by
  classical
  exact Finset.univ.filter (IsCoefficientTriple k v₁ v₂)

/-- The literature-shaped coefficient triple count. -/
noncomputable def coefficientTripleCount (k : ℕ) (v₁ v₂ : K) : ℕ :=
  (coefficientTriples k v₁ v₂).card

/-- The conclusion of Carlet's Kasami cyclic-additive conjecture in the
independent specification. -/
def CarletKasamiConclusion
    (n k : ℕ) (v₁ v₂ : K) : Prop :=
  coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3)

end KasamiCyclicAdditive.LiteratureSpecification
