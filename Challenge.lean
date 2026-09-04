import Mathlib

/-!
# Carlet's Kasami cyclic-additive conjecture

This is the small statement surface intended for Palomar audit.  It uses only
Mathlib and defines exactly the finite-field objects appearing in the
conjecture.

Let `K` be a finite field of characteristic two with `|K| = 2^n`, and let
`k` satisfy `gcd(k,n)=1`.  Put

`d = 4^k - 2^k + 1`

and

`δ(b) = (b+1)^d + b^d + 1`.

Let `Δ` be the image of `δ`.  Carlet's cyclic-additive conjecture for the
Kasami exponent asserts that for every pair of distinct nonzero coefficients
`v₁,v₂`, the number of triples `(x,y,z) ∈ Δ³` satisfying

`v₁ x + v₂ y + (v₁+v₂) z = 0`

is exactly `2^(2n-3)`.

No range hypothesis on `k`, and no separate lower bound on `n`, is imposed
here.  The coefficient hypotheses and `|K| = 2^n` force `n ≥ 2`; coprimality
then makes `k % n` a positive representative below `n`.  The proved solution
formally shows that reducing `k` modulo `n` leaves the derivative image and
coefficient triple count unchanged.
-/

open Finset

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- The Kasami exponent `4^k - 2^k + 1`. -/
def kasamiExponent (k : ℕ) : ℕ := 4 ^ k - 2 ^ k + 1

/-- The normalized derivative of the Kasami monomial in direction `1`:
`δ(b) = (b+1)^d + b^d + 1`. -/
def kasamiDerivative (k : ℕ) (b : K) : K :=
  (b + 1) ^ kasamiExponent k + b ^ kasamiExponent k + 1

/-- The image `Δ` of the normalized Kasami derivative. -/
def derivativeImage (k : ℕ) (K : Type*) [Field K] [Fintype K] [DecidableEq K] : Finset K :=
  Finset.image (kasamiDerivative k) Finset.univ

/-- The number of triples `(x,y,z) ∈ Δ³` satisfying
`v₁ x + v₂ y + (v₁+v₂) z = 0`. -/
def coefficientTripleCount (k : ℕ) (v₁ v₂ : K) : ℕ :=
  (((derivativeImage k K) ×ˢ (derivativeImage k K) ×ˢ (derivativeImage k K)).filter
    (fun p => v₁ * p.1 + v₂ * p.2.1 + (v₁ + v₂) * p.2.2 = 0)).card

/-- **Carlet's Kasami cyclic-additive conjecture.**  For the Kasami exponent
with `gcd(k,n) = 1` over a field of characteristic two with `|K| = 2^n`, every
nondegenerate translation-invariant three-variable coefficient relation has
exactly the random-half-set number `2^(2n-3)` of solutions in `Δ`. -/
theorem carlet_kasami_cyclic_additive
    [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  sorry

end KasamiCyclicAdditive
