import Mathlib
import KasamiCyclicAdditive.Statement.Definitions

/-!
# Executable checks for boundary cases

`Validation/BoundaryCases.lean` contains the mathematical boundary theorems. This file
adds a deliberately computational audit.

There are two levels.

1. On the computable prime field `ZMod 2`, we evaluate the repository's actual
   audited definitions `kasamiExponent`, `kasamiDerivative`, `derivativeImage`,
   and `coefficientTripleCount` directly with `native_decide`.
2. Mathlib's `GaloisField p n` is defined as a splitting field and its field
   structure is noncomputable, so it cannot itself be used as a native
   evaluator. For the extension-field spot checks we therefore use a tiny
   polynomial-basis model of `GF(2^n)`. This model still calls the repository's
   `kasamiExponent`; only the concrete finite-field arithmetic is supplied
   locally. The independent Python implementation in
   `scripts/check_boundary_cases.py` provides a second implementation of the
   same finite computations.

For the theorem cases, expected sizes and counts are written from the formulas
`2^(n-1)` and `2^(2n-3)`, not as precomputed output. For the selected
non-coprime audit case we deliberately use the independently observed values
`7` and `22` as golden references, so drift in either executable model is
detected rather than merely reported.

The model is parameterized by the exponent rather than by `k`, so that the
same code path evaluates both the Kasami exponent and the non-Kasami
exponents used as negative controls.

The computations here are audits, not dependencies of the main theorem.
-/

open Finset

namespace KasamiCyclicAdditive

/-! ## Direct evaluation of the audited definitions -/

/-- Small unit checks of the audited definitions themselves. -/
example : kasamiExponent 2 = 13 := by native_decide
example : kasamiDerivative (K := ZMod 2) 2 0 = 0 := by native_decide
example : kasamiDerivative (K := ZMod 2) 2 1 = 0 := by native_decide
example : (derivativeImage 2 (ZMod 2)).card = 1 := by native_decide
example : coefficientTripleCount (K := ZMod 2) 2 0 1 = 1 := by native_decide

/-- The audited exponent agrees with the closed form `q^2 - q + 1`, `q = 2^k`,
used in the literature. -/
example : ∀ k ∈ Finset.Icc 1 6, kasamiExponent k = (2 ^ k) ^ 2 - 2 ^ k + 1 := by native_decide

/-! ## A computable polynomial-basis model for extension-field checks -/

/-- One step of binary-polynomial multiplication. `modulus` includes its
leading `X^n` term; for `GF(16)` below it is `0b10011 = X^4 + X + 1`. -/
def boundaryGFMulAux (n modulus : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, _, out => out
  | fuel + 1, a, b, out =>
      let out' := if b % 2 = 1 then Nat.xor out a else out
      let shifted := 2 * a
      let a' := if 2 ^ n ≤ shifted then Nat.xor shifted modulus else shifted
      boundaryGFMulAux n modulus fuel a' (b / 2) out'

/-- Multiplication in the polynomial-basis model of `GF(2^n)`. -/
def boundaryGFMul (n modulus a b : ℕ) : ℕ :=
  boundaryGFMulAux n modulus n a b 0

/-- Exponentiation in the polynomial-basis model. -/
def boundaryGFPow (n modulus a : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => boundaryGFMul n modulus (boundaryGFPow n modulus a e) a

/-! ### The model at an arbitrary exponent

Keeping the exponent as a parameter lets the negative controls below run
through exactly the same code as the Kasami cases. -/

/-- The normalized derivative `b ↦ (b+1)^d + b^d + 1` in the executable
model, at an arbitrary exponent `d`. -/
def boundaryGFDerivativeOfExponent (n modulus d b : ℕ) : ℕ :=
  Nat.xor
    (Nat.xor
      (boundaryGFPow n modulus (Nat.xor b 1) d)
      (boundaryGFPow n modulus b d))
    1

/-- Derivative image in the executable model, at an arbitrary exponent. -/
def boundaryGFDerivativeImageOfExponent (n modulus d : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ n)).image (boundaryGFDerivativeOfExponent n modulus d)

/-- Coefficient triple count in the executable model, at an arbitrary
exponent, with the same coefficient pattern as `coefficientTripleCount`.
Addition in the binary polynomial basis is XOR. -/
def boundaryGFCoefficientTripleCountOfExponent (n modulus d v₁ v₂ : ℕ) : ℕ :=
  let Delta := boundaryGFDerivativeImageOfExponent n modulus d
  ((Delta ×ˢ Delta ×ˢ Delta).filter (fun p =>
    Nat.xor
      (Nat.xor
        (boundaryGFMul n modulus v₁ p.1)
        (boundaryGFMul n modulus v₂ p.2.1))
      (boundaryGFMul n modulus (Nat.xor v₁ v₂) p.2.2) = 0)).card

/-! ### The model at the Kasami exponent

The exponent is not duplicated: it is the audited `kasamiExponent` from
`Statement/Definitions.lean`. -/

/-- The normalized Kasami derivative in the executable model. -/
def boundaryGFDerivative (n modulus k b : ℕ) : ℕ :=
  boundaryGFDerivativeOfExponent n modulus (kasamiExponent k) b

/-- Derivative image in the executable model. -/
def boundaryGFDerivativeImage (n modulus k : ℕ) : Finset ℕ :=
  boundaryGFDerivativeImageOfExponent n modulus (kasamiExponent k)

/-- Coefficient triple count in the executable model. -/
def boundaryGFCoefficientTripleCount (n modulus k v₁ v₂ : ℕ) : ℕ :=
  boundaryGFCoefficientTripleCountOfExponent n modulus (kasamiExponent k) v₁ v₂

/-! ### The absolute trace in the model

In the easy-branch instances audited below, `Δ` coincides with the trace
hyperplane.  The trace is also used to record the failure of that identification
in the selected non-easy cases. -/

/-- Accumulator for the absolute trace of the polynomial-basis model. -/
private def boundaryGFTraceAux (n modulus : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _, acc => acc
  | fuel + 1, y, acc =>
      boundaryGFTraceAux n modulus fuel (boundaryGFMul n modulus y y) (Nat.xor acc y)

/-- The absolute trace `x + x^2 + ⋯ + x^(2^(n-1))` in the model. -/
def boundaryGFTrace (n modulus x : ℕ) : ℕ :=
  boundaryGFTraceAux n modulus n x 0

/-- The trace hyperplane `H₀ = {x : Tr(x) = 0}` in the model. -/
def boundaryGFTraceZero (n modulus : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ n)).filter (fun x => boundaryGFTrace n modulus x = 0)

/-- `Δ` is closed under addition, i.e. is an `𝔽₂`-subspace. -/
def boundaryGFImageIsSubspace (n modulus k : ℕ) : Prop :=
  ∀ a ∈ boundaryGFDerivativeImage n modulus k,
    ∀ b ∈ boundaryGFDerivativeImage n modulus k,
      Nat.xor a b ∈ boundaryGFDerivativeImage n modulus k

instance (n modulus k : ℕ) : Decidable (boundaryGFImageIsSubspace n modulus k) := by
  unfold boundaryGFImageIsSubspace; infer_instance

/-- The Kasami power map is APN: every nonzero direction `a` makes
`b ↦ (b+a)^d + b^d` exactly two-to-one, equivalently its image has
`2^(n-1)` elements. -/
def boundaryGFIsAPN (n modulus k : ℕ) : Prop :=
  ∀ a ∈ (Finset.range (2 ^ n)).erase 0,
    ((Finset.range (2 ^ n)).image (fun b =>
      Nat.xor (boundaryGFPow n modulus (Nat.xor b a) (kasamiExponent k))
              (boundaryGFPow n modulus b (kasamiExponent k)))).card = 2 ^ (n - 1)

instance (n modulus k : ℕ) : Decidable (boundaryGFIsAPN n modulus k) := by
  unfold boundaryGFIsAPN; infer_instance

/-! Defining polynomials of the model fields, each including its leading
`X^n` term. -/

private def f4Modulus : ℕ := 0b111
private def f8Modulus : ℕ := 0b1011
private def f16Modulus : ℕ := 0b10011
private def f32Modulus : ℕ := 0b100101
private def f128Modulus : ℕ := 0b10000011

set_option maxRecDepth 10000

/-! ### Positive instances

The right-hand sides below are the theorem's formulas evaluated from `n`, not
precomputed numerical observations. -/

example : (boundaryGFDerivativeImage 2 f4Modulus 1).card = 2 ^ (2 - 1) := by native_decide
example : boundaryGFCoefficientTripleCount 2 f4Modulus 1 1 2 = 2 ^ (2 * 2 - 3) := by
  native_decide

example : (boundaryGFDerivativeImage 3 f8Modulus 1).card = 2 ^ (3 - 1) := by native_decide
example : boundaryGFCoefficientTripleCount 3 f8Modulus 1 1 2 = 2 ^ (2 * 3 - 3) := by
  native_decide
example : boundaryGFCoefficientTripleCount 3 f8Modulus 2 1 2 = 2 ^ (2 * 3 - 3) := by
  native_decide

example : (boundaryGFDerivativeImage 4 f16Modulus 1).card = 2 ^ (4 - 1) := by native_decide
example : boundaryGFCoefficientTripleCount 4 f16Modulus 1 1 2 = 2 ^ (2 * 4 - 3) := by
  native_decide

/-! ### The easy branch `k ≡ ±1 (mod n)`

For the easy-branch parameters checked here, `Δ` is the trace hyperplane,
hence a subspace. Every instance checked above lies in this branch, so on its
own it does not exercise the content of the conjecture. -/

example : boundaryGFDerivativeImage 2 f4Modulus 1 = boundaryGFTraceZero 2 f4Modulus := by
  native_decide
example : boundaryGFDerivativeImage 3 f8Modulus 1 = boundaryGFTraceZero 3 f8Modulus := by
  native_decide
example : boundaryGFDerivativeImage 3 f8Modulus 2 = boundaryGFTraceZero 3 f8Modulus := by
  native_decide
example : boundaryGFDerivativeImage 4 f16Modulus 1 = boundaryGFTraceZero 4 f16Modulus := by
  native_decide
example : boundaryGFDerivativeImage 5 f32Modulus 1 = boundaryGFTraceZero 5 f32Modulus := by
  native_decide

example : boundaryGFImageIsSubspace 5 f32Modulus 1 := by native_decide

/-! ### The genuinely nontrivial branch

`n = 5`, `k = 2` is the smallest admissible pair with `k ≢ ±1 (mod n)`. There
`Δ` is neither the trace hyperplane nor even a subspace, so the count is not
forced by hyperplane geometry, and the conjecture has real content. -/

example : (boundaryGFDerivativeImage 5 f32Modulus 2).card = 2 ^ (5 - 1) := by native_decide

example : boundaryGFDerivativeImage 5 f32Modulus 2 ≠ boundaryGFTraceZero 5 f32Modulus := by
  native_decide

/-- Over `𝔽₃₂` with `k = 2`, the derivative image is not a subspace. -/
theorem boundary_f32_k2_not_subspace : ¬ boundaryGFImageIsSubspace 5 0b100101 2 := by
  native_decide

/-- Yet the coefficient count there is still `2^(2n-3)`. -/
theorem boundary_f32_k2_count :
    boundaryGFCoefficientTripleCount 5 0b100101 2 1 2 = 2 ^ (2 * 5 - 3) := by
  native_decide

/-- The count is constant across coefficients, not merely correct at one pair:
over `𝔽₃₂` with `k = 2`, every admissible pair gives `2^(2n-3)`. -/
theorem boundary_f32_k2_all_pairs :
    ∀ v₁ ∈ (Finset.range (2 ^ 5)).erase 0, ∀ v₂ ∈ (Finset.range (2 ^ 5)).erase 0,
      v₁ ≠ v₂ →
        boundaryGFCoefficientTripleCount 5 0b100101 2 v₁ v₂ = 2 ^ (2 * 5 - 3) := by
  native_decide

example : ¬ boundaryGFImageIsSubspace 5 f32Modulus 3 := by native_decide
example : boundaryGFCoefficientTripleCount 5 f32Modulus 3 1 2 = 2 ^ (2 * 5 - 3) := by
  native_decide

/-! ### Beyond the congruence classes covered by the general Nagy--Vajda proof

`n = 7`, `k = 3` has `k mod n ∉ {1, 2, n-2, n-1}`.  Nagy--Vajda's
general proof covers those four congruence classes; their exhaustive
computation for `n ≤ 13` also covers this finite case. -/

example : (boundaryGFDerivativeImage 7 f128Modulus 3).card = 2 ^ (7 - 1) := by native_decide

/-- Over `𝔽₁₂₈` with `k = 3`, the derivative image is not a subspace either. -/
theorem boundary_f128_k3_not_subspace : ¬ boundaryGFImageIsSubspace 7 0b10000011 3 := by
  native_decide

/-- And the coefficient count there is again `2^(2n-3)`. -/
theorem boundary_f128_k3_count :
    boundaryGFCoefficientTripleCount 7 0b10000011 3 1 2 = 2 ^ (2 * 7 - 3) := by
  native_decide

/-! ### The APN property

The count would be uninteresting for an exponent that failed to be APN; these
checks tie the audited `kasamiExponent` to the property that defines it. -/

example : boundaryGFIsAPN 5 f32Modulus 1 := by native_decide
example : boundaryGFIsAPN 5 f32Modulus 2 := by native_decide
example : boundaryGFIsAPN 5 f32Modulus 3 := by native_decide
example : boundaryGFIsAPN 5 f32Modulus 4 := by native_decide

/-! ### Degenerate coefficient cases

Here the expected value comes from the symbolic boundary theorem: the count
must equal the square of the *computed* derivative-image cardinality. -/

example :
    boundaryGFCoefficientTripleCount 2 f4Modulus 1 1 1
      = (boundaryGFDerivativeImage 2 f4Modulus 1).card ^ 2 := by
  native_decide

example :
    boundaryGFCoefficientTripleCount 2 f4Modulus 1 0 1
      = (boundaryGFDerivativeImage 2 f4Modulus 1).card ^ 2 := by
  native_decide

/-! ### A non-coprime parameter

We deliberately violate `gcd(k,n)=1`. These finite checks use the independently
observed values as golden references: the image has size `7` and the selected
admissible coefficient count is `22`, rather than the coprime-case values `8`
and `32`. -/

example : (boundaryGFDerivativeImage 4 f16Modulus 2).card = 7 := by native_decide

example :
    boundaryGFCoefficientTripleCount 4 f16Modulus 2 1 2 = 22 := by
  native_decide

/-! ### Negative controls: non-Kasami exponents

Replacing the Kasami exponent by a different one usually changes `|Δ|`, so the
half-size condition alone rejects it. The exponents below are the interesting
ones: over `𝔽₁₂₈` they give a derivative image of the correct size `2^(n-1)`
and still fail the count. They witness that the conjecture constrains more
than the cardinality of `Δ`, and that the count as formalized here is
sensitive enough to detect a wrong exponent. -/

example : (boundaryGFDerivativeImageOfExponent 7 f128Modulus 29).card = 2 ^ (7 - 1) := by
  native_decide
example : (boundaryGFDerivativeImageOfExponent 7 f128Modulus 43).card = 2 ^ (7 - 1) := by
  native_decide
example : (boundaryGFDerivativeImageOfExponent 7 f128Modulus 63).card = 2 ^ (7 - 1) := by
  native_decide

example : boundaryGFCoefficientTripleCountOfExponent 7 f128Modulus 29 1 2 ≠ 2 ^ (2 * 7 - 3) := by
  native_decide
example : boundaryGFCoefficientTripleCountOfExponent 7 f128Modulus 43 1 2 ≠ 2 ^ (2 * 7 - 3) := by
  native_decide
example : boundaryGFCoefficientTripleCountOfExponent 7 f128Modulus 63 1 2 ≠ 2 ^ (2 * 7 - 3) := by
  native_decide

/-- None of those three exponents is equivalent to a normalized Kasami
exponent as a power map on `𝔽₁₂₈`: their residues modulo
`2^7 - 1 = 127` are distinct from every `kasamiExponent k`,
`1 ≤ k < 7`. -/
theorem boundary_negative_controls_not_kasami_mod_period :
    ∀ k ∈ Finset.Icc 1 6,
      kasamiExponent k % (2 ^ 7 - 1) ≠ 29 % (2 ^ 7 - 1) ∧
      kasamiExponent k % (2 ^ 7 - 1) ≠ 43 % (2 ^ 7 - 1) ∧
      kasamiExponent k % (2 ^ 7 - 1) ≠ 63 % (2 ^ 7 - 1) := by
  native_decide

end KasamiCyclicAdditive
