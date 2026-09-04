import KasamiCyclicAdditive.Main

/-!
# Proved solution

Comparator checks the proved theorem in this Solution environment against its
counterpart in `Challenge.lean`.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Palomar-facing proved declaration. -/
theorem carlet_kasami_cyclic_additive
    [CharP K 2]
    {n k : ℕ} (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n)
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  exact carlet_kasami_cyclic_additive_literature
    hkn hcard hv₁ hv₂ hne

end KasamiCyclicAdditive
