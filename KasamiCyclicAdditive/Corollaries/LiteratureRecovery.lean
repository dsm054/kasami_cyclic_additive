import KasamiCyclicAdditive.Assembly.Reduction
import KasamiCyclicAdditive.MCM.HalfSize

/-!
# Optional literature-recovery results

These theorems recover the coefficient-form conclusion when the
Dillon--Kashyap phase formula is supplied externally. They are kept separate
from the half-size-only theorem used by the final assembly.

This module is terminal: it records how the development recovers the
specialized literature statement, and no other module depends on it.
-/

namespace KasamiCyclicAdditive

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- The coefficient-form conclusion from the Dillon--Kashyap phase formula at
both possible normalized parameters.  The half-size cardinality is *not* assumed:
it is discharged from `kasami_half_size` (`MCM/HalfSize.lean`), so the phase formula is
the only result imported from the literature. -/
theorem kasami_conjecture_of_phase_formula {n k : ℕ}
    (hklt : k < n) (hkn : Nat.Coprime k n)
    (hn : 2 ≤ n) (hcard : Fintype.card K = 2 ^ n)
    (hphase : DillonKashyapPhaseFormula k (primitiveAddChar K) ∧
      DillonKashyapPhaseFormula (n - k) (primitiveAddChar K))
    {v₁ v₂ : K} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) (hne : v₁ ≠ v₂) :
    coefficientTripleCount k v₁ v₂ = 2 ^ (2 * n - 3) := by
  have hkpos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · rw [hk0, Nat.coprime_zero_left] at hkn
      omega
    · exact hk
  have hk_le : k ≤ n := hklt.le
  have hhalf : 2 * (derivativeImage k K).card = Fintype.card K ∧
      2 * (derivativeImage (n - k) K).card = Fintype.card K :=
    ⟨kasami_half_size hkpos hklt hkn hcard,
     kasami_half_size (by omega) (by omega)
       ((Nat.coprime_self_sub_left hk_le).mpr hkn) hcard⟩
  have hK2 : 2 < Fintype.card K := by
    rw [hcard]
    calc
      2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  obtain ⟨k0, m, hk0, hodd, hcop0, he, hcop⟩ := exists_normalized_parameter hklt hkn
  rcases hk0 with hk0 | hk0
  · rw [hk0] at hodd hcop0 he
    have hslope := normalized_slope_of_phase_count_average hn hcard hcop0 he hcop hphase.1
      (walshTripleCountFormula_of_half_size hhalf.1)
      (slopeAverageFormula_of_half_size hhalf.1 hK2)
    exact coefficient_form_of_normalized_witness hn hcard hslope hv₁ hv₂ hne rfl
  · rw [hk0] at hodd hcop0 he
    have hk_le : k ≤ n := Nat.le_of_lt hklt
    obtain ⟨w1, w2, hw1, hw2, hwne, hcount⟩ :=
      coefficientCount_transfer_complement hk_le hcard hv₁ hv₂ hne
    have hslope := normalized_slope_of_phase_count_average hn hcard hcop0 he hcop hphase.2
      (walshTripleCountFormula_of_half_size hhalf.2)
      (slopeAverageFormula_of_half_size hhalf.2 hK2)
    exact coefficient_form_of_normalized_witness hn hcard hslope hw1 hw2 hwne hcount

end KasamiCyclicAdditive
