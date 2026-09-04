import KasamiCyclicAdditive.Validation.LiteratureSpecification
import KasamiCyclicAdditive.Validation.LiteratureBridge
import KasamiCyclicAdditive.Validation.BoundaryCases
import KasamiCyclicAdditive.Validation.BoundaryComputations

/-!
Top-level imports for validation and executable checks.

This umbrella is deliberately outside the Comparator-facing `Solution.lean`
import path. For explicit replay commands, including forced re-elaboration of
the `native_decide` boundary computations, see `docs/VALIDATION.md`.
-/
