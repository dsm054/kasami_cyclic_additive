# Validation runbook

The validation layer is deliberately separate from the Palomar-facing proof
environment. `Solution.lean` imports only `KasamiCyclicAdditive.Main`, so the
Comparator checks the proved theorem without importing executable boundary
audits or their `native_decide` dependencies.

## Boundary validation

The boundary checks have three complementary parts.

- `KasamiCyclicAdditive/Validation/BoundaryCases.lean` contains symbolic Lean
  theorems covering non-vacuity, derived hypotheses, and sharp failure of the
  coefficient conclusion when the coefficient hypotheses are violated.
- `KasamiCyclicAdditive/Validation/BoundaryComputations.lean` contains the
  executable Lean audit. It evaluates the audited definitions on computable
  finite-field models, checks easy and genuinely nontrivial Kasami cases,
  all-pairs and APN instances, the non-coprime control, and non-Kasami negative
  controls. These checks use `native_decide` by design.
- `scripts/check_boundary_cases.py` independently reimplements the finite-field
  arithmetic in Python and repeats the same audit families, with some stronger
  sweeps.

To rerun all three boundary layers from the repository root, use:

```bash
lake env lean KasamiCyclicAdditive/Validation/BoundaryCases.lean
lake env lean KasamiCyclicAdditive/Validation/BoundaryComputations.lean
python3 scripts/check_boundary_cases.py
```

The direct `lake env lean` invocation on `BoundaryComputations.lean` is
intentional: it re-elaborates that source file and therefore reruns its
`native_decide` checks rather than merely importing an already-built `.olean`.

## Statement fidelity

The independent statement check is split between:

- `KasamiCyclicAdditive/Validation/LiteratureSpecification.lean`, a Mathlib-only
  source-shaped restatement of the target; and
- `KasamiCyclicAdditive/Validation/LiteratureBridge.lean`, which proves that the
  source-shaped definitions agree with the implementation definitions.

These can be re-elaborated directly with:

```bash
lake env lean KasamiCyclicAdditive/Validation/LiteratureSpecification.lean
lake env lean KasamiCyclicAdditive/Validation/LiteratureBridge.lean
```

`KasamiCyclicAdditive/Validation.lean` is the umbrella import for all four Lean
validation modules. It is useful for ordinary library builds, but the direct
commands above are the explicit replay commands for the executable audits.

## Full verification

For the complete submission check, use:

```bash
lake exe cache get
lake build
scripts/verify-comparator.sh
lake env lean KasamiCyclicAdditive/Validation/BoundaryCases.lean
lake env lean KasamiCyclicAdditive/Validation/BoundaryComputations.lean
python3 scripts/check_boundary_cases.py
```

Comparator, boundary validation, and the Python oracle serve different roles:
Comparator verifies the Challenge/Solution proof boundary and permitted axioms;
the Lean validation modules test statement fidelity and nearby finite cases;
and the Python script provides an implementation-independent arithmetic check.
