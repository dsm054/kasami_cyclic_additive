# Carlet's Kasami cyclic-additive conjecture

A self-contained Lean 4 proof of Carlet's Kasami cyclic-additive conjecture.

Let `K` be a finite field of characteristic two with `|K| = 2^n`, let `k`
satisfy `gcd(k,n) = 1`, and put `d_k = 4^k - 2^k + 1`, the Kasami exponent.
Carlet's *cyclic-additive* condition asks that the image `Δ` of the normalized
Kasami derivative `b ↦ (b+1)^{d_k} + b^{d_k} + 1` meets every "slope" of `K`
equally often: for distinct nonzero coefficients the number of additive
relations `v₁x + v₂y + (v₁+v₂)z = 0` with `x,y,z ∈ Δ` should be exactly
`|K|²/8`, independent of the coefficients. The condition is the componentwise
counterpart of APNness for the Kasami power functions, and it is equivalent to
`Δ` being a cyclic-additive difference set with Singer-like parameters.

Carlet stated the conjecture in 2018. Nagy and Vajda (2026) recently proved
the cases `k mod n ∈ {1, 2, n−2, n−1}` and verified `n ≤ 13` exhaustively.
This repository proves the full conjecture for every admissible `(n, k)`.

## Result

For every finite field `K` of characteristic two with `|K| = 2^n`, every `k`
with `gcd(k,n) = 1`, and all distinct nonzero `v₁, v₂ ∈ K`,

```text
#{(x,y,z) ∈ Δ^3 : v₁*x + v₂*y + (v₁+v₂)*z = 0} = 2^(2*n-3),
```

where `Δ` is the image of `b ↦ (b+1)^{d_k} + b^{d_k} + 1` on `K`.

## Proof

Two large parts joined by the half-size identity `2*|Δ| = |K|`, which is proved
from the Artin--Schreier description of the derivative image together with the
Müller--Cohen--Matthews permutation theorem. The half-size identity is then used
twice: to rederive the Dillon--Kashyap multiplicative phase formula, and to
obtain an exact average of the relevant slope triple counts. Fourier inversion
turns the phase correction into twisted root counts, which are interpreted as
incidences on the Fermat cubic `W³ + T³ = 1`. Root existence is proved by a
rational-kernel bijectivity argument in odd extension degree, and in even degree
by factoring `1 + π^k` into a prime-to-three part and the degree-three quotient
`1 + π` and lifting through explicit Hessian quotient coordinates. The geometry
gives a pointwise lower bound, the double count gives the exact average, and the
two together force equality for every slope.

## Formalization

The Palomar-facing declaration is

```lean
KasamiCyclicAdditive.carlet_kasami_cyclic_additive
```

in `Solution.lean`, matching the statement in `Challenge.lean`. The four
statement-critical definitions `kasamiExponent`, `kasamiDerivative`,
`derivativeImage`, and `coefficientTripleCount` are kept concrete and directly
auditable in `Challenge.lean`; Comparator is used for the headline theorem
itself. The Palomar statement assumes neither `2 ≤ n` nor `1 ≤ k`: `2 ≤ n`
follows from `|K| = 2^n` and the existence of two distinct nonzero
coefficients, and coprimality then forces `k % n` into `1, …, n-1`.

Inside the library, `KasamiCyclicAdditive/Main.lean` proves the unnormalized
literature statement `carlet_kasami_cyclic_additive_literature`, reducing `k` to
`k % n` via the periodicity results in
`KasamiCyclicAdditive/Statement/ParameterReduction.lean`;
`carlet_kasami_cyclic_additive_core` is the normalized `1 ≤ k < n` proof core.

Statement fidelity is checked separately from the proof:
`Validation/LiteratureSpecification.lean` restates the target from Mathlib only,
and `Validation/LiteratureBridge.lean` proves it equivalent to the implementation
definitions. `Validation/BoundaryCases.lean` and
`Validation/BoundaryComputations.lean` add symbolic sharpness proofs and
executable checks, and `scripts/check_boundary_cases.py` repeats the same audit
families in independent Python arithmetic. These validation modules are
intentionally outside the Comparator-facing `Solution.lean` import path.

## Documentation

- Mathematical proof walkthrough and validation architecture: [`docs/BLUEPRINT.md`](docs/BLUEPRINT.md)
- Boundary-validation layers and exact run commands: [`docs/VALIDATION.md`](docs/VALIDATION.md)
- Sources and proof ancestry: [`docs/PROVENANCE.md`](docs/PROVENANCE.md)
- Structured Palomar metadata: [`formalization.yaml`](formalization.yaml)

## Verification

The project targets

```text
Lean 4.28.0
Mathlib v4.28.0 (8f9d9cff6bd728b17a24e163c9402775d9e6a365)
```

Build the project and run Comparator with

```bash
lake exe cache get
lake build
scripts/verify-comparator.sh
```

The boundary-validation layer is intentionally separate from `Solution.lean`.
To re-run the symbolic boundary checks, the executable Lean audit (including
its `native_decide` computations), and the independent Python oracle, run

```bash
lake env lean KasamiCyclicAdditive/Validation/BoundaryCases.lean
lake env lean KasamiCyclicAdditive/Validation/BoundaryComputations.lean
python3 scripts/check_boundary_cases.py
```

The direct `lake env lean` command on `BoundaryComputations.lean` re-elaborates
the source file, so its executable checks are actually rerun rather than merely
loaded from an existing `.olean`.

The development is `sorry`-free apart from the deliberate statement placeholder
in `Challenge.lean`. `#print axioms` on the headline theorem reports only
`propext`, `Classical.choice`, and `Quot.sound`.
