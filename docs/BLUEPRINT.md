# Blueprint: Carlet's Kasami cyclic-additive conjecture

This document gives a human-readable map of the proof formalized in this
repository. It focuses on the mathematical structure of the final argument;
`PROVENANCE.md` records the sources and ancestry of the ingredients in more
detail.

The proof combines Kasami/MCM permutation theory, Dickson-polynomial
identities, multiplicative character sums and the Dillon--Kashyap phase
formula, Fourier/root-count conversion, the Fermat cubic, and degree-three
Hessian isogeny geometry. Nagy--Vajda provide the immediate antecedent for the
monomial/root-count reductions and the pointwise-lower-bound plus exact-average
strategy; their Remark 11.13 gives the Fermat-cubic reinterpretation that the
formalization promotes to the organizing geometric mechanism for general
admissible `k`.

## 1. The theorem

Let

$$
d_k=4^k-2^k+1
$$

and let `K` be a finite field of characteristic two with

$$
|K|=2^n,\qquad \gcd(k,n)=1.
$$

No range hypothesis on `k` and no lower bound on `n` are assumed. The
coefficient hypotheses below force $n\ge 2$, and the derivative image and
coefficient count are periodic in `k` with period `n`, so `k` may be replaced
by $k\bmod n$, which coprimality puts in $\{1,\dots,n-1\}$. That periodicity
is proved in `Statement/ParameterReduction.lean`; the normalized range
$1\le k<n$ used from section 3 onwards is therefore a derived convenience, not
a hypothesis.

The normalized Kasami derivative image is

$$
\Delta_k
 = \{(b+1)^{d_k}+b^{d_k}+1:b\in K\}.
$$

For distinct nonzero coefficients $v_1,v_2\in K$, define

$$
N_k(v_1,v_2) = \left|\{(x,y,z)\in\Delta_k^3: v_1x+v_2y+(v_1+v_2)z=0\}\right|.
$$

The theorem is

$$
\boxed{N_k(v_1,v_2)=2^{2n-3}.}
$$

The Palomar-facing declaration is

```lean
KasamiCyclicAdditive.carlet_kasami_cyclic_additive
```

in `Solution.lean`. It assumes exactly the Challenge hypotheses: `gcd(k,n)=1`,
`|K| = 2^n`, and the coefficient conditions. Inside the library,
`KasamiCyclicAdditive/Main.lean` provides two theorems:

```lean
KasamiCyclicAdditive.carlet_kasami_cyclic_additive_literature
KasamiCyclicAdditive.carlet_kasami_cyclic_additive_core
```

`core` is the normalized proof core and carries the extra hypotheses
`1 ≤ k` and `k < n`. `literature` removes those normalization assumptions and
is what matches the Challenge surface: it derives `2 ≤ n` from the coefficient
hypotheses, rewrites the count at `k` as the count at `k % n`, and applies
`core`. `Solution.lean` proves the Palomar theorem by applying `literature`.

At the highest level, the formal proof has the shape

```text
arbitrary Challenge parameter k
        |
        | derive n >= 2; replace k by r = k % n
        v
normalized core parameter r, 1 <= r < n
        |
        v
half-size of Delta_r
        |
        v
normalize_with_count_transport
        |   choose k0 in {r,n-r}, transport coefficients and half-size
        v
half-size of Delta_k0
        |
        +-------------------------------+
        |                               |
        v                               v
phase / positivity branch          exact double count
        |                               |
        v                               v
cube-support split                 exact slope average
  noncube -> correction = 0
  cube/cube -> root counts
               -> Fermat-cubic geometry
               -> correction >= 0
        |
        v
pointwise lower bound
        \                               /
         +-----------------------------+
                        |
                        v
              normalized equality
                        |
                        v
          coefficient transport back to r
                        |
                        v
        carlet_kasami_cyclic_additive_core
                        |
                        v
      carlet_kasami_cyclic_additive_literature
                        |
                        v
        carlet_kasami_cyclic_additive
             (Solution.lean / Challenge.lean)
```

The substantive work after half-size is therefore genuinely two-branched:
phase positivity gives a pointwise lower bound, using geometry only in the
cube/cube case, while an independent double count gives the exact average.

## 2. The proof in one page

### Layer A: the derivative image has half the field

For every `k` the Kasami derivative admits the Müller--Cohen--Matthews
parametrization $\delta(b)=M_k(b^2+b)$, so

$$
\Delta_k=M_k(\mathrm{AS}(K)),
$$

where

$$
\mathrm{AS}(K)=\{b^2+b:b\in K\}.
$$

The Artin--Schreier image has exactly $|K|/2$ elements. For odd normalized
`k` the MCM/Dickson part of the development proves that $M_k$ is a permutation,
so its image of `AS(K)` also has size $|K|/2$. If the normalized parameter `k`
is even, coprimality forces `n-k` to be odd and Frobenius/complement transport
transfers the same cardinality back to `k`.

Thus

$$
2|\Delta_k|=|K|.
$$

This is `kasami_half_size` in `MCM/HalfSize.lean`.

### Layer B: every admissible slope has at least the target count

The coefficient problem is reduced by Frobenius transport to a normalized odd
parameter, again denoted `k`, for which

$$
2^k+1=3m,
\qquad
\gcd(m,2^n-1)=1.
$$

For a slope $\rho$, Fourier inversion expresses the relevant triple count as

$$
\frac{|K|^2}{8} + \frac{1}{|K|}\mathrm{Re}(\text{phase triple sum}).
$$

The multiplicative phase is derived from the half-size equation using the
MCM/Dickson identities. The correction term is then bounded below by zero in
two disjoint cases, which is how `phaseTripleSum_re_nonneg` in
`Assembly/GeometricChain.lean` is actually organized.

If either $\rho$ or $1+\rho$ fails to be a cube, the phase support collapses:
the character factor vanishes and `phaseTripleSum_eq_zero_of_not_cube` makes
the correction exactly zero. Only in the remaining case

$$
\rho=A^3,\qquad 1+\rho=B^3
$$

does the phase-to-root-count conversion apply, rewriting the correction term as
a sum of twisted root counts; it is then enough that the corresponding
algebraic equation has a root. For odd `n` every element is a cube, so only
this second branch occurs there.

That root-existence problem becomes an incidence problem on the Fermat cubic

$$
E: W^3+T^3=1.
$$

Nagy--Vajda's actual `k=2` proof proceeds through the corresponding root
equation; their Remark 11.13 then reinterprets it on the Fermat cubic. The
formalization takes that reinterpretation as the geometric interface and
extends it to all normalized admissible parameters.

For odd `n`, a rational-kernel argument makes the relevant map on `E(K)`
injective and hence bijective. For even `n`, the proof factors the obstruction
into a prime-to-three factor and the degree-three map `1+π`, inverts the first
factor over `K`, and handles only the residual degree-three quotient over the
algebraic closure. Explicit Hessian quotient coordinates then recover the
required root over `K` at the level of the invariant cubes `W^3,T^3`.

Consequently

$$
N(\rho)\ge \frac{|K|^2}{8}
$$

for every admissible slope.

### Layer C: the exact average forces equality

Independently of the geometric branch, the half-size equation yields the exact
double-counting identity

$$
\frac{1}{|\mathcal S|}\sum_{\rho\in\mathcal S}N(\rho)
 =\frac{|K|^2}{8},
$$

where $\mathcal S$ is the set of admissible slopes.

Every summand is at least the average, and the average is exactly that lower
bound. Therefore

$$
N(\rho)=\frac{|K|^2}{8}
\quad\text{for every admissible }\rho.
$$

Coefficient transport first returns this equality from the auxiliary odd
parameter to the normalized core parameter. The outer periodicity theorem in
`Main.lean` then returns from `k % n` to the arbitrary Challenge parameter,
giving

$$
N_k(v_1,v_2)=2^{2n-3}.
$$

The final forcing mechanism is therefore

```text
local geometric existence + global conservation = pointwise equality.
```

This same local-to-global pattern is central in Nagy--Vajda's treatment of the
special cases they resolve.

## 3. Half-size: Artin--Schreier and MCM

The derivative image is identified with the image of the Artin--Schreier
half-space under an MCM polynomial:

```text
AS(K) = {b^2+b : b in K}
Delta_k = mcmMap k '' AS(K).
```

The relevant modules are:

- `MCM/Halfspace.lean` — Artin--Schreier/MCM parametrization;
- `MCM/FrobeniusSum.lean` — shared elementary Frobenius-sum infrastructure;
- `MCM/DicksonPermutation.lean` — Dickson-polynomial arithmetic;
- `MCM/Fourier.lean` — Fourier/Dickson character-sum reduction;
- `MCM/Permutation.lean` — the MCM permutation theorem;
- `MCM/HalfSize.lean` — half-size of `derivativeImage`;
- `MCM/ComplementTransport.lean` — transport between `k` and `n-k`.

The shared Frobenius-sum packet has the following dependency hierarchy. The
nonvanishing proof uses the arithmetic lemmas `pow_two_pow_gcd` and
`pow_card_two_pow`, both from `Preliminaries/Arithmetic.lean`:

```text
frobSum_succ
      |
      v
frobSum_sq_add_self
      |
      |  if frobSum k s = 0
      v
s^(2^k) = s -----------\
                         \
pow_card_two_pow --------> pow_two_pow_gcd
                           |
                           v
                 s^(2^gcd(k,n)) = s
                           |
                    gcd(k,n) = 1
                           |
                           v
                        s^2 = s
                           |
                    s ≠ 0 => s = 1
                           |
frobSum_one --------------+
                           |
                           v
                     contradiction
```

`FrobeniusSum.lean` provides the definition and elementary lemmas used by
Halfspace, Fourier, and Permutation. Since Halfspace imports FrobeniusSum, and
Fourier imports Halfspace, the principal module graph is:

```text
FrobeniusSum ──> Halfspace ──> Fourier ──> Permutation
      └────────────────────────────────> Permutation
```

This separates the elementary MCM zero-freeness interface from the analytic
Fourier machinery.

For odd `k`, `mcmMap_bijective_of_odd` gives global
bijectivity. Since the Artin--Schreier map has kernel of size two,

$$
|\mathrm{AS}(K)|=|K|/2,
$$

and hence

$$
|\Delta_k|=|K|/2.
$$

For even `k`, coprimality implies that `n` is odd and therefore `n-k` is odd.
The complementary parameter has the same derivative-image cardinality, so the
odd result implies the general theorem

```lean
kasami_half_size
```

with conclusion

```lean
2 * (derivativeImage k K).card = Fintype.card K.
```

This half-size equation is the only Kasami-specific input used by the upper
reduction layer.

## 4. Normalization and the slope problem

There are two separate parameter reductions. The **outer reduction**, in
`Statement/ParameterReduction.lean` and `Main.lean`, replaces the arbitrary
Challenge parameter `k` by `k % n` before entering the normalized core. Inside
that core, the **arithmetic/coefficient normalization** described here chooses
an auxiliary parameter in the complementary pair.

`Assembly/Normalization.lean`, `Statement/CoefficientForm.lean`, and
`Assembly/CoefficientReduction.lean` transport the problem to an odd parameter
`k₀ ∈ {k, n-k}` satisfying

$$
2^{k_0}+1=3m,
\qquad
\gcd(m,2^n-1)=1.
$$

The coefficient equation is simultaneously normalized to a slope parameter,
so the problem becomes proving a common value for
`slopeTripleCount k₀ ρ` over the admissible slopes.

Passing to the complement is not only needed when `k` is even. The choice
`exists_normalized_parameter` must also avoid the exceptional residue
`k₀ ≡ 3 (mod 6)` when `n` is even, since that class breaks
$\gcd(m,2^n-1)=1$; so an already-odd `k` can still be replaced by `n-k`.

The two arithmetic facts above are used separately: the factorization by `3`
exposes the cubic structure in the root equation, while
$\gcd(m,2^n-1)=1$ makes the `m`-th power map invertible on `Kˣ`.

## 5. The Dillon--Kashyap phase formula

The proposition `DillonKashyapPhaseFormula` records the natural interface
between the multiplicative-character theory and the later Fourier argument.
The formalization proves the required identity internally from the half-size
statement and the MCM/Dickson machinery.

The transform is taken over the unit group `Kˣ`. For a multiplicative
character $\chi$, let $F:K^\times\to\{\pm 1\}$ be the sign of membership in
$\Delta_k$,

$$
F(x)=
\begin{cases}
  1,&x\in\Delta_k,\\
 -1,&x\notin\Delta_k.
\end{cases}
$$

The resulting multiplicative transform has the Dillon--Kashyap form

$$
\widehat F(\chi)
 = \frac{G(\chi)G(\chi^{2^k+1})}{G(\chi^3)},
$$

with the principal and cubic exceptional characters treated separately.
The endpoint is

```lean
phase_formula_from_half_size
```

in `MCM/PhaseFormula.lean`.

`Corollaries/LiteratureRecovery.lean` records the same downstream proof with
the published Dillon--Kashyap formula supplied directly; this makes the
connection between the internal derivation and the classical statement
explicit.

## 6. From phase to twisted root counts

`Assembly/GeometricChain.lean` derives the Walsh-character interface from the
phase formula, and `Phase/RootCount.lean` converts the phase triple sum into
algebraic root counts. Schematically,

$$
N(\rho) = \frac{|K|^2}{8} + \frac{1}{|K|}\mathrm{Re} C(\rho).
$$

After expansion of the Gauss sums and character orthogonality, `C(ρ)` becomes
a combination of counts of solutions to twisted equations. The relation

$$
2^k+1=3m
$$

turns the relevant monomials into cubes followed by `m`-th powers.

Nagy--Vajda's monomial reduction gives the close special-case antecedent: in
their `k=2` analysis the same passage from character sums to constrained root
counts is explicit. Their subsequent Remark 11.13 supplies the Fermat-cubic
reinterpretation. The formalization packages the general root-existence
requirement as

```lean
RootEqSolvable m K
```

in `Geometry/RootEquation.lean`.

The key point is qualitative. Geometry need only produce at least one root in
each twisted fibre; the exact fibre size is forced later by the global
average.

## 7. The Fermat cubic

The root equation is interpreted on

$$
E: W^3+T^3=1.
$$

Nagy--Vajda's Remark 11.13 gives this Fermat-cubic interpretation for their
`k=2` root equation. The formal development promotes that reinterpretation to
the organizing geometric mechanism and establishes the required root
existence for every normalized admissible parameter.

Let $\pi$ denote the characteristic-two Frobenius endomorphism. For a target
point $P$, the geometric problem is organized around

$$
\Phi_k(Q)=-(Q+\pi^kQ)+T_3,
$$

where `T₃` is a distinguished three-torsion point. If a suitable preimage
`Q=(W,T)` exists, the Hessian addition identities imply the twisted root
equation required by the phase argument.

The proof splits according to the parity of `n`.

## 8. Odd dimension: rational-kernel bijectivity

When `n` is odd, the relevant rational kernel is trivial. Hence

$$
Q\longmapsto -(Q+\pi^kQ)+T_3
$$

is injective on the finite group `E(K)` and therefore bijective.

Given a target `P`, choose its unique preimage `Q`. Three-torsion arguments
exclude the origin and the points at infinity, so `Q` is affine with nonzero
coordinates. The Fermat-cubic incidence identity then supplies the required
root.

The branch is assembled from the Fermat-cubic arithmetic,
`Geometry/FermatCubic/RationalKernel.lean`, and the incidence lemmas in
`Assembly/GeometricChain.lean`.

## 9. Even dimension: the quotient-first bridge

For even `n`, factor in the commutative subring generated by Frobenius:

$$
1+\pi^k=(1+\pi)G.
$$

The factor `1+π` has degree/norm three, while

$$
N(G)=m=\frac{2^k+1}{3}.
$$

The proof in `Geometry/EvenCase.lean` proceeds in five steps.

### 9.1 Invert the prime-to-three factor over `K`

For the target `P`, put

$$
R=T_3-P.
$$

`PointFrobenius.exists_gMap_preimage` (namespace `PointFrobenius`, declared in
`Geometry/FrobeniusAnnihilator.lean`) produces

$$
Y\in E(K),\qquad G(Y)=R.
$$

It obtains `Y` from `Isogeny.gMap_bijective`, which needs only the Frobenius
relation `π² = -2`, the norm identity `a² + 2b² = m`, the annihilator and
coprimality — not the coefficient identities.

### 9.2 Lift only through the degree-three quotient

Write `Y=(x,y)`. Three-torsion considerations give `x,y ≠ 0`. After base
change to $F=\overline K$, choose

$$
W^3=\frac{x+1}{x+y}.
$$

`FermatCubic.explicit_quotient_coordinates` constructs `T` so that

$$
Q=(W,T),\qquad Q+\pi Q=Y.
$$

These are explicit coordinates for the degree-three Hessian quotient.

### 9.3 Reassemble the factorization

Because `G` and `1+π` are polynomials in `π`, they commute. Naturality under
base change gives

$$
(1+\pi)G(Q)=G((1+\pi)Q)=G(Y)=T_3-P.
$$

Using the factorization `(1+π)G=1+π^k` of `Isogeny.gMap_factor`, one obtains

$$
(1+\pi^k)Q=T_3-P,
$$

which is the required Fermat-cubic incidence relation.

### 9.4 Control the Frobenius defect

Although `Q` need not be `K`-rational, `Q+πQ=Y` is. Therefore

$$
\pi^n(Q+\pi Q)=Q+\pi Q,
$$

and hence

$$
(1+\pi)(\pi^nQ-Q)=0.
$$

Thus

$$
\pi^nQ-Q\in\ker(1+\pi).
$$

`EvenAssembly.frobFixed_eq_ptInf` identifies this kernel with the three points
at infinity, yielding

$$
\pi^nQ=Q+\mathrm{ptInf}(\alpha),
\qquad \alpha^3=1.
$$

### 9.5 Descend the invariant cubes

The proof does not require `W` or `T` themselves to lie in `K`. The quotient
coordinates give

$$
W^3,\;T^3
$$

as rational functions of the original `K`-rational coordinates `x,y`.
Therefore the data needed by the root equation already descend to `K`.

The even branch can be summarized as

```text
invert G over K
   -> lift only through 1+pi over Kbar
   -> Frobenius defect lies in ker(1+pi)
   -> classify the three-point kernel
   -> descend W^3,T^3.
```

## 10. Geometry gives existence; averaging gives rigidity

The noncube-support collapse and the parity-dependent `RootEqSolvable` theorem
together give

$$
N(\rho)\ge |K|^2/8
$$

for every admissible slope: noncube slopes have zero correction outright,
while cube/cube slopes use the odd- or even-dimensional Fermat-cubic branch.

Independently, `Counting/Average.lean` gives

$$
\frac{1}{|\mathcal S|}
\sum_{\rho\in\mathcal S}N(\rho)
=|K|^2/8.
$$

Both this average and the additive-character triple-count identity
(`walshTripleCountFormula_of_half_size`) are proved in `Counting/Average.lean`
for an arbitrary `Delta : Finset K`; the namespace
`KasamiCyclicAdditive.CountAverage` carries its own `slopeTripleCount Delta rho`
and `walshCoefficient` for that generic layer, which is then specialized to
`derivativeImage k K`. The unqualified `slopeTripleCount k rho` used in
section 4 is the specialized one in `Counting/Definitions.lean`. This
additive-character identity should not be confused with `WalshCharacterFormula`
in `Phase/Definitions.lean`, which is a multiplicative-character object
constructed later from the phase formula.

This is the same local-lower-bound/global-average mechanism used by
Nagy--Vajda. `Preliminaries/FiniteAverage.lean` packages the elementary
conclusion that all terms must equal the average. Therefore

$$
N(\rho)=|K|^2/8
$$

for every admissible slope.

The elliptic curve supplies existence, not uniqueness. Exactness comes from
the conserved average.

## 11. Returning to the normalized coefficient statement

`Assembly/Reduction.lean` packages the upper proof in the same order as the
Lean theorem chain:

```text
half-size at normalized core parameter k
        |
        v
normalize_with_count_transport
        |
        +--> choose odd k0 in {k,n-k}
        +--> arithmetic data m and gcd(m,2^n-1)=1
        +--> transported coefficients w1,w2
        +--> transported half-size at k0
                         |
                         +-------------------------------+
                         |               |               |
                         v               v               v
                    phase formula   count identity   exact average
                         |
                         v
                WalshCharacterFormula
                         |
                         v
                phaseTripleSum_re_nonneg
                   /                 \
              noncube              cube/cube
                 |                    |
           correction = 0             v
                                  RootEqSolvable
                                  /          \
                               odd n        even n
                                  \          /
                                   correction >= 0
                                           |
                         +-----------------+-----------------+
                         |                                   |
                         v                                   v
                  pointwise lower bound                exact average
                         \                                   /
                          +---------------+------------------+
                                          |
                                          v
                                  exact slope counts
                                          |
                                          v
                               coefficient form at k0
                                          |
                                          v
                           coefficient transport back to k
```

The theorem

```lean
kasami_conjecture_of_half_size
```

states that, under the normalized range, coprimality, and field-cardinality
hypotheses, the derivative-image half-size equation is the only additional
Kasami-specific input needed for the cyclic-additive coefficient count. This
returns from the odd `k₀` slope problem to the coefficient statement at the
normalized core parameter `k`, still under `1 ≤ k < n`. `Main.lean` supplies
the half-size hypothesis using `kasami_half_size`, giving
`carlet_kasami_cyclic_additive_core`; the return to the arbitrary Challenge
parameter happens only afterwards, via `Statement/ParameterReduction.lean`, in
`carlet_kasami_cyclic_additive_literature`.

## 12. Reading guide: mathematics to Lean modules

| Mathematical role | Main Lean modules |
|---|---|
| Statement and derivative image | `Statement/Definitions.lean`, `Counting/Definitions.lean` |
| Periodicity in `k` and reduction to `k % n` | `Statement/ParameterReduction.lean` |
| Shared finite-field Frobenius and `2^k` arithmetic | `Preliminaries/Arithmetic.lean` |
| Shared partial Frobenius-sum packet | `MCM/FrobeniusSum.lean` |
| Artin--Schreier/MCM parametrization | `MCM/Halfspace.lean` |
| MCM/Dickson permutation theorem | `MCM/DicksonPermutation.lean`, `MCM/Fourier.lean`, `MCM/FrobeniusSum.lean`, `MCM/Permutation.lean` |
| Half-size of the derivative image | `MCM/HalfSize.lean`, `MCM/ComplementTransport.lean` |
| Parameter/coefficient normalization | `Assembly/Normalization.lean`, `Statement/CoefficientForm.lean`, `Assembly/CoefficientReduction.lean` |
| Exact slope average | `Counting/Average.lean`, `Preliminaries/FiniteAverage.lean` |
| Character and Gauss-sum infrastructure | `Phase/CharacterSums.lean` (shared orthogonality and Gauss identities), `Phase/AdditiveCharacter.lean`, `MCM/CharacterArithmetic.lean`, `MCM/Fourier.lean` |
| Elementary inputs and bijectivity criteria | `Assembly/ElementaryInputs.lean`, `Preliminaries/FiniteCharacterCriterion.lean`, `Phase/PowerMap.lean` |
| Phase formula | `MCM/DicksonPhase.lean`, `MCM/PhaseFormula.lean` |
| Phase-to-root-count conversion | `Phase/Definitions.lean`, `Phase/RootCount.lean`, `Assembly/GeometricChain.lean` |
| Fermat cubic geometry | `Geometry/FermatCubic/*`, `Geometry/FermatCubic/RationalKernel.lean` |
| Frobenius and isogeny arithmetic | `Geometry/PointFrobenius.lean`, `Geometry/IsogenyFactor.lean`, `Geometry/FrobeniusAnnihilator.lean` |
| Odd root-existence branch | `Assembly/GeometricChain.lean` plus rational-kernel modules |
| Even root-existence branch | `Geometry/EvenCase.lean`, `Geometry/BaseChange.lean`, `Geometry/FermatCubic/Quotient.lean` |
| Final reduction | `Assembly/Reduction.lean`, `Main.lean` |
| Literature phase interface | `Phase/DillonKashyapInterface.lean`, `Corollaries/LiteratureRecovery.lean` |
| Boundary cases and executable checks | `Validation/BoundaryCases.lean`, `Validation/BoundaryComputations.lean` |
| Palomar statement/proof boundary | `Challenge.lean`, `Solution.lean` |

## 13. Validation architecture

The repository separates statement fidelity from boundary testing.

1. `KasamiCyclicAdditive/Validation/LiteratureSpecification.lean` is the normative
   source-shaped specification.  It imports only Mathlib, restates the Kasami
   exponent and derivative independently, expresses membership in `Δ`
   existentially, and counts solutions by filtering all of `K³`.  It does not
   use the implementation definitions `derivativeImage` or
   `coefficientTripleCount`.
2. `KasamiCyclicAdditive/Validation/LiteratureBridge.lean` is the semantic
   bridge.  It proves that existential derivative-image membership agrees with
   the implementation `Finset.image`, that the two differently constructed
   solution sets coincide, and hence that the two triple counts are equal.
3. `KasamiCyclicAdditive/Validation/BoundaryCases.lean` proves symbolic boundary facts:
   non-vacuity, derived hypotheses, and sharp failure when coefficient
   hypotheses are violated.
4. `KasamiCyclicAdditive/Validation/BoundaryComputations.lean` supplies executable Lean
   spot checks, including nonlinear/non-subspace cases, all-pairs sweeps, APN
   checks, and wrong-exponent controls.
5. `scripts/check_boundary_cases.py` independently reimplements the finite
   arithmetic and repeats the same audit families outside Lean.

The boundary computations are deliberately supporting evidence rather than the
definition of the target; the literature specification is the semantic
reference point.

### Boundary cases and exact checks

The formal development also records what the theorem does **not** say.
`KasamiCyclicAdditive/Validation/BoundaryCases.lean` records non-vacuity witnesses over
`𝔽₄`, `𝔽₈`, and `𝔽₁₆`.  In the checked easy-branch cases with
`k ≡ ±1 (mod n)`, the executable audit finds `Δ` equal to the trace hyperplane,
so the count is forced by hyperplane geometry.  Two further witnesses lie
outside that easy branch: `𝔽₃₂` with
`k = 2`, the smallest instance where `Δ` is not a subspace, and `𝔽₁₂₈` with
`k = 3`, outside the four congruence classes covered by the general
Nagy--Vajda proof (though included in their exhaustive `n ≤ 13` computation).
These are named `carlet_f32_k2_instance` and `carlet_f128_k3_instance`. It also proves
symbolically that the coefficient restrictions are sharp: if `v₁ = v₂ ≠ 0`, or
if exactly one of the two coefficients is zero, the linear equation degenerates
and the count is

```text
|Δ|^2.
```

For every admissible `(n,k)`, the half-size theorem gives
`|Δ|^2 = 2^(2n-2)`, a factor-two miss from the Carlet value
`2^(2n-3)`. Over `𝔽₄` this specializes to the concrete failure `4 ≠ 2`.

### The two computational audits

`KasamiCyclicAdditive/Validation/BoundaryComputations.lean` executes the repository's
actual audited definitions directly wherever the underlying field model is
computable. In particular it evaluates `kasamiExponent`, `kasamiDerivative`,
`derivativeImage`, and `coefficientTripleCount` on `ZMod 2` with
`native_decide`. Mathlib's `GaloisField p n` is a noncomputable splitting-field
construction, so extension-field native evaluation cannot simply use that
representation. For the small extension-field checks the same Lean file uses a
tiny polynomial-basis `GF(2^n)` evaluator; it reuses the repository's
`kasamiExponent` and mirrors the derivative and coefficient-count formulas.
It includes golden-reference checks for the positive cases and the nearby
non-coprime failure

```text
GF(16), n=4, k=2:  |Δ| = 7,  count = 22 ≠ 32.
```

For a second implementation, independent of the Lean development, run

```bash
python3 scripts/check_boundary_cases.py
```

That script implements the same small finite fields from scratch in Python and
covers the same audit families, with some deliberately stronger sweeps.  In
particular it checks the non-subspace cases at `(n,k)=(5,2),(5,3),(7,3)`,
sweeps all 930 admissible coefficient pairs at `(5,2)`, verifies APN behavior
for the normalized Kasami exponents over `GF(32)`, asserts the non-coprime
golden values `7` and `22`, and checks non-Kasami exponent residues that
have the correct half-size derivative image but miss the Carlet count.  Thus
the audit has three different layers: generic Lean proofs, executable Lean
checks, and an independent arithmetic oracle.

## 14. Self-containment

The final theorem proves the Kasami-specific mathematical ingredients within
the Lean development. In particular, the repository proves the MCM permutation
theorem needed here, the derivative-image half-size theorem, the
Dillon--Kashyap-shaped phase formula, the Fourier/root-count conversion, both
Fermat-cubic root-existence branches, and the exact-average forcing step.

`DillonKashyapPhaseFormula` remains an explicit proposition because it is the
natural literature interface; it is not an axiom of the final theorem.

The headline theorem's axiom audit reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## 15. Compressed proof architecture

The entire argument can be compressed into the actual sequence used by the
formal proof. First reduce the arbitrary Challenge parameter to
$r=k\bmod n$ and enter the normalized core. Then

$$
\Delta_r
\longleftrightarrow
M_r(\mathrm{AS}(K))
\quad\Longrightarrow\quad
|\Delta_r|=|K|/2.
$$

The internal normalization chooses $k_0\in\{r,n-r\}$ and transports both the
coefficient problem and the half-size equation to $k_0$. From that transported
half-size equation, the proof obtains in parallel

$$
\begin{cases}
\text{multiplicative phase formula},\\
\text{additive-character triple-count identity},\\
\text{exact slope average}.
\end{cases}
$$

The phase branch then splits by cube support:

$$
\text{phase}
\longrightarrow
\begin{cases}
\text{noncube support}\Longrightarrow C(\rho)=0,\\
\text{cube/cube support}\Longrightarrow
\text{twisted root count}\Longrightarrow
\text{Fermat-cubic incidence}\Longrightarrow C(\rho)\ge 0.
\end{cases}
$$

Thus for every admissible slope

$$
N(\rho)\ge |K|^2/8,
\qquad
\mathrm{avg}_\rho N(\rho)=|K|^2/8,
$$

which forces

$$
N(\rho)=|K|^2/8\ \forall\rho.
$$

The coefficient theorem is then transported from $k_0$ back to the normalized
core parameter $r$, giving `carlet_kasami_cyclic_additive_core`; the outer
periodicity rewrite returns from $r=k\bmod n$ to the arbitrary Challenge
parameter in `carlet_kasami_cyclic_additive_literature`, which `Solution.lean`
applies.
