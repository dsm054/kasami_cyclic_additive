#!/usr/bin/env python3
"""Independent exact oracle for the Kasami cyclic-additive boundary cases.

No external packages are used. GF(2^n) is represented in a polynomial basis,
with addition as XOR and multiplication reduced modulo the listed irreducible
binary polynomial.

This script does *not* execute the Lean definitions. Its purpose is the
opposite: it independently reimplements the finite-field arithmetic and checks
properties predicted by the theorem or by the symbolic boundary lemmas.
Positive-case expectations are derived from the theorem formulas; the selected
non-coprime case deliberately pins the independently observed values 7 and 22
as golden references so drift is detected.
"""

from itertools import product
from math import gcd


# Named audit cases used by both the focused checks and the main replay.
CARLET_F32_K2_CASE = (5, 2, 0b100101, 1, 2)
CARLET_F128_K3_CASE = (7, 3, 0b10000011, 1, 2)
NON_KASAMI_F128_EXPONENTS = (29, 43, 63)


def gf_mul(a: int, b: int, n: int, modulus: int) -> int:
    """Multiply two elements of GF(2^n) in the polynomial basis.

    Args:
        a: First operand, as an n-bit coefficient vector.
        b: Second operand, as an n-bit coefficient vector.
        n: Field extension degree.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        The product a * b reduced modulo ``modulus``, as an n-bit vector.
    """
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & (1 << n):
            a ^= modulus
    return out & ((1 << n) - 1)


def gf_pow(a: int, exponent: int, n: int, modulus: int) -> int:
    """Raise an element of GF(2^n) to a non-negative power by square-and-multiply.

    Args:
        a: Base element, as an n-bit coefficient vector.
        exponent: Non-negative integer exponent.
        n: Field extension degree.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        ``a`` raised to ``exponent``, with the empty product 0^0 taken as 1.
    """
    out = 1
    while exponent:
        if exponent & 1:
            out = gf_mul(out, a, n, modulus)
        a = gf_mul(a, a, n, modulus)
        exponent >>= 1
    return out


def kasami_exponent(k: int) -> int:
    """Return the Kasami exponent d = 4^k - 2^k + 1.

    Args:
        k: Kasami parameter.

    Returns:
        The exponent defining the Kasami power map x -> x^d.
    """
    return 4**k - 2**k + 1


def derivative_image_of_exponent(n: int, d: int, modulus: int) -> set[int]:
    """Compute the image of the derivative in direction 1 at an arbitrary exponent.

    The derivative at direction 1 is b -> (b+1)^d + b^d, shifted by the constant
    1 so that the image is the set Δ used by the Carlet counting argument.
    Keeping d as a parameter lets the negative controls run through exactly the
    same code as the Kasami cases, mirroring the Lean model.

    Args:
        n: Field extension degree.
        d: Exponent defining the power map x -> x^d.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        The set Δ of distinct derivative values over all b in GF(2^n).
    """
    return {
        gf_pow(b ^ 1, d, n, modulus) ^ gf_pow(b, d, n, modulus) ^ 1
        for b in range(1 << n)
    }


def derivative_image(n: int, k: int, modulus: int) -> set[int]:
    """Compute the image of the derivative of the Kasami map in direction 1.

    Args:
        n: Field extension degree.
        k: Kasami parameter.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        The set Δ of distinct derivative values over all b in GF(2^n).
    """
    return derivative_image_of_exponent(n, kasami_exponent(k), modulus)


def trace(x: int, n: int, modulus: int) -> int:
    """Compute the absolute trace x + x^2 + ... + x^(2^(n-1)) of a field element.

    Args:
        x: Field element, as an n-bit coefficient vector.
        n: Field extension degree.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        The trace, which lies in the prime subfield and so is 0 or 1.
    """
    acc = 0
    y = x
    for _ in range(n):
        acc ^= y
        y = gf_mul(y, y, n, modulus)
    return acc


def trace_zero(n: int, modulus: int) -> set[int]:
    """Return the trace hyperplane H0 = {x : Tr(x) = 0}.

    Args:
        n: Field extension degree.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        The set of the 2^(n-1) elements of trace zero.
    """
    return {x for x in range(1 << n) if trace(x, n, modulus) == 0}


def is_subspace(delta: set[int]) -> bool:
    """Test whether a set of field elements is closed under addition.

    Args:
        delta: A set of elements, as n-bit coefficient vectors.

    Returns:
        True if the set is an F2-subspace, i.e. closed under XOR.
    """
    return all((a ^ b) in delta for a in delta for b in delta)


def is_apn(n: int, k: int, modulus: int) -> bool:
    """Test whether the Kasami power map is APN on GF(2^n).

    APN means every nonzero direction a makes b -> (b+a)^d + b^d exactly
    two-to-one. Since that map is invariant under b -> b + a its fibres are
    unions of pairs, so being two-to-one is equivalent to the image having
    2^(n-1) elements.

    Args:
        n: Field extension degree.
        k: Kasami parameter.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Returns:
        True if the map x -> x^d is APN on GF(2^n).
    """
    d = kasami_exponent(k)
    return all(
        len(
            {
                gf_pow(b ^ a, d, n, modulus) ^ gf_pow(b, d, n, modulus)
                for b in range(1 << n)
            }
        )
        == 1 << (n - 1)
        for a in range(1, 1 << n)
    )


def triple_count_in(delta: set[int], n: int, modulus: int, v1: int, v2: int) -> int:
    """Count vanishing linear combinations of three elements drawn from a set.

    Enumerates all triples (x, y, z) in delta^3 and counts those satisfying
    v1*x + v2*y + v3*z = 0 in GF(2^n), where v3 = v1 + v2. The enumeration is
    deliberately direct, mirroring the Lean filter over the triple product
    rather than shortcutting through field division.

    Args:
        delta: The set Δ the triples are drawn from.
        n: Field extension degree.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        v1: First coefficient.
        v2: Second coefficient; the third coefficient is v1 XOR v2.

    Returns:
        The number of triples whose combination vanishes.
    """
    v3 = v1 ^ v2
    count = 0
    for x, y, z in product(delta, repeat=3):
        total = (
            gf_mul(v1, x, n, modulus)
            ^ gf_mul(v2, y, n, modulus)
            ^ gf_mul(v3, z, n, modulus)
        )
        count += total == 0
    return count


def triple_count(n: int, k: int, modulus: int, v1: int, v2: int) -> tuple[int, int]:
    """Count vanishing triples for the Kasami parameter k.

    Args:
        n: Field extension degree.
        k: Kasami parameter.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        v1: First coefficient.
        v2: Second coefficient; the third coefficient is v1 XOR v2.

    Returns:
        A pair ``(delta_size, count)``: the cardinality of Δ and the number of
        triples whose combination vanishes.
    """
    delta = derivative_image(n, k, modulus)
    return len(delta), triple_count_in(delta, n, modulus, v1, v2)


def carlet_target(n: int) -> int:
    """Return the triple count 2^(2n-3) predicted by Carlet's conjecture.

    Args:
        n: Field extension degree.

    Returns:
        The expected number of vanishing triples for admissible coefficients.
    """
    return 1 << (2 * n - 3)


def half_field_size(n: int) -> int:
    """Return 2^(n-1), the expected cardinality of Δ.

    Args:
        n: Field extension degree.

    Returns:
        Half the size of GF(2^n).
    """
    return 1 << (n - 1)


def check_admissible(n: int, k: int, modulus: int, v1: int, v2: int) -> None:
    """Verify the conjecture on one admissible instance and report the values.

    Args:
        n: Field extension degree.
        k: Kasami parameter; must satisfy 1 <= k < n and gcd(k, n) = 1.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        v1: First coefficient; must be non-zero and distinct from ``v2``.
        v2: Second coefficient; must be non-zero and distinct from ``v1``.

    Raises:
        AssertionError: If the hypotheses fail, if |Δ| is not 2^(n-1), or if the
            triple count differs from the Carlet target 2^(2n-3).
    """
    assert 1 <= k < n
    assert gcd(k, n) == 1
    assert v1 != 0 and v2 != 0 and v1 != v2
    delta_size, count = triple_count(n, k, modulus, v1, v2)
    assert delta_size == half_field_size(n), (n, k, delta_size)
    assert count == carlet_target(n), (n, k, v1, v2, count)
    print(
        f"GF(2^{n}), k={k}, admissible: |Δ|={delta_size}, "
        f"count={count}, target={carlet_target(n)}"
    )


def check_structure(n: int, k: int, modulus: int, expect_hyperplane: bool) -> None:
    """Check whether Δ is the trace hyperplane, as the branch of k predicts.

    In the easy-branch cases checked here the image Δ is H0, hence a subspace,
    and the triple count is forced by hyperplane geometry.  The selected
    non-easy cases are not even closed under addition.  This check records which
    behavior occurs on each audited instance.

    Args:
        n: Field extension degree.
        k: Kasami parameter; must satisfy 1 <= k < n and gcd(k, n) = 1.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        expect_hyperplane: Whether Δ is expected to equal H0.

    Raises:
        AssertionError: If the hypotheses fail, if |Δ| is not 2^(n-1), or if the
            observed structure disagrees with ``expect_hyperplane``.
    """
    assert 1 <= k < n
    assert gcd(k, n) == 1
    easy_branch = k % n in (1, n - 1)
    assert expect_hyperplane == easy_branch, (n, k, expect_hyperplane)
    delta = derivative_image(n, k, modulus)
    assert len(delta) == half_field_size(n), (n, k, len(delta))
    eq_h0 = delta == trace_zero(n, modulus)
    subspace = is_subspace(delta)
    assert eq_h0 == expect_hyperplane, (n, k, eq_h0)
    assert subspace == expect_hyperplane, (n, k, subspace)
    print(
        f"GF(2^{n}), k={k}: |Δ|={len(delta)}, Δ==H0 {eq_h0}, subspace {subspace} "
        f"({'easy' if easy_branch else 'nontrivial'} branch)"
    )


def check_all_pairs(n: int, k: int, modulus: int) -> None:
    """Verify that the triple count is constant over every admissible pair.

    The conjecture asserts constancy, not merely correctness at one coefficient
    pair, so this sweeps all distinct non-zero (v1, v2).

    Args:
        n: Field extension degree.
        k: Kasami parameter; must satisfy 1 <= k < n and gcd(k, n) = 1.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Raises:
        AssertionError: If any admissible pair misses the Carlet target.
    """
    delta = derivative_image(n, k, modulus)
    target = carlet_target(n)
    counts = {
        triple_count_in(delta, n, modulus, v1, v2)
        for v1 in range(1, 1 << n)
        for v2 in range(1, 1 << n)
        if v1 != v2
    }
    assert counts == {target}, (n, k, sorted(counts))
    print(
        f"GF(2^{n}), k={k}: all {((1 << n) - 1) * ((1 << n) - 2)} admissible "
        f"pairs give count {target}"
    )


def check_apn(n: int, k: int, modulus: int) -> None:
    """Verify that the Kasami power map is APN, the property defining it.

    Args:
        n: Field extension degree.
        k: Kasami parameter.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.

    Raises:
        AssertionError: If some nonzero direction fails to be two-to-one.
    """
    assert is_apn(n, k, modulus), (n, k)
    print(f"GF(2^{n}), k={k}, d={kasami_exponent(k)}: APN (every direction 2-to-1)")


def check_degenerate(n: int, k: int, modulus: int, v1: int, v2: int) -> None:
    """Verify the |Δ|^2 triple count predicted for degenerate coefficients.

    Degenerate means v1 = v2 or one of them is zero, so that the third
    coefficient v1 + v2 vanishes or the constraint collapses to two free
    choices.

    Args:
        n: Field extension degree.
        k: Kasami parameter.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        v1: First coefficient.
        v2: Second coefficient.

    Raises:
        AssertionError: If the triple count is not |Δ|^2.
    """
    delta_size, count = triple_count(n, k, modulus, v1, v2)
    assert count == delta_size**2, (n, k, v1, v2, delta_size, count)
    print(
        f"GF(2^{n}), k={k}, coefficients=({v1},{v2}): "
        f"|Δ|={delta_size}, count={count}=|Δ|^2"
    )


def inspect_non_coprime(
    n: int,
    k: int,
    modulus: int,
    expected_delta_size: int,
    expected_counts: list[int],
    v1: int = 1,
) -> None:
    """Check a non-coprime golden case against independently recorded values.

    Sweeps every admissible second coefficient, verifies the exact observed
    derivative-image size and set of triple counts, and also confirms that the
    coprime-case conclusions fail.

    Args:
        n: Field extension degree.
        k: Kasami parameter; must satisfy 1 <= k < n and gcd(k, n) != 1.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        expected_delta_size: Golden derivative-image cardinality.
        expected_counts: Golden sorted list of distinct admissible triple counts.
        v1: First coefficient, held fixed across the sweep.

    Raises:
        AssertionError: If the hypotheses fail, the golden values drift, or the
            strengthened coprime-case conclusions unexpectedly both hold.
    """
    assert 1 <= k < n
    assert gcd(k, n) != 1
    target = carlet_target(n)
    expected_half = half_field_size(n)

    delta = derivative_image(n, k, modulus)
    counts = {
        v2: triple_count(n, k, modulus, v1, v2)[1]
        for v2 in range(1 << n)
        if v2 != 0 and v2 != v1
    }

    distinct_counts = sorted(set(counts.values()))
    assert len(delta) == expected_delta_size, (n, k, len(delta), expected_delta_size)
    assert distinct_counts == expected_counts, (n, k, distinct_counts, expected_counts)

    # The same golden case must also witness failure of the strengthened
    # coprime-case statement.
    assert len(delta) != expected_half or any(c != target for c in counts.values())
    print(
        f"GF(2^{n}), k={k}, gcd={gcd(k, n)}: "
        f"|Δ|={len(delta)} (half-field target {expected_half}); "
        f"admissible counts={distinct_counts} (Carlet target {target})"
    )


def check_negative_control(n: int, d: int, modulus: int, v1: int, v2: int) -> None:
    """Check a non-Kasami exponent that has the right |Δ| but the wrong count.

    Most wrong exponents are rejected by |Δ| alone. These are the interesting
    ones: they pass the cardinality filter and still miss the Carlet target, so
    they witness that the count constrains more than the size of Δ and that the
    formalized count is sensitive enough to detect a wrong exponent.

    Args:
        n: Field extension degree.
        d: A non-Kasami exponent.
        modulus: Irreducible binary polynomial of degree n, bit x^n included.
        v1: First coefficient.
        v2: Second coefficient.

    Raises:
        AssertionError: If d is equivalent modulo 2^n-1 to a normalized Kasami
            exponent, if |Δ| is not 2^(n-1), or if the count unexpectedly hits
            the Carlet target.
    """
    period = (1 << n) - 1
    kasami_residues = {kasami_exponent(k) % period for k in range(1, n)}
    assert d % period not in kasami_residues, (n, d, d % period, sorted(kasami_residues))
    delta = derivative_image_of_exponent(n, d, modulus)
    assert len(delta) == half_field_size(n), (n, d, len(delta))
    count = triple_count_in(delta, n, modulus, v1, v2)
    assert count != carlet_target(n), (n, d, v1, v2, count)
    print(
        f"GF(2^{n}), non-Kasami d={d}: |Δ|={len(delta)} (correct size), "
        f"count={count} != target {carlet_target(n)}"
    )


def main() -> None:
    """Run the boundary-case checks over small fields and print the results.

    The case families match the `native_decide` audits in
    `KasamiCyclicAdditive/BoundaryComputations.lean`.  Some Python checks are
    deliberately stronger sweeps, so the correspondence is by audit family
    rather than literally one assertion for one theorem.
    """
    # Irreducible binary polynomials:
    # x^2+x+1, x^3+x+1, x^4+x+1, x^5+x^2+1, x^7+x+1.
    f4 = 0b111
    f8 = 0b1011
    f16 = 0b10011
    f32 = 0b100101
    f128 = 0b10000011

    # The exponent matches the closed form q^2 - q + 1 used in the literature.
    for k in range(1, 7):
        assert kasami_exponent(k) == (2**k) ** 2 - 2**k + 1
    print(f"d(k) for k=1..6: {[kasami_exponent(k) for k in range(1, 7)]}")

    # Positive instances. The expected image size and count are derived from
    # n, not supplied as test data.
    check_admissible(2, 1, f4, 1, 2)
    check_admissible(3, 1, f8, 1, 2)
    check_admissible(3, 2, f8, 1, 2)
    check_admissible(4, 1, f16, 1, 2)

    # Checked easy-branch cases: Δ is the trace hyperplane, so the count is
    # forced by hyperplane geometry and exercises none of the nonlinear case.
    check_structure(2, 1, f4, expect_hyperplane=True)
    check_structure(3, 1, f8, expect_hyperplane=True)
    check_structure(3, 2, f8, expect_hyperplane=True)
    check_structure(4, 1, f16, expect_hyperplane=True)
    check_structure(5, 1, f32, expect_hyperplane=True)

    # The genuinely nontrivial branch. n=5, k=2 is the smallest admissible pair
    # with k not congruent to +-1 mod n.
    n32, k32, mod32, v132, v232 = CARLET_F32_K2_CASE
    assert mod32 == f32
    check_structure(n32, k32, mod32, expect_hyperplane=False)
    check_admissible(n32, k32, mod32, v132, v232)
    check_all_pairs(n32, k32, mod32)
    check_structure(5, 3, f32, expect_hyperplane=False)
    check_admissible(5, 3, f32, 1, 2)

    # Outside the congruence classes covered by the general Nagy--Vajda proof.
    # Their exhaustive n <= 13 computation also covers this finite case.
    n128, k128, mod128, v1128, v2128 = CARLET_F128_K3_CASE
    assert mod128 == f128
    check_structure(n128, k128, mod128, expect_hyperplane=False)
    check_admissible(n128, k128, mod128, v1128, v2128)

    # The exponent is tied to the property that defines it.
    for k in (1, 2, 3, 4):
        check_apn(5, k, f32)

    # The symbolic boundary lemmas predict |Δ|^2 in these degenerate cases.
    check_degenerate(2, 1, f4, 1, 1)
    check_degenerate(2, 1, f4, 0, 1)

    # Deliberately violate gcd(k,n)=1; the golden values are asserted, not just
    # reported, because the Lean audit hardcodes them.
    inspect_non_coprime(4, 2, f16, expected_delta_size=7, expected_counts=[22])

    # Non-Kasami power-map residues that survive the cardinality filter and
    # still fail the Carlet count.
    for d in NON_KASAMI_F128_EXPONENTS:
        check_negative_control(7, d, f128, 1, 2)


if __name__ == "__main__":
    main()
