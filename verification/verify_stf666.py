"""
Verification: stf(666) = 98-digit number from README
=====================================================

This script verifies that stf(666) - the triangular row sum for base 666 -
produces the 98-digit number claimed in the README:

37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290

Mathematical background:
- 666 is a triangular number: tri(36) = 666
- qtri(666) = 36, meaning 666 has 36 "rows" in its triangular arrangement
- stf(666) sums all rows when digits 0-665 are arranged in a 36-row triangle
  and each row is interpreted as a base-666 number

This is the target value that Prime-Square-Sum investigates: is this number
equal to a sum of primes raised to some power?
"""

from trisum_recast_demonstration import trisum, tri, inverse_tri


def verify_stf_666():
    """Verify stf(666) matches the README claim."""

    # The claimed value from the README
    EXPECTED = 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290

    # Verify 666 is triangular
    qtri_666 = inverse_tri(666)
    assert qtri_666 == 36, f"Expected qtri(666)=36, got {qtri_666}"
    print(f"[OK] 666 is triangular: tri(36) = {tri(36)} = 666")

    # Verify tri(36) = 666
    assert tri(36) == 666, f"Expected tri(36)=666, got {tri(36)}"
    print(f"[OK] Confirmed: tri(36) = 666")

    # Compute stf(666) = trisum(base=666, n_rows=36)
    print(f"\nComputing stf(666) = trisum(666, 36)...")
    print(f"  This sums 36 rows of digits 0-665 in base 666")

    computed = trisum(666, 36)

    print(f"\nResults:")
    print(f"  Computed stf(666)  = {computed}")
    print(f"  Expected (README)  = {EXPECTED}")
    print(f"  Digit count        = {len(str(computed))} digits")

    if computed == EXPECTED:
        print(f"\n[VERIFIED] stf(666) matches the 98-digit number in README")
        return True
    else:
        print(f"\n[MISMATCH] Values differ!")
        print(f"  Difference = {abs(computed - EXPECTED)}")
        return False


def show_mathematical_context():
    """Display the chain of relationships for context."""
    print("\n" + "="*70)
    print("MATHEMATICAL CONTEXT")
    print("="*70)

    print("\nThe observed pattern:")
    print("  1. tri(4) = 10                 (4th triangular number)")
    print("  2. 10 = primesum(3,1) = 2+3+5  (sum of first 3 primes, power 1)")
    print("  3. stf(10) = 666               (triangular row sum in base 10)")
    print("  4. 666 = primesum(7,2)         (sum of first 7 primes, power 2)")
    print("  5. 666 = tri(36)               (666 is ALSO triangular!)")
    print()

    print("The question: does stf(666) continue the pattern?")
    print("  a) Is stf(666) triangular?     --> NO (known)")
    print("  b) Is stf(666) = primesum(n,p) for some n,p?  --> UNKNOWN")
    print()

    print("If (b) is true, particularly for p=3, we'd have:")
    print("  primesum(3,1) -> stf(10) -> primesum(7,2) -> stf(666) -> primesum(?,3)?")
    print()

    print("Why this requires iteration (computational irreducibility):")
    print("  - There's no closed-form formula for the nth prime")
    print("  - Therefore no inverse: primesum^-1(x) cannot be computed directly")
    print("  - We must enumerate and check: primesum(1,p), primesum(2,p), ...")


if __name__ == "__main__":
    print("="*70)
    print("VERIFICATION: stf(666)")
    print("="*70)

    success = verify_stf_666()
    show_mathematical_context()

    print("\n" + "="*70)
    if success:
        print("RESULT: VERIFIED")
    else:
        print("RESULT: FAILED")
    print("="*70)
