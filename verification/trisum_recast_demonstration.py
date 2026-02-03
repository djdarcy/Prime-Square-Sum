"""
TriSum and Recast Pattern Demonstration
========================================

This program demonstrates the pattern observed in Section 4.4 of
"Zero_AG to The Scarcity Framework: A Guide" by D. Darcy.

The observation: When using triangular numbers as bases, the TriSum
operation produces results that, when recast, yield other triangular
numbers - suggesting structural invariance across base representations.

This serves as computational verification before formal proof.
"""

def tri(n: int) -> int:
    """Compute the nth triangular number: 1 + 2 + ... + n = n(n+1)/2"""
    return n * (n + 1) // 2


def inverse_tri(t: int) -> int | None:
    """
    If t is a triangular number, return n such that tri(n) = t.
    Otherwise return None.

    Uses the quadratic formula: n = (-1 + sqrt(1 + 8t)) / 2
    """
    import math
    discriminant = 1 + 8 * t
    sqrt_disc = int(math.isqrt(discriminant))

    # Check if discriminant is a perfect square
    if sqrt_disc * sqrt_disc != discriminant:
        return None

    # Check if result is a positive integer
    if (sqrt_disc - 1) % 2 != 0:
        return None

    n = (sqrt_disc - 1) // 2

    # Verify
    if tri(n) == t:
        return n
    return None


def is_triangular(t: int) -> bool:
    """Check if t is a triangular number."""
    return inverse_tri(t) is not None


def number_to_digits(x: int, base: int) -> list[int]:
    """Convert a number to its digit representation in a given base."""
    if x == 0:
        return [0]
    digits = []
    while x > 0:
        digits.append(x % base)
        x //= base
    return digits[::-1]  # Reverse to get most significant first


def digits_to_number(digits: list[int], base: int) -> int:
    """Convert a list of digits in a given base to a number."""
    result = 0
    for d in digits:
        result = result * base + d
    return result


def recast(x: int, source_base: int, target_base: int) -> int:
    """
    Recast: take the digit representation of x in source_base,
    and reinterpret those same digits as a number in target_base.

    This is NOT base conversion - it's treating the digit string
    as if it were written in a different base.
    """
    digits = number_to_digits(x, source_base)
    return digits_to_number(digits, target_base)


def build_digit_triangle(base: int, n_rows: int) -> list[list[int]]:
    """
    Build a triangle of digits 0 through base-1, arranged with
    n_rows rows (bottom row has n_rows digits, top row has 1 digit).

    For base = Tri[n], we have exactly Tri[n] digits (0 to Tri[n]-1)
    which fill a triangle of n rows perfectly.
    """
    triangle = []
    current_digit = 0

    # Build from bottom (n_rows digits) to top (1 digit)
    for row_size in range(n_rows, 0, -1):
        row = []
        for _ in range(row_size):
            row.append(current_digit)
            current_digit += 1
        triangle.append(row)

    return triangle


def trisum(base: int, n_rows: int) -> int:
    """
    Compute TriSum for a given base.

    Arranges digits 0 to base-1 in a triangle, interprets each row
    as a number in the given base, and sums them.
    """
    triangle = build_digit_triangle(base, n_rows)

    total = 0
    for row in triangle:
        row_value = digits_to_number(row, base)
        total += row_value

    return total


def analyze_trisum_pattern(n: int, verbose: bool = True) -> dict:
    """
    Analyze the TriSum pattern for a given n.

    Uses base = Tri[n], computes TriSum, checks if result
    (or its recast to base 10) is triangular.
    """
    base = tri(n)
    trisum_value = trisum(base, n)
    trisum_in_base = number_to_digits(trisum_value, base)
    recast_value = recast(trisum_value, base, 10)

    # Check if trisum_value itself is triangular
    trisum_tri_index = inverse_tri(trisum_value)

    # Check if recast value is triangular
    recast_tri_index = inverse_tri(recast_value)

    result = {
        'n': n,
        'base': base,
        'base_name': f'Tri[{n}]',
        'trisum_value_base10': trisum_value,
        'trisum_in_base': trisum_in_base,
        'trisum_as_string': ''.join(map(str, trisum_in_base)) if max(trisum_in_base) < 10 else trisum_in_base,
        'recast_to_base10': recast_value,
        'trisum_is_triangular': trisum_tri_index is not None,
        'trisum_tri_index': trisum_tri_index,
        'recast_is_triangular': recast_tri_index is not None,
        'recast_tri_index': recast_tri_index,
    }

    if verbose:
        print(f"\n{'='*60}")
        print(f"n = {n}, base = Tri[{n}] = {base}")
        print(f"{'='*60}")
        print(f"Digit triangle (base {base}):")
        triangle = build_digit_triangle(base, n)
        for i, row in enumerate(triangle):
            indent = "  " * i
            print(f"  {indent}{row} -> {digits_to_number(row, base)} (base 10)")
        print(f"\nTriSum[{base}] = {trisum_value} (base 10)")
        print(f"TriSum[{base}] in base {base} = {result['trisum_as_string']}")
        print(f"Recast to base 10 = {recast_value}")
        print()

        if result['trisum_is_triangular']:
            print(f"[YES] TriSum value {trisum_value} = Tri[{trisum_tri_index}]")
        else:
            print(f"[NO]  TriSum value {trisum_value} is NOT triangular")

        if result['recast_is_triangular']:
            print(f"[YES] Recast value {recast_value} = Tri[{recast_tri_index}]")
            # Check for deeper pattern
            if inverse_tri(recast_tri_index) is not None:
                deeper = inverse_tri(recast_tri_index)
                print(f"  --> And {recast_tri_index} = Tri[{deeper}], so recast = Tri[Tri[{deeper}]]")
        else:
            print(f"[NO]  Recast value {recast_value} is NOT triangular")

    return result


def find_pattern_relationships(results: list[dict]) -> None:
    """Analyze relationships between consecutive results."""
    print("\n" + "="*60)
    print("PATTERN ANALYSIS")
    print("="*60)

    for r in results:
        n = r['n']
        if r['recast_is_triangular']:
            tri_idx = r['recast_tri_index']
            # Check if tri_idx relates to n
            print(f"\nn={n}: Recast = Tri[{tri_idx}]")

            # Is tri_idx = Tri[something]?
            deeper = inverse_tri(tri_idx)
            if deeper:
                print(f"       {tri_idx} = Tri[{deeper}]")
                print(f"       So: TriSum[Tri[{n}]] recast = Tri[Tri[{deeper}]]")

                # Relationship between n and deeper?
                print(f"       Relationship: {deeper} = {deeper} (n={n}, n+1={n+1}, 2n={2*n})")
        elif r['trisum_is_triangular']:
            tri_idx = r['trisum_tri_index']
            print(f"\nn={n}: TriSum (direct) = Tri[{tri_idx}]")
            deeper = inverse_tri(tri_idx)
            if deeper:
                print(f"       {tri_idx} = Tri[{deeper}]")
        else:
            print(f"\nn={n}: Neither TriSum nor Recast is triangular")
            print(f"       TriSum = {r['trisum_value_base10']}, Recast = {r['recast_to_base10']}")


def main():
    print("TriSum and Recast Pattern Demonstration")
    print("="*60)
    print("\nDefinitions:")
    print("  Tri[n] = n(n+1)/2 (triangular number)")
    print("  TriSum[b] = sum of rows when digits 0..b-1 form a triangle")
    print("  Recast = reinterpret digit string in different base")
    print("\nObservation: Using Tri[n] as base, TriSum produces")
    print("values that connect back to triangular numbers.")

    # Test for n = 2 through 8
    results = []
    for n in range(2, 9):
        result = analyze_trisum_pattern(n, verbose=True)
        results.append(result)

    find_pattern_relationships(results)

    # Summary table
    print("\n" + "="*60)
    print("SUMMARY TABLE")
    print("="*60)
    print(f"{'n':<4} {'Base':<8} {'TriSum':<12} {'Recast':<12} {'Tri?':<15} {'Pattern'}")
    print("-"*70)

    for r in results:
        tri_status = ""
        if r['recast_is_triangular']:
            tri_status = f"Tri[{r['recast_tri_index']}]"
        elif r['trisum_is_triangular']:
            tri_status = f"Tri[{r['trisum_tri_index']}] (direct)"
        else:
            tri_status = "No"

        # Determine pattern
        pattern = ""
        if r['recast_is_triangular']:
            idx = r['recast_tri_index']
            deeper = inverse_tri(idx)
            if deeper:
                pattern = f"Tri[Tri[{deeper}]]"

        print(f"{r['n']:<4} {r['base']:<8} {r['trisum_value_base10']:<12} {r['recast_to_base10']:<12} {tri_status:<15} {pattern}")


if __name__ == "__main__":
    main()
