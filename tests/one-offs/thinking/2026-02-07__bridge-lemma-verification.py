"""
Phase 3B Bridge Lemma Verification
====================================
Verify the mathematical relationships that connect the algorithmic stf
definition (foldl-based digitsToNat) to the closed-form tf formula.

The bridge lemma establishes:
  digitsToNat(b, [d0, d1, ..., d_{z-1}]) = sum_{i=0}^{z-1} d_i * b^(z-1-i)

And from there, the recursive relation:
  rowValue(b, z+1) = (b - tri(z+1)) * b^z + rowValue(b, z) - z * (b^z - 1)/(b-1)

Finally, the closed-form TriSum for stf(b).
"""
import math


# === Core definitions ===

def tri(n):
    """Triangular number: n*(n+1)/2"""
    return n * (n + 1) // 2


def qg(b):
    """Quasi-grade: largest r such that tri(r) = b (assumes b is triangular)."""
    r = int((-1 + math.isqrt(1 + 8 * b)) / 2)
    assert tri(r) == b, f"b={b} is not triangular"
    return r


def digitsToNat(b, digits):
    """Interpret a list of digits as a base-b number via foldl."""
    acc = 0
    for d in digits:
        acc = acc * b + d
    return acc


def digitsToNat_sum(b, digits):
    """Interpret a list of digits as a base-b number via positional sum.
    sum_{i=0}^{z-1} d_i * b^(z-1-i)
    """
    z = len(digits)
    return sum(d * b ** (z - 1 - i) for i, d in enumerate(digits))


def row_digits(b, z):
    """Row z from top: z consecutive digits starting at b - tri(z)."""
    start = b - tri(z)
    return [start + i for i in range(z)]


def rowValue(b, z):
    """Row z value: interpret row_digits as base-b number (algorithmic)."""
    return digitsToNat(b, row_digits(b, z))


def rowValue_sum(b, z):
    """Row z value via positional sum formula."""
    return digitsToNat_sum(b, row_digits(b, z))


def tf_closed(b, z):
    """Closed-form tf from Mathematica notebook."""
    num = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2
           + b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))
    den = 2 * (b - 1)**2
    return num // den


def stf(b):
    """Sum of all row values: stf(b) = sum_{z=1}^{qg(b)} rowValue(b, z)."""
    r = qg(b)
    return sum(rowValue(b, z) for z in range(1, r + 1))

# === Verification 1: digitsToNat foldl vs positional sum ===

def verify_foldl_sum_correspondence():
    """Verify digitsToNat(b, digits) = sum_{i=0}^{z-1} d_i * b^(z-1-i)
    for various bases and digit lists."""
    print('=' * 70)
    print('VERIFICATION 1: foldl-to-sum correspondence')
    print('  digitsToNat(b, ds) == sum_{i} d_i * b^(z-1-i)')
    print('=' * 70)

    all_ok = True

    # Test with base 10, rows z=1..4
    print('\n--- Base 10, triangle rows ---')
    b = 10
    for z in range(1, 5):
        digits = row_digits(b, z)
        val_foldl = digitsToNat(b, digits)
        val_sum = digitsToNat_sum(b, digits)
        match = val_foldl == val_sum
        all_ok = all_ok and match
        print(f'  z={z}: digits={digits}')
        print(f'    foldl  = {val_foldl}')
        print(f'    sum    = {val_sum}')
        z_len = len(digits)
        terms = [f'{d}*{b}^{z_len-1-i}' for i, d in enumerate(digits)]
        joined = ' + '.join(terms)
        print(f'    expand = {joined} = {val_sum}')
        print(f'    match  = {match}')

    # Test with arbitrary digit lists
    print('\n--- Arbitrary digit lists ---')
    test_cases = [
        (2, [1, 0, 1, 1]),      # binary 1011 = 11
        (16, [15, 0]),           # hex F0 = 240
        (3, [2, 1, 0]),         # ternary 210 = 21
        (10, [1, 2, 3, 4, 5]),  # decimal 12345
        (7, [6, 5, 4, 3]),      # base-7 6543
    ]
    for b, digits in test_cases:
        val_foldl = digitsToNat(b, digits)
        val_sum = digitsToNat_sum(b, digits)
        match = val_foldl == val_sum
        all_ok = all_ok and match
        print(f'  base={b}, digits={digits}: foldl={val_foldl}, sum={val_sum}, match={match}')

    status = 'PASSED' if all_ok else 'FAILED'
    print(f'\n  ALL FOLDL-SUM TESTS: {status}')
    return all_ok

# === Verification 2: rowValue algorithmic vs sum vs closed-form ===

def verify_rowvalue_three_ways():
    """Verify rowValue matches across all three definitions for base 10."""
    print('\n' + '=' * 70)
    print('VERIFICATION 2: rowValue three-way agreement (base 10, z=1..4)')
    print('  algorithmic (foldl) vs positional sum vs closed-form')
    print('=' * 70)

    b = 10
    all_ok = True
    expected = {1: 9, 2: 78, 3: 456, 4: 123}

    for z in range(1, 5):
        val_algo = rowValue(b, z)
        val_sum = rowValue_sum(b, z)
        val_closed = tf_closed(b, z)
        exp = expected[z]

        match_all = (val_algo == val_sum == val_closed == exp)
        all_ok = all_ok and match_all

        start = b - tri(z)
        digits = row_digits(b, z)

        print(f'\n  z={z}: start={start}, digits={digits}')
        print(f'    algorithmic (foldl) = {val_algo}')
        print(f'    positional sum     = {val_sum}')
        print(f'    closed-form tf     = {val_closed}')
        print(f'    expected           = {exp}')
        print(f'    all agree          = {match_all}')

    total = sum(expected.values())
    print(f'\n  stf(10) = {total} (expected 666)')
    print(f'  computed stf(10) = {stf(10)}')
    status = 'PASSED' if all_ok else 'FAILED'
    print(f'  ALL THREE-WAY TESTS: {status}')
    return all_ok

# === Verification 3: Recursive relation for rowValue ===

def verify_recursive_relation():
    """Investigate: rowValue(b, z+1) = ? relationship to rowValue(b, z).

    For row z, digits are [s, s+1, ..., s+z-1] where s = b - tri(z).
    For row z+1, digits are [s2, s2+1, ..., s2+z] where s2 = b - tri(z+1).

    Note: s2 = b - tri(z+1) = b - tri(z) - (z+1) = s - (z+1).

    Derivation:
    digitsToNat(b, [s2, s2+1, ..., s2+z])
    = s2 * b^z + sum_{i=1}^{z} (s2+i) * b^(z-i)

    Let j = i-1, i = j+1, when i=1..z then j=0..z-1:
    = s2 * b^z + sum_{j=0}^{z-1} (s + j - z) * b^(z-1-j)
    = s2 * b^z + sum_{j=0}^{z-1} (s+j) * b^(z-1-j) - z * sum_{j=0}^{z-1} b^(z-1-j)
    = s2 * b^z + rowValue(b, z) - z * (b^z - 1)/(b - 1)

    So: rowValue(b, z+1) = (b - tri(z+1)) * b^z + rowValue(b, z) - z * (b^z - 1)/(b-1)
    """
    print('\n' + '=' * 70)
    print('VERIFICATION 3: Recursive relation for rowValue')
    print('=' * 70)

    all_ok = True

    # First, compute and show the pattern for base 10
    print('\n--- Simple multiplier search: rowValue(10, z+1) vs rowValue(10, z) ---')
    b = 10
    for z in range(1, 4):
        rv_z = rowValue(b, z)
        rv_z1 = rowValue(b, z + 1)
        diff = rv_z1 - b * rv_z
        print(f'  rowValue(10, {z})   = {rv_z}')
        print(f'  rowValue(10, {z+1}) = {rv_z1}')
        print(f'  b * rowValue(10, {z}) = {b * rv_z}')
        print(f'  rowValue(10, {z+1}) - b * rowValue(10, {z}) = {diff}')
        print()

    # Now verify the derived recursive formula
    print('--- Derived recursive formula verification ---')
    print('  rowValue(b, z+1) = s2 * b^z + rowValue(b, z) - z * (b^z - 1)/(b-1)')
    print('  where s2 = b - tri(z+1)')
    print()

    for b in [3, 6, 10, 15, 21]:
        r = qg(b)
        print(f'  Base b={b}, r={r}:')
        base_ok = True
        for z in range(1, r):
            rv_z = rowValue(b, z)
            rv_z1 = rowValue(b, z + 1)

            s_prime = b - tri(z + 1)
            geometric = z * (b**z - 1) // (b - 1)
            rv_z1_predicted = s_prime * b**z + rv_z - geometric

            match = (rv_z1 == rv_z1_predicted)
            base_ok = base_ok and match

            if not match:
                print(f'    z={z}->{z+1}: actual={rv_z1}, predicted={rv_z1_predicted} MISMATCH')
                print(f'      s2={s_prime}, b^z={b**z}, geometric={geometric}')
                print(f'      s2*b^z = {s_prime * b**z}')
                print(f'      rv_z = {rv_z}')
                geo_exact = (b**z - 1) / (b - 1)
                print(f'      (b^z-1)/(b-1) = {geo_exact}')
                print(f'      z * that = {z * geo_exact}')

        all_ok = all_ok and base_ok
        print(f'    all rows match: {base_ok}')

    status = 'PASSED' if all_ok else 'FAILED'
    print(f'\n  ALL RECURSIVE TESTS: {status}')
    return all_ok

# === Verification 4: Closed-form TriSum for stf ===

def verify_trisum_closed_form():
    """Verify stf(b) = sum_{z=1}^{qg(b)} rowValue(b, z) for triangular bases.
    Also verify against stf(b) = sum_{z=1}^{r} tf_closed(b, z).
    """
    print('\n' + '=' * 70)
    print('VERIFICATION 4: Closed-form TriSum for stf(b)')
    print('=' * 70)

    all_ok = True
    triangular_bases = [3, 6, 10, 15, 21, 28, 36, 45, 55, 66,
                        78, 91, 105, 120, 136, 153, 171, 190, 210, 666]

    print(f'\n  {"b":>5} {"r":>3} {"stf_algo":>20} {"stf_closed":>20} {"match":>6}')
    print('  ' + '-' * 56)

    for b in triangular_bases:
        r = qg(b)
        stf_algo = sum(rowValue(b, z) for z in range(1, r + 1))
        stf_closed = sum(tf_closed(b, z) for z in range(1, r + 1))
        match = stf_algo == stf_closed
        all_ok = all_ok and match
        mstr = 'OK' if match else 'FAIL'
        print(f'  {b:>5} {r:>3} {stf_algo:>20} {stf_closed:>20} {mstr:>6}')

    # Detailed breakdown for b=3, 6, 10, 15
    print('\n--- Detailed breakdown for selected bases ---')
    for b in [3, 6, 10, 15]:
        r = qg(b)
        print(f'\n  Base b={b}, r=qg(b)={r}:')
        total = 0
        for z in range(1, r + 1):
            digits = row_digits(b, z)
            val = rowValue(b, z)
            total += val
            print(f'    z={z}: digits={digits}, rowValue={val}')
        print(f'    stf({b}) = {total}')

    computed = stf(10)
    print(f'\n  stf(10) = {computed}')
    assert computed == 666, f'Expected stf(10) = 666, got {computed}'
    print(f'  stf(10) == 666: VERIFIED')

    status = 'PASSED' if all_ok else 'FAILED'
    print(f'\n  ALL TRISUM TESTS: {status}')
    return all_ok

# === Verification 5: Full bridge from foldl to closed-form ===

def verify_bridge_lemma_chain():
    """Verify the complete bridge lemma chain:
    foldl definition -> positional sum -> closed-form tf -> TriSum
    For each step, verify the equivalence holds numerically.
    """
    print('\n' + '=' * 70)
    print('VERIFICATION 5: Full bridge lemma chain')
    print('  foldl -> sum -> closed-form -> TriSum')
    print('=' * 70)

    all_ok = True

    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 666]:
        r = qg(b)
        stf_foldl = 0
        stf_sum = 0
        stf_closed = 0
        row_ok = True

        for z in range(1, r + 1):
            digits = row_digits(b, z)
            v_foldl = digitsToNat(b, digits)
            v_sum = digitsToNat_sum(b, digits)
            v_closed = tf_closed(b, z)

            if not (v_foldl == v_sum == v_closed):
                row_ok = False
                print(f'  MISMATCH at b={b}, z={z}: foldl={v_foldl}, sum={v_sum}, closed={v_closed}')

            stf_foldl += v_foldl
            stf_sum += v_sum
            stf_closed += v_closed

        chain_ok = row_ok and (stf_foldl == stf_sum == stf_closed)
        all_ok = all_ok and chain_ok

        if not chain_ok:
            print(f'  b={b}: stf_foldl={stf_foldl}, stf_sum={stf_sum}, stf_closed={stf_closed}')

    status = 'PASSED' if all_ok else 'FAILED'
    print(f'\n  Bridge lemma chain verified for all bases: {status}')

    print('\n  KEY RESULT:')
    print('    For any triangular base b with r = qg(b):')
    print('      stf(b) = sum{z=1..r} digitsToNat(b, rowDigits(b,z))')
    print('             = sum{z=1..r} sum{i=0..z-1} (b - tri(z) + i) * b^(z-1-i)')
    print('             = sum{z=1..r} tf_closed(b, z)')
    print('    All three representations are equivalent.')

    return all_ok

# === Bonus: Digit structure visualization ===

def show_triangle_structure():
    """Visualize the digit triangle for selected bases."""
    print('\n' + '=' * 70)
    print('BONUS: Triangle digit structure visualization')
    print('=' * 70)

    for b in [3, 6, 10, 15]:
        r = qg(b)
        print(f'\n  Base b={b}, r={r}:')
        for z in range(1, r + 1):
            digits = row_digits(b, z)
            val = rowValue(b, z)
            digit_str = ' '.join(f'{d:2d}' for d in digits)
            padding = ' ' * (3 * (r - z))
            print(f'    {padding}{digit_str}  = {val}')
        pad = ' ' * (3 * r)
        print(f'    {pad}stf({b}) = {stf(b)}')


# === Main ===

if __name__ == '__main__':
    print('Phase 3B Bridge Lemma Verification')
    print('=' * 70)

    results = []

    results.append(('foldl-sum correspondence', verify_foldl_sum_correspondence()))
    results.append(('rowValue three-way', verify_rowvalue_three_ways()))
    results.append(('recursive relation', verify_recursive_relation()))
    results.append(('TriSum closed-form', verify_trisum_closed_form()))
    results.append(('bridge lemma chain', verify_bridge_lemma_chain()))

    show_triangle_structure()

    # Summary
    print('\n' + '=' * 70)
    print('SUMMARY')
    print('=' * 70)
    all_passed = True
    for name, passed in results:
        status = 'PASSED' if passed else 'FAILED'
        if not passed:
            all_passed = False
        print(f'  {name:.<40} {status}')

    print()
    if all_passed:
        print('  ALL VERIFICATIONS PASSED')
        print()
        print('  Bridge Lemma is numerically validated:')
        print('    1. foldl and positional-sum are equivalent (digitsToNat)')
        print('    2. rowValue agrees across algorithmic, sum, and closed-form')
        print('    3. Recursive relation rowValue(b, z+1) from rowValue(b, z) holds')
        print('    4. TriSum stf(b) = sum of tf_closed(b, z) for all triangular b')
        print('    5. Full chain foldl -> sum -> closed-form -> TriSum verified')
    else:
        print('  SOME VERIFICATIONS FAILED - see details above')