"""
Verify that the tf closed-form formula agrees with the algorithmic
row_value computation for all rows across multiple bases.
"""
import math


def tri(n):
    return n * (n + 1) // 2


def tf_closed(b, z):
    """Closed-form tf from Mathematica notebook"""
    num = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2
           + b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))
    den = 2 * (b - 1)**2
    return num // den


def row_value_algo(b, z):
    """Row z from top has z digits, starting at digit b - tri(z)"""
    start = b - tri(z)
    val = 0
    for i in range(z):
        val = val * b + (start + i)
    return val


if __name__ == "__main__":
    print('Verifying tf_closed matches row_value_algo:')

    all_match = True
    for b in [3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153, 171, 190, 210, 666]:
        r_float = (-1 + math.isqrt(1 + 8*b)) / 2
        r = int(r_float)
        if tri(r) != b:
            continue  # skip non-triangular

        mismatches = []
        for z in range(1, r + 1):
            closed = tf_closed(b, z)
            algo = row_value_algo(b, z)
            if closed != algo:
                mismatches.append((z, closed, algo))
                all_match = False

        stf_c = sum(tf_closed(b, z) for z in range(1, r + 1))
        stf_a = sum(row_value_algo(b, z) for z in range(1, r + 1))
        status = 'OK' if stf_c == stf_a else 'MISMATCH'

        if mismatches:
            for z, c, a in mismatches:
                print(f'  b={b}, z={z}: closed={c}, algo={a} MISMATCH')

        print(f'  b={b} (r={r}): stf_closed={stf_c}, stf_algo={stf_a}, match={stf_c == stf_a}')

    print()
    if all_match:
        print('ALL TESTS PASSED: closed-form and algorithmic agree for all tested bases.')
    else:
        print('SOME MISMATCHES FOUND')
