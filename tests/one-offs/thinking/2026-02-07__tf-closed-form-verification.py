"""
Verify the tf closed-form formula against algorithmic computation.
tf(b,z) = (-2 + 2b - 2b^2 + z - bz - z^2 + bz^2 + b^z(2 + 2b^2 + z + z^2 - b(2 + z + z^2))) / (2(-1 + b)^2)
stf(b) = sum_(z=1)^qg(b) tf(b,z)
"""
import math


def tf_closed(b, z):
    """Closed-form: tf(b,z) from Mathematica"""
    num = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2 + b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))
    den = 2 * (b - 1)**2
    return num // den


def qg(b):
    """Inverse triangular: find r such that tri(r) = b"""
    r = (-1 + int(math.isqrt(1 + 8*b))) // 2
    if r * (r + 1) // 2 == b:
        return r
    return None


def stf_closed(b):
    """stf via closed-form tf"""
    r = qg(b)
    if r is None:
        return None
    return sum(tf_closed(b, z) for z in range(1, r + 1))


def stf_algo(b):
    """stf via algorithmic digit-triangle approach"""
    r = (-1 + int(math.isqrt(1 + 8*b))) // 2
    digits = list(range(b))
    idx = 0
    total = 0
    for row_size in range(r, 0, -1):
        row_digits = digits[idx:idx + row_size]
        idx += row_size
        val = 0
        for d in row_digits:
            val = val * b + d
        total += val
    return total


if __name__ == "__main__":
    print('=== Verifying tf closed-form formula ===')
    print(f'stf_closed(10) = {stf_closed(10)}')
    print(f'stf_algo(10)   = {stf_algo(10)}')

    print()
    print('=== Individual tf values for base 10 ===')
    for z in range(1, 5):
        print(f'  tf(10, {z}) = {tf_closed(10, z)}')
    print(f'  sum = {sum(tf_closed(10, z) for z in range(1, 5))}')

    print()
    print(f'stf_closed(6)  = {stf_closed(6)}')
    print(f'stf_algo(6)    = {stf_algo(6)}')

    print(f'stf_closed(3)  = {stf_closed(3)}')
    print(f'stf_algo(3)    = {stf_algo(3)}')

    print()
    print('=== stf(666) ===')
    val = stf_algo(666)
    print(f'stf_algo(666) = {val}')
    print(f'digits = {len(str(val))}')
    expected = 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290
    print(f'matches expected: {val == expected}')

    val2 = stf_closed(666)
    print(f'stf_closed(666) = {val2}')
    print(f'closed matches algo: {val == val2}')
