"""
Test the stf-k^2 conjecture:
  For b = tri(r) where r = k^2, is stf(b) divisible by 6?

Cases:
  k=1: r=1,  b=tri(1)=1   (trivial, base-1)
  k=2: r=4,  b=tri(4)=10  -> stf(10)=666, 666/6=111 YES
  k=3: r=9,  b=tri(9)=45  -> stf(45)=3988218576606, /6=664703096101 YES
  k=4: r=16, b=tri(16)=136 -> ?
  k=5: r=25, b=tri(25)=325 -> ?
"""
from math import comb


def stf(b):
    """Compute stf(b) using the digit-triangle method."""
    # Find row count r such that tri(r) = b
    # tri(r) = r*(r+1)/2 = b => r = (-1 + sqrt(1+8b))/2
    import math
    disc = 1 + 8 * b
    sqrt_disc = math.isqrt(disc)
    if sqrt_disc * sqrt_disc != disc:
        return None
    r = (sqrt_disc - 1) // 2
    if r * (r + 1) // 2 != b:
        return None
    if b <= 1:
        return None

    # Build digits 0..b-1, fill triangle bottom-up
    # Row r (bottom) has r digits, row r-1 has r-1 digits, etc.
    # Digits fill from bottom-left: row r gets 0..r-1, row r-1 gets r..2r-2, etc.
    # Actually from the examples:
    # stf(10): Row4=0123, Row3=456, Row2=78, Row1=9
    # So bottom row gets LOWEST digits, top row gets HIGHEST
    digits = list(range(b))
    total = 0
    pos = 0
    for z in range(r, 0, -1):  # z=r (bottom, largest) to z=1 (top, smallest)
        row_digits = digits[pos:pos + z]
        # Interpret as base-b number
        row_val = 0
        for d in row_digits:
            row_val = row_val * b + d
        total += row_val
        pos += z
    return total


def greedy_canonical(X, weights):
    """Greedy decomposition: largest weight first."""
    remaining = X
    n = len(weights)
    digits = [0] * n
    for i in sorted(range(n), key=lambda j: weights[j], reverse=True):
        if weights[i] > 0:
            digits[i] = remaining // weights[i]
            remaining -= digits[i] * weights[i]
    return digits


# Test the conjecture
print('=== Testing stf-k^2 Conjecture ===')
print(f'{"k":>3} {"r=k^2":>6} {"b=tri(r)":>10} {"stf(b)":>50} {"div6":>5} {"stf/6":>45}')
print('-' * 130)

row4_weights = [comb(4, k) for k in range(5)]  # [1, 4, 6, 4, 1]

for k in range(2, 6):
    r = k * k
    b = r * (r + 1) // 2

    val = stf(b)
    if val is not None:
        div6 = val % 6 == 0
        quotient = val // 6 if div6 else 'N/A'
        print(f'{k:>3} {r:>6} {b:>10} {val:>50} {str(div6):>5} {str(quotient):>45}')

        # Pascal Row 4 representation
        d = greedy_canonical(val, row4_weights)
        is_pure_center = d[0] == 0 and d[1] == 0 and d[3] == 0 and d[4] == 0
        print(f'    Row 4 repr: {d} {"<-- PURE CENTER!" if is_pure_center else ""}')
    else:
        print(f'{k:>3} {r:>6} {b:>10} {"SKIPPED (base too small)":>50}')

# Also check non-perfect-square r values as control
print()
print('=== Control: non-perfect-square r values ===')
for r in [3, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15]:
    b = r * (r + 1) // 2
    val = stf(b)
    if val is not None:
        div6 = val % 6 == 0
        div2 = val % 2 == 0
        div3 = val % 3 == 0
        print(f'  r={r:>2}, b={b:>3}: stf={val}, div2={div2}, div3={div3}, div6={div6}')

# Also check: is stf(b) mod 6 related to r mod something?
print()
print('=== stf(b) mod 6 for all r up to 15 ===')
for r in range(2, 16):
    b = r * (r + 1) // 2
    val = stf(b)
    if val is not None:
        is_sq = int(r**0.5)**2 == r
        print(f'  r={r:>2} {"(k^2)" if is_sq else "     "}, b={b:>3}: stf mod 6 = {val % 6}, stf mod 2 = {val % 2}, stf mod 3 = {val % 3}')
