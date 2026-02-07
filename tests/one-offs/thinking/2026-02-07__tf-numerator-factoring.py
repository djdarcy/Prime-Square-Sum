"""
Symbolic analysis of the tf numerator to verify divisibility by 2*(b-1)^2.

Key findings:
- N(1, z) = 0 for all z (b=1 is a root)
- N'(1, z) = 0 for all z (b=1 is a double root)
- N factors as 2*(b-1)^2 * Q(b,z) for each z
- The second derivative N''(1,z) = 2*z*(1-z^2) which is NOT always zero,
  confirming that (b-1)^2 is the exact multiplicity, not (b-1)^3.

This means: tf(b,z) = Q(b,z) / 1 = Q(b,z) after cancellation,
where Q is a polynomial in b of degree z.
"""
from sympy import symbols, diff, simplify, factor

b, z = symbols('b z')

# tf numerator symbolically
N = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2 +
     b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))

print('=== Evaluations at b=1 ===')
print('N(b=1, z) =', simplify(N.subs(b, 1)))
print()

# Derivative w.r.t. b
Nb = diff(N, b)
print("N'(b=1, z) =", simplify(Nb.subs(b, 1)))
print()

# Second derivative
Nbb = diff(N, b, 2)
print("N''(b=1, z) =", simplify(Nbb.subs(b, 1)))
print()

# Factor N as polynomial in b for specific z values
print('=== Factored form for concrete z ===')
for zv in range(1, 8):
    Nz = N.subs(z, zv)
    f = factor(Nz)
    print('z=%d: N = %s' % (zv, f))

print()

# Verify the quotient Q(b,z) = N / (2*(b-1)^2) for concrete z
print('=== Quotient Q(b,z) = N / (2*(b-1)^2) ===')
for zv in range(1, 6):
    Nz = N.subs(z, zv)
    Q = simplify(Nz / (2*(b-1)**2))
    print('z=%d: Q = %s' % (zv, Q))

# Verify divisibility numerically
print()
print('=== Numerical divisibility check ===')

def tf_num(bv, zv):
    return (-2 + 2*bv - 2*bv**2 + zv - bv*zv - zv**2 + bv*zv**2 +
            bv**zv * (2 + 2*bv**2 + zv + zv**2 - bv*(2 + zv + zv**2)))

for bv in [3, 6, 10, 15, 45, 136, 325, 666]:
    den = 2*(bv-1)**2
    # qg(b) = number of rows
    import math
    r = (-1 + int(math.isqrt(1 + 8*bv))) // 2
    all_ok = True
    for zv in range(1, r+1):
        num = tf_num(bv, zv)
        if num % den != 0:
            print('  FAIL: b=%d, z=%d' % (bv, zv))
            all_ok = False
    if all_ok:
        print('  b=%d: all z=1..%d OK' % (bv, r))
