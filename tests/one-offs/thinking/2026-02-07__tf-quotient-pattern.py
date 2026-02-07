"""
Analyze the quotient Q(b,z) = tfNumerator(b,z) / (2*(b-1)^2).

Q(b,z) is what tf(b,z) actually equals after cancellation.
Goal: find a direct formula for Q without going through the fraction.
"""
from sympy import symbols, simplify, factor, Poly, collect

b, z = symbols('b z')

N = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2 +
     b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))

print('=== Q(b,z) = N / (2*(b-1)^2) for z=1..7 ===')
for zv in range(1, 8):
    Nz = N.subs(z, zv)
    Q = simplify(Nz / (2*(b-1)**2))
    Q_expanded = Poly(Q, b)
    print('z=%d: Q = %s' % (zv, Q_expanded))
    # Extract coefficients
    coeffs = Q_expanded.all_coeffs()
    print('      coefficients (high to low): %s' % coeffs)

print()
print('=== Looking for pattern in coefficients ===')
print()
# Let us see the coefficient of b^(z-1) term
for zv in range(1, 8):
    Nz = N.subs(z, zv)
    Q = simplify(Nz / (2*(b-1)**2))
    p = Poly(Q, b)
    coeffs = p.all_coeffs()  # highest degree first
    print('z=%d: degree=%d, coeffs=%s' % (zv, p.degree(), list(coeffs)))

print()
print('=== Verify: Q can be written as rowValue formula ===')
print('rowValue(b, z) = sum_{i=0}^{z-1} (start + i) * b^{z-1-i}')
print('where start = b - tri(z) = b - z*(z+1)/2')
print()
for bv in [10]:
    for zv in range(1, 5):
        # Algorithmic
        start = bv - zv*(zv+1)//2
        algo = sum((start + i) * bv**(zv-1-i) for i in range(zv))
        # From Q formula
        Nz = N.subs(z, zv).subs(b, bv)
        q = Nz // (2*(bv-1)**2)
        print('b=%d, z=%d: algo=%d, Q=%d, match=%s' % (bv, zv, algo, q, algo == q))

print()
print('=== Try to find recursive formula for Q ===')
print('Q(b, z+1) in terms of Q(b, z)?')
for zv in range(1, 6):
    Nz = N.subs(z, zv)
    Nz1 = N.subs(z, zv+1)
    Qz = simplify(Nz / (2*(b-1)**2))
    Qz1 = simplify(Nz1 / (2*(b-1)**2))
    diff = simplify(Qz1 - b*Qz)
    print('z=%d: Q(b,%d) - b*Q(b,%d) = %s' % (zv, zv+1, zv, diff))
