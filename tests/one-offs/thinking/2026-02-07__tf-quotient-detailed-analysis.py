"""
Detailed analysis of Q(b,z) = tfNumerator(b,z) / (2*(b-1)^2).

Computes:
1. Q(b,z) coefficients for z=1..8
2. Recursive relation Q(b,z+1) - b*Q(b,z)
3. Verification that Q matches rowValue for multiple triangular bases

Key findings:
- Coefficients (high to low): always start with 1, second coeff related to tri(z),
  then count down by 1, last two coefficients equal
- z=1: [1, -1]
- z=2: [1, -2, -2]
- z=3: [1, -5, -4, -4]
- z=4: [1, -9, -8, -7, -7]
- z=5: [1, -14, -13, -12, -11, -11]
- z=6: [1, -20, -19, -18, -17, -16, -16]
- z=7: [1, -27, -26, -25, -24, -23, -22, -22]
- z=8: [1, -35, -34, -33, -32, -31, -30, -29, -29]

Recursion: Q(b, z+1) = b*Q(b,z) + R(b,z) where R has clean structure.
"""
from sympy import symbols, cancel, Poly
import math

b, z = symbols('b z')

N = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2 +
     b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))

print('=== Q(b,z) coefficients (high to low) for z=1..8 ===')
for zv in range(1, 9):
    Nz = N.subs(z, zv)
    Q = cancel(Nz / (2*(b-1)**2))
    p = Poly(Q, b)
    coeffs = list(p.all_coeffs())
    print('z=%d: degree=%d, coeffs=%s' % (zv, p.degree(), coeffs))

print()
print('=== Recursive relation: Q(b,z+1) - b*Q(b,z) ===')
for zv in range(1, 7):
    Nz = N.subs(z, zv)
    Nz1 = N.subs(z, zv+1)
    Qz = cancel(Nz / (2*(b-1)**2))
    Qz1 = cancel(Nz1 / (2*(b-1)**2))
    diff = cancel(Qz1 - b*Qz)
    print('z=%d: Q(b,%d) - b*Q(b,%d) = %s' % (zv, zv+1, zv, diff))

print()
print('=== Verify Q matches rowValue for multiple bases ===')
for bv in [3, 6, 10, 15, 45]:
    r = (-1 + int(math.isqrt(1 + 8*bv))) // 2
    if r*(r+1)//2 != bv:
        continue
    for zv in range(1, r+1):
        start = bv - zv*(zv+1)//2
        algo = sum((start + i) * bv**(zv-1-i) for i in range(zv))
        Nz_val = N.subs(z, zv).subs(b, bv)
        q_val = int(Nz_val) // (2*(bv-1)**2)
        ok = 'OK' if algo == q_val else 'FAIL'
        print('b=%d, z=%d: rowValue=%d, Q=%d [%s]' % (bv, zv, algo, q_val, ok))
