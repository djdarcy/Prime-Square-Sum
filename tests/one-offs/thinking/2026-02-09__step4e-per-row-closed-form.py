"""
Step 4E — Per-row closed form verification
============================================

Verify the Nat-safe additive identity:
  (b-1)^2 * rv'(b,z) + (b - tri(z)) * (b-1) + (z-1) * (b-1) + b
    = (b - tri(z)) * (b-1) * b^z + b^z

This is equivalent to: 2*(b-1)^2 * rv'(b,z) = N(b,z) where
  N(b,z) = -2 + 2b - 2b^2 + z - bz - z^2 + bz^2
           + b^z * (2 + 2b^2 + z + z^2 - b*(2 + z + z^2))

Date: 2026-02-09
"""
import math


def tri(n):
    return n * (n + 1) // 2


def rv_prime(b, z):
    """rowValue'(b, z) = Σ_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def N_poly(b, z):
    """The Mathematica/sympy polynomial N(b,z)"""
    return (-2 + 2 * b - 2 * b ** 2 + z - b * z - z ** 2 + b * z ** 2
            + b ** z * (2 + 2 * b ** 2 + z + z ** 2 - b * (2 + z + z ** 2)))


# ---- Category 1: Main identity (Nat-safe additive form) ----
print("=" * 60)
print("Category 1: Nat-safe additive identity")
print("  (b-1)^2 * rv' + (b-tri(z))*(b-1) + (z-1)*(b-1) + b")
print("  = (b-tri(z))*(b-1)*b^z + b^z")
print("=" * 60)

passes = 0
for b in range(2, 30):
    for z in range(1, 12):
        if tri(z) > b:
            break
        rv = rv_prime(b, z)
        lhs = (b - 1) ** 2 * rv + (b - tri(z)) * (b - 1) + (z - 1) * (b - 1) + b
        rhs = (b - tri(z)) * (b - 1) * b ** z + b ** z
        assert lhs == rhs, f"FAIL: b={b}, z={z}"
        passes += 1

print(f"  PASSED: {passes} cases (b=2..29, z=1..11)")

# ---- Category 2: Cross-check with N(b,z) polynomial ----
print()
print("=" * 60)
print("Category 2: Cross-check 2*(b-1)^2 * rv' == N(b,z)")
print("=" * 60)

passes = 0
for b in range(2, 30):
    for z in range(1, 12):
        if tri(z) > b:
            break
        rv = rv_prime(b, z)
        lhs = 2 * (b - 1) ** 2 * rv
        rhs = N_poly(b, z)
        assert lhs == rhs, f"FAIL: b={b}, z={z}, lhs={lhs}, rhs={rhs}"
        passes += 1

print(f"  PASSED: {passes} cases")

# ---- Category 3: weighted_power_sum_reverse ----
print()
print("=" * 60)
print("Category 3: Weighted power sum reverse")
print("  Sum i*b^(z-1-i) == Sum (z-1-i)*b^i")
print("=" * 60)

passes = 0
for b in range(0, 15):
    for z in range(0, 10):
        lhs = sum(i * b ** (z - 1 - i) for i in range(z))
        rhs = sum((z - 1 - i) * b ** i for i in range(z))
        assert lhs == rhs, f"FAIL: b={b}, z={z}"
        passes += 1

print(f"  PASSED: {passes} cases (b=0..14, z=0..9)")

# ---- Category 4: Decomposition chain verification ----
print()
print("=" * 60)
print("Category 4: Full decomposition chain")
print("  rv' = (b-tri(z))*G_asc + W_asc")
print("  (b-1)*G_asc + 1 = b^z")
print("  (b-1)^2*W_asc + (z-1)*(b-1) + b = b^z")
print("=" * 60)

passes = 0
for b in range(2, 20):
    for z in range(1, 10):
        if tri(z) > b:
            break
        rv = rv_prime(b, z)
        G_asc = sum(b ** i for i in range(z))
        W_asc = sum((z - 1 - i) * b ** i for i in range(z))

        # Split identity
        assert rv == (b - tri(z)) * G_asc + W_asc, f"Split FAIL: b={b}, z={z}"
        # Geometric identity
        assert (b - 1) * G_asc + 1 == b ** z, f"Geom FAIL: b={b}, z={z}"
        # Weighted identity
        assert (b - 1) ** 2 * W_asc + (z - 1) * (b - 1) + b == b ** z, f"Weight FAIL: b={b}, z={z}"
        passes += 1

print(f"  PASSED: {passes} cases (b=2..19, z=1..9)")

# ---- Category 5: Concrete values for native_decide ----
print()
print("=" * 60)
print("Category 5: Concrete values for native_decide checks")
print("=" * 60)

test_cases = [(10, 1), (10, 2), (10, 3), (10, 4), (6, 1), (6, 2), (6, 3), (15, 1), (15, 2), (15, 3), (15, 4), (15, 5)]
for b, z in test_cases:
    rv = rv_prime(b, z)
    lhs = (b - 1) ** 2 * rv + (b - tri(z)) * (b - 1) + (z - 1) * (b - 1) + b
    rhs = (b - tri(z)) * (b - 1) * b ** z + b ** z
    print(f"  (b={b:2d}, z={z}): rv'={rv:>8}, LHS={lhs:>12}, RHS={rhs:>12}, match={lhs == rhs}")

print()
print("All categories passed.")
