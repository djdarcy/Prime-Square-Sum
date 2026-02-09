"""
Step 4E — Approach derivation and closed-form exploration
=========================================================

Documents the exploration from N(b,z) polynomial to the Nat-safe additive form.
Evaluates three approaches:
  - N(b,z) polynomial form (needs Z-cast or sign separation)
  - Direct induction via rowValue'_succ_add
  - Building-block assembly (the winning approach)

Extracted from session log (inline python -c scripts).

Date: 2026-02-09
"""


def tri(n):
    return n * (n + 1) // 2


def rv_prime(b, z):
    """rowValue'(b, z) = Sum_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def N_poly(b, z):
    """The Mathematica/sympy polynomial N(b,z)"""
    return (-2 + 2 * b - 2 * b ** 2 + z - b * z - z ** 2 + b * z ** 2
            + b ** z * (2 + 2 * b ** 2 + z + z ** 2 - b * (2 + z + z ** 2)))


# ---- Category 1: N(b,z) polynomial verification ----
print("=" * 60)
print("Category 1: N(b,z) polynomial matches 2*(b-1)^2*rv'")
print("=" * 60)

passes = 0
for b in [3, 6, 10, 15, 21, 28]:
    for z in [1, 2, 3, 4, 5]:
        if tri(z) <= b:
            rv = rv_prime(b, z)
            lhs = 2 * (b - 1) ** 2 * rv
            rhs = N_poly(b, z)
            assert lhs == rhs, f"FAIL: b={b}, z={z}"
            passes += 1

print(f"  PASSED: {passes} cases")


# ---- Category 2: N(b,z) non-negativity for valid cases ----
print()
print("=" * 60)
print("Category 2: N(b,z) >= 0 for valid cases (tri(z) <= b)")
print("=" * 60)

negative_count = 0
for b in range(2, 50):
    for z in range(1, 20):
        if tri(z) <= b:
            n = N_poly(b, z)
            if n < 0:
                print(f"  NEGATIVE! b={b}, z={z}: N={n}")
                negative_count += 1

print(f"  {negative_count} negative values found in b=2..49, z=1..19")


# ---- Category 3: Divisibility 2*(b-1)^2 | N(b,z) ----
print()
print("=" * 60)
print("Category 3: 2*(b-1)^2 divides N(b,z) for valid cases")
print("=" * 60)

fails = 0
for b in range(2, 30):
    for z in range(1, 15):
        if tri(z) <= b:
            n = N_poly(b, z)
            d = 2 * (b - 1) ** 2
            if d > 0 and n % d != 0:
                print(f"  NOT DIVISIBLE! b={b}, z={z}: N={n}, 2*(b-1)^2={d}")
                fails += 1

print(f"  {fails} non-divisible cases found in b=2..29, z=1..14")


# ---- Category 4: Nat-safe additive form (sign separation) ----
print()
print("=" * 60)
print("Category 4: Nat-safe additive form (separated POS/NEG)")
print("  2*(b-1)^2*rv + 2 + 2b^2 + bz + z^2 + b^(z+1)*(2+z+z^2)")
print("  = 2b + z + bz^2 + b^z*(2+2b^2+z+z^2)")
print("=" * 60)

passes = 0
for b in range(2, 30):
    for z in range(1, 12):
        if tri(z) <= b:
            rv = rv_prime(b, z)
            lhs = (2 * (b - 1) ** 2 * rv + 2 + 2 * b ** 2 + b * z + z ** 2
                   + b ** (z + 1) * (2 + z + z ** 2))
            rhs = (2 * b + z + b * z ** 2
                   + b ** z * (2 + 2 * b ** 2 + z + z ** 2))
            assert lhs == rhs, f"FAIL b={b}, z={z}"
            passes += 1

print(f"  PASSED: {passes} cases")


# ---- Category 5: Building-block assembly derivation ----
print()
print("=" * 60)
print("Category 5: Building-block assembly (Approach D)")
print("  rv' = (b-tri(z))*G(z) + W_asc(z)")
print("  weighted_sum_closed: (b-1)^2*W_asc + (z-1)*(b-1) + b = b^z")
print("  geom identity: (b-1)*G + 1 = b^z")
print("=" * 60)

passes = 0
for b in range(2, 30):
    for z in range(1, 12):
        if tri(z) <= b:
            rv = rv_prime(b, z)
            G = sum(b ** i for i in range(z))
            W_asc = sum((z - 1 - i) * b ** i for i in range(z))

            # Check split
            assert rv == (b - tri(z)) * G + W_asc, f"Split FAIL b={b}, z={z}"

            # Using closed forms in integer arithmetic:
            # (b-1)^2*G + (b-1) = (b-1)*b^z  (multiply geom by (b-1))
            assert (b - 1) ** 2 * G + (b - 1) == (b - 1) * b ** z, f"Geom2 FAIL"

            # 2*(b-1)^2*rv' = 2*(b-tri(z))*(b-1)*(b^z - 1) + 2*b^z - 2*(z-1)*(b-1) - 2*b
            term1 = (2 * b - z ** 2 - z) * (b - 1) * (b ** z - 1)
            term2 = 2 * b ** z - 2 * (z - 1) * (b - 1) - 2 * b
            assert 2 * (b - 1) ** 2 * rv == term1 + term2, f"Derivation FAIL"
            passes += 1

print(f"  PASSED: {passes} cases")


# ---- Category 6: Winning Nat-safe form (halved, no factor 2) ----
print()
print("=" * 60)
print("Category 6: Final theorem form (halved)")
print("  (b-1)^2*rv + (b-tri z)*(b-1) + (z-1)*(b-1) + b")
print("  = (b-tri z)*(b-1)*b^z + b^z")
print("=" * 60)

passes = 0
for b in range(2, 30):
    for z in range(1, 12):
        if tri(z) <= b:
            rv = rv_prime(b, z)
            bt = b - tri(z)
            lhs = (b - 1) ** 2 * rv + bt * (b - 1) + (z - 1) * (b - 1) + b
            rhs = bt * (b - 1) * b ** z + b ** z
            assert lhs == rhs, f"FAIL b={b}, z={z}"
            passes += 1

print(f"  PASSED: {passes} cases")


# ---- Category 7: Concrete proof chain walkthrough (b=10, z=3) ----
print()
print("=" * 60)
print("Category 7: Step-by-step proof chain (b=10, z=3)")
print("=" * 60)

b, z = 10, 3
t = tri(z)  # 6
bt = b - t  # 4
G_desc = sum(b ** (z - 1 - i) for i in range(z))
W_desc = sum(i * b ** (z - 1 - i) for i in range(z))
G_asc = sum(b ** i for i in range(z))
W_asc = sum((z - 1 - i) * b ** i for i in range(z))
rv = bt * G_desc + W_desc

print(f"  1. rowValue'_split: rv'(10,3) = {bt}*{G_desc} + {W_desc} = {rv}")
print(f"  2. power_sum_reverse: G_desc={G_desc} = G_asc={G_asc}")
print(f"  3. weighted_power_sum_reverse: W_desc={W_desc} = W_asc={W_asc}")
print(f"  4. weighted_sum_closed: {(b-1)**2}*{W_asc} + {(z-1)*(b-1)} + {b} = {b**z}")
print(f"  5. geom identity: {b-1}*{G_asc} + 1 = {b**z}")
print(f"  6. multiply by (b-1): {(b-1)**2}*{G_asc} + {b-1} = {(b-1)*b**z}")
print(f"  7. Assembly: {(b-1)**2}*{rv} + {bt*(b-1)} + {(z-1)*(b-1)} + {b} = {bt*(b-1)*b**z} + {b**z}")
assert (b - 1) ** 2 * rv + bt * (b - 1) + (z - 1) * (b - 1) + b == bt * (b - 1) * b ** z + b ** z

print()
print("Summary: Direct assembly from 5 existing lemmas + 1 new flip lemma")
print("  rowValue'_split, power_sum_reverse, weighted_power_sum_reverse,")
print("  weighted_sum_closed, geom_sum_pred_mul_add_one")
print()
print("All categories passed.")
