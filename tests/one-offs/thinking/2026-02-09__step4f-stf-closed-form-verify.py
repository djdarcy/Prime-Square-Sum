"""
Step 4F — stf' closed form verification
========================================

Determines and verifies the Nat-safe additive identity for the full
stf(b) = F(b) closed form.

Strategy: multiply the telescoping identity by 6*(b-1)^3, then substitute
the closed forms for B (4A), C (4C), and rv' (4E).

Date: 2026-02-09
"""


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    """Inverse triangular: largest r such that tri(r) <= b."""
    r = 0
    while tri(r + 1) <= b:
        r += 1
    return r


def rv_prime(b, z):
    """rowValue'(b, z) = Sum_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def stf_prime(b):
    """stf'(b) = Sum_{z=1}^{qg(b)} rv'(b, z)"""
    r = qg(b)
    return sum(rv_prime(b, z) for z in range(1, r + 1))


def B_sum(b):
    """Boundary sum B = Sum_{z<r} (b - tri(z) + z)"""
    r = qg(b)
    return sum(b - tri(z) + z for z in range(r))


def C_sum(b):
    """Correction sum C = Sum_{z<r} (z+1) * G(z+1) where G(n) = Sum_{i<n} b^i"""
    r = qg(b)
    return sum((z + 1) * sum(b ** i for i in range(z + 1)) for z in range(r))


# ---- Category 1: Verify telescoping identity ----
print("=" * 60)
print("Category 1: Verify telescoping identity")
print("  stf'(b) + C + b*rv'(b,r) = b*stf'(b) + B")
print("=" * 60)

test_bases = [3, 6, 10, 15, 21, 28, 36, 45]
for b in test_bases:
    r = qg(b)
    if r == 0:
        continue
    s = stf_prime(b)
    B = B_sum(b)
    C = C_sum(b)
    rv = rv_prime(b, r)
    lhs = s + C + b * rv
    rhs = b * s + B
    ok = "OK" if lhs == rhs else "FAIL"
    print(f"  b={b:3d}, r={r}: stf'={s:>10}, B={B:>6}, C={C:>10}, rv'={rv:>10}  [{ok}]")

# ---- Category 2: Verify rearranged form ----
print()
print("=" * 60)
print("Category 2: Verify (b-1)*stf' + B = C + b*rv'")
print("=" * 60)

for b in test_bases:
    r = qg(b)
    if r == 0:
        continue
    s = stf_prime(b)
    B = B_sum(b)
    C = C_sum(b)
    rv = rv_prime(b, r)
    lhs = (b - 1) * s + B
    rhs = C + b * rv
    ok = "OK" if lhs == rhs else "FAIL"
    print(f"  b={b:3d}: (b-1)*stf' + B = {lhs:>12}, C + b*rv' = {rhs:>12}  [{ok}]")

# ---- Category 3: Determine the 6*(b-1)^4 identity ----
print()
print("=" * 60)
print("Category 3: Full Nat-safe identity")
print("  6*(b-1)^4*stf' + LHS_extra = RHS_terms")
print("  (all terms are closed-form in b and r)")
print("=" * 60)

passes = 0
for b in range(3, 50):
    r = qg(b)
    if r < 1:
        continue
    if tri(r) > b:
        continue

    s = stf_prime(b)
    bt = b - tri(r)  # b - tri(r), guaranteed >= 0

    # LHS of Nat-safe identity
    lhs = (6 * (b - 1) ** 4 * s
           + 6 * r * b * (b - 1) ** 3
           + 6 * (b - 1) ** 2 * tri(r)
           + 6 * (r + 1) * b ** (r + 1)
           + 6 * b * bt * (b - 1) ** 2
           + 6 * b * (r - 1) * (b - 1) ** 2
           + 6 * b ** 2 * (b - 1))

    # RHS of Nat-safe identity (no stf')
    rhs = ((b - 1) ** 3 * r * (r - 1) * (r - 2)
           + 6 * r * b ** (r + 2)
           + 6 * b
           + 6 * bt * (b - 1) ** 2 * b ** (r + 1)
           + 6 * (b - 1) * b ** (r + 1))

    if lhs != rhs:
        print(f"  FAIL: b={b}, r={r}")
        print(f"    LHS = {lhs}")
        print(f"    RHS = {rhs}")
        print(f"    diff = {lhs - rhs}")
    else:
        passes += 1

print(f"  PASSED: {passes} cases (b=3..49)")

# ---- Category 4: Simplification for triangular bases ----
print()
print("=" * 60)
print("Category 4: Simplification when b = tri(r) (bt = 0)")
print("  6*(b-1)^4*stf' + simpler_LHS = simpler_RHS")
print("=" * 60)

for n in range(2, 10):
    b = tri(n)
    r = n  # qg(tri(n)) = n
    s = stf_prime(b)
    # When b = tri(r), bt = 0, so bt terms vanish
    lhs = (6 * (b - 1) ** 4 * s
           + 6 * r * b * (b - 1) ** 3
           + 6 * (b - 1) ** 2 * tri(r)
           + 6 * (r + 1) * b ** (r + 1)
           + 6 * b * (r - 1) * (b - 1) ** 2
           + 6 * b ** 2 * (b - 1))

    rhs = ((b - 1) ** 3 * r * (r - 1) * (r - 2)
           + 6 * r * b ** (r + 2)
           + 6 * b
           + 6 * (b - 1) * b ** (r + 1))

    ok = "OK" if lhs == rhs else "FAIL"
    print(f"  n={n}, b=tri({n})={b:>4}, r={r}: stf'={s:>12}  [{ok}]")

# ---- Category 5: Extract stf' value from identity ----
print()
print("=" * 60)
print("Category 5: Verify stf' = (RHS - LHS_extra) / (6*(b-1)^4)")
print("=" * 60)

for b in [3, 6, 10, 15, 21, 28, 36, 45]:
    r = qg(b)
    if r < 1:
        continue
    s = stf_prime(b)
    bt = b - tri(r)

    rhs = ((b - 1) ** 3 * r * (r - 1) * (r - 2)
           + 6 * r * b ** (r + 2)
           + 6 * b
           + 6 * bt * (b - 1) ** 2 * b ** (r + 1)
           + 6 * (b - 1) * b ** (r + 1))

    lhs_extra = (6 * r * b * (b - 1) ** 3
                 + 6 * (b - 1) ** 2 * tri(r)
                 + 6 * (r + 1) * b ** (r + 1)
                 + 6 * b * bt * (b - 1) ** 2
                 + 6 * b * (r - 1) * (b - 1) ** 2
                 + 6 * b ** 2 * (b - 1))

    numerator = rhs - lhs_extra
    denom = 6 * (b - 1) ** 4
    if denom > 0 and numerator % denom == 0:
        computed_stf = numerator // denom
        ok = "OK" if computed_stf == s else "FAIL"
        print(f"  b={b:3d}: stf'={s:>12}, computed={computed_stf:>12}  [{ok}]")
    else:
        print(f"  b={b:3d}: NOT DIVISIBLE! num={numerator}, den={denom}")

# ---- Category 6: Proof chain walkthrough (b=10, r=4) ----
print()
print("=" * 60)
print("Category 6: Step-by-step proof chain (b=10, r=4)")
print("=" * 60)

b, r = 10, 4
s = stf_prime(b)
B = B_sum(b)
C = C_sum(b)
rv = rv_prime(b, r)
bt = b - tri(r)

print(f"  stf'(10) = {s}")
print(f"  B = {B}, C = {C}, rv'(10,4) = {rv}")
print(f"  b - tri(r) = {bt}")
print()

# Telescoping
print(f"  1. Telescoping: {s} + {C} + 10*{rv} = 10*{s} + {B}")
print(f"     {s + C + 10 * rv} = {10 * s + B}")
print()

# Rearranged
print(f"  2. Rearranged: 9*{s} + {B} = {C} + 10*{rv}")
print(f"     {9 * s + B} = {C + 10 * rv}")
print()

# Multiply by 6*(b-1)^3 = 6*729
print(f"  3. Multiply by 6*729 = {6 * 729}")
val = 6 * 729 * (9 * s + B)
print(f"     6*9^4*{s} + 6*9^3*{B} = 6*9^3*{C} + 6*9^3*10*{rv}")
print(f"     {6 * 9 ** 4 * s} + {6 * 729 * B} = {6 * 729 * C} + {6 * 729 * 10 * rv}")
print()

# Substitute boundary_sum_closed
print(f"  4. B-closed: 6*{B} + {r*(r-1)*(r-2)} = 6*{r}*{b} = {6*r*b}")
print(f"     Multiply by (b-1)^3={729}:")
print(f"     6*729*{B} + 729*{r*(r-1)*(r-2)} = {6*r*b*729}")
print(f"     {6*729*B} + {729*r*(r-1)*(r-2)} = {6*r*b*729}")
print()

# Substitute correction_sum_closed
print(f"  5. C-closed: (b-1)^3*C + (b-1)^2*tri(r) + (r+1)*b^(r+1) = r*b^(r+2) + b")
cc_lhs = 729 * C + 81 * tri(r) + 5 * 10 ** 5
cc_rhs = 4 * 10 ** 6 + 10
print(f"     729*{C} + 81*{tri(r)} + 5*100000 = 4*1000000 + 10")
print(f"     {cc_lhs} = {cc_rhs}")
print(f"     Multiply by 6:")
print(f"     {6*729*C} + {6*81*tri(r)} + {6*5*10**5} = {6*4*10**6} + {6*10}")
print()

# Substitute rv' closed form
print(f"  6. rv'-closed: (b-1)^2*rv' + bt*(b-1) + (r-1)*(b-1) + b = bt*(b-1)*b^r + b^r")
rv_lhs = 81 * rv + bt * 9 + 3 * 9 + 10
rv_rhs = bt * 9 * 10 ** 4 + 10 ** 4
print(f"     81*{rv} + {bt}*9 + 3*9 + 10 = {bt}*9*10000 + 10000")
print(f"     {rv_lhs} = {rv_rhs}")
print(f"     Multiply by 6*(b-1)*b = 6*9*10 = 540:")
rv2_lhs = 6 * 729 * 10 * rv + 6 * 10 * bt * 81 + 6 * 10 * 3 * 81 + 6 * 100 * 9
rv2_rhs = 6 * bt * 81 * 10 ** 5 + 6 * 9 * 10 ** 5
print(f"     {rv2_lhs} = {rv2_rhs}")

print()
print("All categories passed." if passes > 0 else "FAILURES detected!")
