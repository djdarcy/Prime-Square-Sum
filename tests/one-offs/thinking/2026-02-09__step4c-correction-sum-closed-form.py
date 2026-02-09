"""
Step 4C: Correction Sum C(b, r) - Closed Form Verification
===========================================================

Verifies the algebra for the correction sum that appears in the
telescoping proof of stf(b) = primesum(r, 2).

Definitions:
  G(n) = Sum_{i=0}^{n-1} b^i = (b^n - 1)/(b-1)
  C(b, r) = Sum_{z=0}^{r-1} (z+1) * G(z+1)
  tri(r) = r*(r+1)/2

Key identities verified:
  1. C expanded via geometric sum
  2. (b-1)*C = Sum_{j=1}^{r} j*b^j - tri(r)
  3. Arith-geom sum: (b-1)^2 * Sum_{i<n} i*b^i + n*b^n = (n-1)*b^(n+1) + b
  4. Nat-safe additive form:
     (b-1)^3 * C + (b-1)^2 * tri(r) + (r+1)*b^(r+1) = r*b^(r+2) + b

Test bases: b=6(r=3), b=10(r=4), b=15(r=5), b=21(r=6)
"""

from fractions import Fraction
import sys


def tri(r):
    """Triangular number: r*(r+1)/2"""
    return r * (r + 1) // 2


def G(n, b):
    """Geometric sum: Sum_{i=0}^{n-1} b^i  [direct summation]"""
    return sum(b**i for i in range(n))


def G_closed(n, b):
    """Geometric sum via closed form (using Fraction for exactness)"""
    if b == 1:
        return n
    return Fraction(b**n - 1, b - 1)


def C_direct(b, r):
    """C(b, r) = Sum_{z=0}^{r-1} (z+1) * G(z+1)  [direct summation]"""
    return sum((z + 1) * G(z + 1, b) for z in range(r))


def C_via_geometric(b, r):
    """C expanded using geometric sum formula:
    C = Sum_{z=0}^{r-1} (z+1) * (b^(z+1) - 1) / (b-1)
    """
    return sum(Fraction((z + 1) * (b**(z + 1) - 1), b - 1) for z in range(r))


def arith_geom_sum_direct(n, b):
    """Sum_{i=0}^{n-1} i * b^i  [direct summation]"""
    return sum(i * b**i for i in range(n))


def arith_geom_sum_rhs(n, b):
    """From the identity: (b-1)^2 * Sum_{i<n} i*b^i + n*b^n = (n-1)*b^(n+1) + b
    So: Sum_{i<n} i*b^i = [(n-1)*b^(n+1) + b - n*b^n] / (b-1)^2
    """
    numerator = (n - 1) * b**(n + 1) + b - n * b**n
    return Fraction(numerator, (b - 1)**2)


def sum_j_bj(r, b):
    """Sum_{j=1}^{r} j * b^j = Sum_{j=0}^{r} j * b^j  (j=0 term is 0)
    This equals Sum_{i<r+1} i * b^i = arith_geom_sum with n=r+1
    """
    return sum(j * b**j for j in range(r + 1))


# ============================================================
# TEST CASES
# ============================================================

test_cases = [
    (6, 3),    # b=6, r=3: tri(6) = 21
    (10, 4),   # b=10, r=4: tri(10) = 55
    (15, 5),   # b=15, r=5: tri(15) = 120
    (21, 6),   # b=21, r=6: tri(21) = 231
    (3, 2),    # small case
    (28, 7),   # larger case
    (36, 8),   # even larger
]

all_pass = True
section_pass = True


def check(label, lhs, rhs):
    global all_pass, section_pass
    ok = (lhs == rhs)
    status = "PASS" if ok else "FAIL"
    if not ok:
        all_pass = False
        section_pass = False
    print(f"  [{status}] {label}")
    if not ok:
        print(f"         LHS = {lhs}")
        print(f"         RHS = {rhs}")
        print(f"         diff = {lhs - rhs}")
    return ok


print("=" * 72)
print("Step 4C: Correction Sum C(b, r) - Closed Form Verification")
print("=" * 72)

# ------------------------------------------------------------------
# Section 1: Basic definitions agree
# ------------------------------------------------------------------
print("\n--- Section 1: G(n) direct vs closed form ---")
section_pass = True
for b, r in test_cases:
    for n in range(1, r + 2):
        g_dir = G(n, b)
        g_cls = G_closed(n, b)
        if g_dir != g_cls:
            print(f"  [FAIL] G({n}, {b}): direct={g_dir}, closed={g_cls}")
            all_pass = False
            section_pass = False
if section_pass:
    print("  [PASS] All G(n, b) direct == closed form")

# ------------------------------------------------------------------
# Section 2: C direct == C via geometric sum expansion
# ------------------------------------------------------------------
print("\n--- Section 2: C(b,r) direct summation == geometric expansion ---")
section_pass = True
for b, r in test_cases:
    c_dir = C_direct(b, r)
    c_geo = C_via_geometric(b, r)
    check(f"C({b},{r}): direct={c_dir}, geometric={c_geo}", c_dir, c_geo)

# ------------------------------------------------------------------
# Section 3: Arith-geom sum identity
# ------------------------------------------------------------------
print("\n--- Section 3: Arith-geom sum identity verification ---")
section_pass = True
for b, r in test_cases:
    for n in range(1, r + 3):
        S = arith_geom_sum_direct(n, b)
        lhs = (b - 1)**2 * S + n * b**n
        rhs = (n - 1) * b**(n + 1) + b
        if lhs != rhs:
            check(f"arith_geom b={b}, n={n}", lhs, rhs)
if section_pass:
    print("  [PASS] All arith-geom sum identities hold")

print("\n--- Section 3b: Arith-geom closed form == direct ---")
section_pass = True
for b, r in test_cases:
    for n in range(1, r + 3):
        S_dir = arith_geom_sum_direct(n, b)
        S_cls = arith_geom_sum_rhs(n, b)
        if S_dir != S_cls:
            check(f"arith_geom_sum b={b}, n={n}", S_dir, S_cls)
if section_pass:
    print("  [PASS] All arith-geom closed forms match direct sums")


# ------------------------------------------------------------------
# Section 4: (b-1)*C = Sum_{j=1}^{r} j*b^j - tri(r)
# ------------------------------------------------------------------
print("\n--- Section 4: (b-1)*C = Sum_{j=1}^r j*b^j - tri(r) ---")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    lhs = (b - 1) * c
    S = sum_j_bj(r, b)
    rhs = S - tri(r)
    check(f"b={b}, r={r}: (b-1)*C={lhs}, Sum-tri={rhs}", lhs, rhs)

# ------------------------------------------------------------------
# Section 5: (b-1)^3*C = r*b^(r+2) + b - (r+1)*b^(r+1) - (b-1)^2*tri(r)
# ------------------------------------------------------------------
print("\n--- Section 5: (b-1)^3*C closed form ---")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    lhs = (b - 1)**3 * c
    rhs = r * b**(r + 2) + b - (r + 1) * b**(r + 1) - (b - 1)**2 * tri(r)
    check(f"b={b}, r={r}: (b-1)^3*C = {lhs}", lhs, rhs)

# ------------------------------------------------------------------
# Section 6: Nat-safe ADDITIVE form (no division!)
# ------------------------------------------------------------------
print("\n--- Section 6: Nat-safe additive form ---")
print("    (b-1)^3*C + (b-1)^2*tri(r) + (r+1)*b^(r+1) = r*b^(r+2) + b")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    lhs = (b - 1)**3 * c + (b - 1)**2 * tri(r) + (r + 1) * b**(r + 1)
    rhs = r * b**(r + 2) + b
    check(f"b={b}, r={r}: LHS={lhs}, RHS={rhs}", lhs, rhs)


# ------------------------------------------------------------------
# Section 7: Intermediate additive form
# ------------------------------------------------------------------
print("\n--- Section 7: Intermediate additive: (b-1)*C + tri(r) = Sum_{j<r+1} j*b^j ---")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    lhs = (b - 1) * c + tri(r)
    rhs = arith_geom_sum_direct(r + 1, b)
    check(f"b={b}, r={r}: (b-1)*C+tri(r)={lhs}, Sum={rhs}", lhs, rhs)

# ------------------------------------------------------------------
# Section 8: Chain the intermediate form through arith-geom
# ------------------------------------------------------------------
print("\n--- Section 8: Full chain: (b-1)^2*((b-1)*C + tri(r)) + (r+1)*b^(r+1) = r*b^(r+2) + b ---")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    inner = (b - 1) * c + tri(r)
    lhs = (b - 1)**2 * inner + (r + 1) * b**(r + 1)
    rhs = r * b**(r + 2) + b
    check(f"b={b}, r={r}: LHS={lhs}, RHS={rhs}", lhs, rhs)

print("\n    Expanding: (b-1)^2*((b-1)*C + tri(r)) = (b-1)^3*C + (b-1)^2*tri(r)")
print("    So Section 8 == Section 6. Both are the same Nat-safe additive identity.")


# ------------------------------------------------------------------
# Section 9: Show concrete values for documentation
# ------------------------------------------------------------------
print("\n--- Section 9: Concrete values for reference ---")
hdr = "  {:>4} {:>3} {:>12} {:>8} {:>14} {:>14}".format(
    "b", "r", "C(b,r)", "tri(r)", "(b-1)*C", "Sum j*b^j")
print(hdr)
print("  " + "-"*4 + " " + "-"*3 + " " + "-"*12 + " " + "-"*8 + " " + "-"*14 + " " + "-"*14)
for b, r in test_cases:
    c = C_direct(b, r)
    t = tri(r)
    bm1_c = (b - 1) * c
    S = sum_j_bj(r, b)
    print(f"  {b:4d} {r:3d} {c:12d} {t:8d} {bm1_c:14d} {S:14d}")

# ------------------------------------------------------------------
# Section 10: Verify all terms are natural numbers (Nat-safe)
# ------------------------------------------------------------------
print("\n--- Section 10: Nat-safety check (all terms >= 0) ---")
section_pass = True
for b, r in test_cases:
    c = C_direct(b, r)
    terms = {
        "(b-1)^3 * C": (b - 1)**3 * c,
        "(b-1)^2 * tri(r)": (b - 1)**2 * tri(r),
        "(r+1)*b^(r+1)": (r + 1) * b**(r + 1),
        "r*b^(r+2)": r * b**(r + 2),
        "b": b,
    }
    for name, val in terms.items():
        if val < 0:
            print(f"  [FAIL] b={b}, r={r}: {name} = {val} < 0!")
            all_pass = False
            section_pass = False
    lhs_keys = ["(b-1)^3 * C", "(b-1)^2 * tri(r)", "(r+1)*b^(r+1)"]
    lhs_sum = sum(terms[k] for k in lhs_keys)
    rhs_sum = terms["r*b^(r+2)"] + terms["b"]
    if lhs_sum != rhs_sum:
        print(f"  [FAIL] b={b}, r={r}: LHS={lhs_sum} != RHS={rhs_sum}")
        all_pass = False
        section_pass = False

if section_pass:
    print("  [PASS] All terms are non-negative and identity holds for all test cases")


# ------------------------------------------------------------------
# Section 11: Edge cases r=0 and r=1
# ------------------------------------------------------------------
print("\n--- Section 11: Edge cases ---")

# r=0: C(b, 0) = empty sum = 0
print("\n  r=0 edge cases:")
for b in [2, 3, 5, 10]:
    c = C_direct(b, 0)
    check(f"C({b}, 0) = 0 (empty sum)", c, 0)
    r = 0
    lhs = (b - 1)**3 * c + (b - 1)**2 * tri(r) + (r + 1) * b**(r + 1)
    rhs = r * b**(r + 2) + b
    check(f"  Nat-safe r=0, b={b}: {lhs} = {rhs}", lhs, rhs)

# r=1: C(b, 1) = 1*G(1) = 1*1 = 1
print("\n  r=1 edge cases:")
for b in [2, 3, 5, 10]:
    c = C_direct(b, 1)
    check(f"C({b}, 1) = 1 (single term: 1*G(1)=1*1)", c, 1)
    r = 1
    lhs = (b - 1)**3 * c + (b - 1)**2 * tri(r) + (r + 1) * b**(r + 1)
    rhs = r * b**(r + 2) + b
    check(f"  Nat-safe r=1, b={b}: {lhs} = {rhs}", lhs, rhs)


# ------------------------------------------------------------------
# Summary
# ------------------------------------------------------------------
print("\n" + "=" * 72)
if all_pass:
    print("ALL CHECKS PASSED")
    print()
    print("Summary of verified identities:")
    print("  1. G(n, b) direct == closed form")
    print("  2. C(b, r) direct == geometric expansion")
    print("  3. Arith-geom: (b-1)^2 * Sum_{i<n} i*b^i + n*b^n = (n-1)*b^(n+1) + b")
    print("  4. (b-1)*C = Sum_{j=1}^r j*b^j - tri(r)")
    print("  5. (b-1)^3*C = r*b^(r+2) + b - (r+1)*b^(r+1) - (b-1)^2*tri(r)")
    print("  6. NAT-SAFE: (b-1)^3*C + (b-1)^2*tri(r) + (r+1)*b^(r+1) = r*b^(r+2) + b")
    print("  7. INTERMEDIATE: (b-1)*C + tri(r) = Sum_{j<r+1} j*b^j")
    print("  8. FULL CHAIN: Section 8 == Section 6 (algebraic equivalence)")
    print("  9. All terms are natural numbers (Nat-safe)")
    print(" 10. Edge cases r=0 and r=1 verified")
    print()
    print("The Nat-safe additive identity for C is:")
    print("  (b-1)^3 * C + (b-1)^2 * tri(r) + (r+1)*b^(r+1) = r*b^(r+2) + b")
    print()
    print("This avoids ALL division. Every term is a natural number.")
    print("Suitable for Lean 4 Nat arithmetic proofs.")
else:
    print("SOME CHECKS FAILED - review output above")
    sys.exit(1)
