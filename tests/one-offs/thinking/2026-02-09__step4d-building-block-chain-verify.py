"""
Step 4D — Building block derivation chain verification
=======================================================

Verifies that the Lean proof building blocks (hsplit, hfactor, hkey, hag, hgeom)
combine correctly for the weighted_sum_closed theorem.

Extracted from session log (inline python -c scripts).

Date: 2026-02-09
"""


def tri(n):
    return n * (n + 1) // 2


# ---- Category 1: Native decide verification values ----
print("=" * 60)
print("Category 1: weighted_sum_closed concrete values")
print("  (b-1)^2 * Sum_{i<r}(r-1-i)*b^i + (r-1)*(b-1) + b = b^r")
print("=" * 60)

test_cases = [(10, 4), (6, 3), (15, 5), (1, 1), (1, 5)]
for b, r in test_cases:
    W = sum((r - 1 - i) * b ** i for i in range(r))
    lhs = (b - 1) ** 2 * W + (r - 1) * (b - 1) + b
    rhs = b ** r
    print(f"  b={b:2d}, r={r}: W={W:>8}, LHS={lhs:>10}, RHS={rhs:>10}, match={lhs == rhs}")


# ---- Category 2: Building block chain for b=10, r=4 ----
print()
print("=" * 60)
print("Category 2: Building block chain (b=10, r=4)")
print("=" * 60)

b, r = 10, 4
W = sum((r - 1 - i) * b ** i for i in range(r))
AG = sum(i * b ** i for i in range(r))
G = sum(b ** i for i in range(r))

print(f"  b={b}, r={r}")
print(f"  W  = Sum (r-1-i)*b^i = {W}")
print(f"  AG = Sum i*b^i       = {AG}")
print(f"  G  = Sum b^i         = {G}")
print()

# hsplit: W + AG = (r-1)*G
print(f"  hsplit: W + AG = {W + AG}, (r-1)*G = {(r - 1) * G}, match={W + AG == (r - 1) * G}")

# hsplit2: (b-1)^2*W + (b-1)^2*AG = (r-1)*(b-1)^2*G
lhs2 = (b - 1) ** 2 * W + (b - 1) ** 2 * AG
rhs2 = (r - 1) * ((b - 1) ** 2 * G)
print(f"  hsplit2: (b-1)^2*W + (b-1)^2*AG = {lhs2}, (r-1)*(b-1)^2*G = {rhs2}, match={lhs2 == rhs2}")

# hfactor: (r-1)*(b-1)^2*G + (r-1)*(b-1) = (r-1)*(b-1)*b^r
lhs3 = (r - 1) * ((b - 1) ** 2 * G) + (r - 1) * (b - 1)
rhs3 = (r - 1) * (b - 1) * b ** r
print(f"  hfactor: {lhs3} = {rhs3}, match={lhs3 == rhs3}")

# hkey: (r-1)*(b-1)*b^r + r*b^r = b^r + (r-1)*b^(r+1)
lhs4 = (r - 1) * (b - 1) * b ** r + r * b ** r
rhs4 = b ** r + (r - 1) * b ** (r + 1)
print(f"  hkey: {lhs4} = {rhs4}, match={lhs4 == rhs4}")

# hag (arith_geom_sum): (b-1)^2*AG + r*b^r = (r-1)*b^(r+1) + b
lhs_ag = (b - 1) ** 2 * AG + r * b ** r
rhs_ag = (r - 1) * b ** (r + 1) + b
print(f"  hag: {lhs_ag} = {rhs_ag}, match={lhs_ag == rhs_ag}")

# hgeom (geom_sum_pred_mul_add_one): (b-1)*G + 1 = b^r
lhs_g = (b - 1) * G + 1
rhs_g = b ** r
print(f"  hgeom: {lhs_g} = {rhs_g}, match={lhs_g == rhs_g}")

print()
print("omega combination trace:")
print("  From hsplit2: (b-1)^2*W = (r-1)*(b-1)^2*G - (b-1)^2*AG")
print("  From hfactor: (r-1)*(b-1)^2*G = (r-1)*(b-1)*b^r - (r-1)*(b-1)")
print("  Substituting: (b-1)^2*W = (r-1)*(b-1)*b^r - (r-1)*(b-1) - (b-1)^2*AG")
print("  From hag: (b-1)^2*AG = (r-1)*b^(r+1) + b - r*b^r")
print("  Goal: (b-1)^2*W + (r-1)*(b-1) + b = b^r")


# ---- Category 3: Broad test ----
print()
print("=" * 60)
print("Category 3: Broad verification across bases")
print("=" * 60)

passes = 0
for b in range(1, 30):
    for r in range(1, 12):
        W = sum((r - 1 - i) * b ** i for i in range(r))
        AG = sum(i * b ** i for i in range(r))
        G = sum(b ** i for i in range(r))
        assert W + AG == (r - 1) * G, f"hsplit FAIL: b={b}, r={r}"
        assert (b - 1) ** 2 * W + (r - 1) * (b - 1) + b == b ** r, f"closed FAIL: b={b}, r={r}"
        passes += 1

print(f"  PASSED: {passes} cases (b=1..29, r=1..11)")
print()
print("All categories passed.")
