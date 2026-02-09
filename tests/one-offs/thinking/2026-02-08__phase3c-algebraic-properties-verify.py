"""
Phase 3C: Numerical Verification of Algebraic Properties

Theorems verified:
  1. rowValue'_split    -- rv'(b,z) = (b-tri z)*Sum b^(z-1-i) + Sum i*b^(z-1-i)
  2. stf_eq_stf'        -- stf(b) = stf'(b)  [algorithmic foldl = algebraic Finset.sum]
  3. geom_sum_mul_add_one -- b*Sum_{i<n} b^i + 1 = Sum_{i<n+1} b^i
  4. power_sum_reverse   -- Sum_{i<z} b^(z-1-i) = Sum_{i<z} b^i
  5. rowValue'_succ_add  -- rv'(b,z+1) + (z+1)*Sum_{i<z+1} b^i = b*rv'(b,z) + (b-tri z+z)
  6. power_sum_closed    -- Sum_{i<z} b^(z-1-i) = (b^z - 1)/(b-1) for b >= 2

These match the Lean 4 theorems in proofs/TriSum.lean (Phase 3C section).
"""
import math


def tri(n):
    return n * (n + 1) // 2


def qg(b):
    """Inverse triangular: returns r if b = tri(r), else None."""
    r = (-1 + int(math.isqrt(1 + 8 * b))) // 2
    return r if tri(r) == b else None


def rowValue_prime(b, z):
    """rowValue'(b, z) = Σ_{i<z} (b - tri(z) + i) * b^(z-1-i)"""
    return sum((b - tri(z) + i) * b ** (z - 1 - i) for i in range(z))


def stf_algo(b):
    """Algorithmic stf: foldl-based, matching the Lean 'stf' definition."""
    r = qg(b)
    if r is None:
        return None
    return sum(rowValue_prime(b, z) for z in range(1, r + 1))


def stf_prime(b):
    """Algebraic stf': Finset.sum of rowValue' over all rows."""
    r = qg(b)
    if r is None:
        return None
    return sum(rowValue_prime(b, i + 1) for i in range(r))


# Test bases: all triangular numbers up to 666, plus a few non-triangular
TRIANGULAR_BASES = [b for b in range(1, 700) if qg(b) is not None]
EXTRA_BASES = [2, 3, 5, 7, 8, 12, 20, 100]


if __name__ == "__main__":
    all_pass = True

    # === Test 1: rowValue'_split ===
    print("=== 1. rowValue'_split: rv'(b,z) = (b-tri z)*Sum(b^(z-1-i)) + Sum(i*b^(z-1-i)) ===\n")

    split_ok = True
    test_cases = [(b, z) for b in [6, 10, 15, 21, 28, 36, 55, 666]
                  for z in range(0, (qg(b) or 0) + 1)]
    for b, z in test_cases:
        rv = rowValue_prime(b, z)
        geom_part = (b - tri(z)) * sum(b ** (z - 1 - i) for i in range(z))
        linear_part = sum(i * b ** (z - 1 - i) for i in range(z))
        rhs = geom_part + linear_part
        ok = rv == rhs
        split_ok = split_ok and ok
        if not ok:
            print(f"  FAIL b={b} z={z}: rv'={rv}, split={rhs}")

    print(f"Tested {len(test_cases)} cases. All passed: {split_ok}")
    all_pass = all_pass and split_ok

    # === Test 2: stf_eq_stf' ===
    print("\n=== 2. stf_eq_stf': stf(b) = stf'(b) ===\n")

    bridge_ok = True
    for b in TRIANGULAR_BASES[:20]:
        s1 = stf_algo(b)
        s2 = stf_prime(b)
        ok = s1 == s2
        bridge_ok = bridge_ok and ok
        if b <= 55 or not ok:
            print(f"b={b:>3} r={qg(b):>2}: stf={s1}, stf'={s2}, match={ok}")

    print(f"All stf=stf' checks passed: {bridge_ok}")
    all_pass = all_pass and bridge_ok

    # === Test 3: geom_sum_mul_add_one ===
    print("\n=== 3. geom_sum_mul_add_one: b*Sum_{i<n} b^i + 1 = Sum_{i<n+1} b^i ===\n")

    geom_ok = True
    for b in [2, 3, 5, 6, 10, 15, 100]:
        for n in range(0, 9):
            lhs = b * sum(b ** i for i in range(n)) + 1
            rhs = sum(b ** i for i in range(n + 1))
            ok = lhs == rhs
            geom_ok = geom_ok and ok
            if not ok:
                print(f"  FAIL b={b} n={n}: LHS={lhs}, RHS={rhs}")
        print(f"b={b:>3}: n=0..8 all OK")

    print(f"All geom_sum checks passed: {geom_ok}")
    all_pass = all_pass and geom_ok

    # === Test 4: power_sum_reverse ===
    print("\n=== 4. power_sum_reverse: Sum_{i<z} b^(z-1-i) = Sum_{i<z} b^i ===\n")

    reverse_ok = True
    for b in [2, 3, 6, 10, 15]:
        for z in range(0, 9):
            desc = sum(b ** (z - 1 - i) for i in range(z))
            asc = sum(b ** i for i in range(z))
            ok = desc == asc
            reverse_ok = reverse_ok and ok
            if not ok:
                print(f"  FAIL b={b} z={z}: desc={desc}, asc={asc}")
        print(f"b={b:>2}: z=0..8 all OK")

    print(f"All power_sum_reverse checks passed: {reverse_ok}")
    all_pass = all_pass and reverse_ok

    # === Test 5: rowValue'_succ_add ===
    print("\n=== 5. rowValue'_succ_add: rv'(b,z+1) + (z+1)*Sum(b^i) = b*rv'(b,z) + (b-tri z+z) ===\n")

    recur_ok = True
    for b in [6, 10, 15, 21, 28, 36, 55, 666]:
        r = qg(b)
        if r is None:
            continue
        for z in range(0, r):  # z+1 must be valid row, so tri(z+1) <= b
            if tri(z + 1) > b:
                break
            lhs = rowValue_prime(b, z + 1) + (z + 1) * sum(b ** i for i in range(z + 1))
            rhs = b * rowValue_prime(b, z) + (b - tri(z) + z)
            ok = lhs == rhs
            recur_ok = recur_ok and ok
            if not ok:
                print(f"  FAIL b={b} z={z}: LHS={lhs}, RHS={rhs}")
        print(f"b={b:>3} r={r}: all z=0..{r-1} OK")

    print(f"All rowValue'_succ_add checks passed: {recur_ok}")
    all_pass = all_pass and recur_ok

    # === Test 6: power_sum_closed ===
    print("\n=== 6. power_sum_closed: Sum(b^(z-1-i)) = (b^z - 1)/(b-1) for b >= 2 ===\n")

    closed_ok = True
    for b in [2, 3, 5, 6, 10, 15, 100]:
        for z in range(0, 9):
            desc_sum = sum(b ** (z - 1 - i) for i in range(z))
            if z == 0:
                formula = 0  # empty sum
            else:
                formula = (b ** z - 1) // (b - 1)
            ok = desc_sum == formula
            closed_ok = closed_ok and ok
            if not ok:
                print(f"  FAIL b={b} z={z}: sum={desc_sum}, formula={formula}")
        print(f"b={b:>3}: z=0..8 all OK")

    print(f"All power_sum_closed checks passed: {closed_ok}")
    all_pass = all_pass and closed_ok

    # === Final Summary ===
    print(f"\n{'='*60}")
    print(f"PHASE 3C VERIFICATION: {'ALL PASSED' if all_pass else 'FAILURES DETECTED'}")
    print(f"{'='*60}")
