/-
  Core.lean — The connecting theorems tying stf to primesum

  Imports all modules and proves the core identity:
    stf(10) = primesum(7, 2) = 666

  Also proves:
  - stf(10) is triangular (666 = tri(36))
  - The full chain: tri(4) = 10, stf(10) = 666, 666 = tri(36)
  - 10 = primesum(3, 1) — the input itself is a prime sum
-/
import TriSum
import Primes
import PrimesumMod6

-- ============================================================
-- The Core Identity
-- ============================================================

-- stf(10) = primesum([2,3,5,7,11,13,17], 2)
theorem stf_eq_primesum_7_2 :
    stf 10 = primesum firstSevenPrimes 2 := by native_decide

-- ============================================================
-- Triangular connections
-- ============================================================

-- stf(10) is a triangular number
theorem stf_ten_is_triangular : isTriangular (stf 10) = true := by native_decide

-- 10 = primesum(3, 1) — the input base is itself a prime sum
theorem ten_eq_primesum_3_1 : 10 = primesum firstThreePrimes 1 := by native_decide

-- ============================================================
-- The full chain
-- ============================================================

-- tri(4) = 10 ∧ stf(10) = 666 ∧ 666 = tri(36)
theorem chain_tri4_to_tri36 :
    tri 4 = 10 ∧ stf 10 = 666 ∧ 666 = tri 36 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

-- The complete pattern in one theorem:
-- tri(4) is a prime sum, stf of that prime sum is another prime sum,
-- and that result is also triangular
theorem core_pattern :
    tri 4 = primesum firstThreePrimes 1 ∧
    stf (tri 4) = primesum firstSevenPrimes 2 ∧
    isTriangular (stf (tri 4)) = true := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩
