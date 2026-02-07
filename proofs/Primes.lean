/-
  Primes.lean — Prime sum definitions and verification

  Defines:
  - firstSevenPrimes: [2, 3, 5, 7, 11, 13, 17]
  - primesum: sum of p^power for primes in a list

  Key results:
  - All entries in firstSevenPrimes are prime
  - primesum(7, 2) = 666
  - primesum(3, 1) = 10
-/
import Mathlib.Data.Nat.Prime.Defs

-- The first 7 primes
def firstSevenPrimes : List Nat := [2, 3, 5, 7, 11, 13, 17]

-- The first 3 primes
def firstThreePrimes : List Nat := [2, 3, 5]

-- Sum of p^power for each prime p in the list
def primesum (primes : List Nat) (power : Nat) : Nat :=
  primes.foldl (fun acc p => acc + p ^ power) 0

-- ============================================================
-- Primality verification
-- ============================================================

-- Individual primality proofs
theorem prime_2 : Nat.Prime 2 := by native_decide
theorem prime_3 : Nat.Prime 3 := by native_decide
theorem prime_5 : Nat.Prime 5 := by native_decide
theorem prime_7 : Nat.Prime 7 := by native_decide
theorem prime_11 : Nat.Prime 11 := by native_decide
theorem prime_13 : Nat.Prime 13 := by native_decide
theorem prime_17 : Nat.Prime 17 := by native_decide

-- ============================================================
-- Primesum computations
-- ============================================================

-- 2^2 + 3^2 + 5^2 + 7^2 + 11^2 + 13^2 + 17^2 = 666
theorem primesum_7_2 : primesum firstSevenPrimes 2 = 666 := by native_decide

-- 2 + 3 + 5 = 10
theorem primesum_3_1 : primesum firstThreePrimes 1 = 10 := by native_decide
