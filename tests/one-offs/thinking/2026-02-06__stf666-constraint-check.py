"""
Check if stf(666) satisfies the new structural constraints:
1. r = qg(666) must be a perfect square for stf(666) to be divisible by 6
2. If stf(666) = primesum(n,2), then n must be 1 (mod 6)

Also verify: is stf(666) actually divisible by 6?
"""
from math import isqrt

# stf(666) = known 98-digit value
stf_666 = 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290

# 1. What is r = qg(666)?
# tri(r) = r*(r+1)/2 = 666
# r^2 + r - 1332 = 0
# r = (-1 + sqrt(1 + 4*1332)) / 2 = (-1 + sqrt(5329)) / 2
disc = 1 + 8 * 666
sqrt_disc = isqrt(disc)
print(f'=== qg(666) calculation ===')
print(f'  1 + 8*666 = {disc}')
print(f'  sqrt({disc}) = {sqrt_disc}')
print(f'  Is perfect square? {sqrt_disc**2 == disc}')
r = (sqrt_disc - 1) // 2
print(f'  r = qg(666) = {r}')
print(f'  tri({r}) = {r*(r+1)//2}')
print(f'  Is r a perfect square? {isqrt(r)**2 == r}')
if isqrt(r)**2 == r:
    k = isqrt(r)
    print(f'  r = {k}^2 = {k**2}')

print()

# 2. Is stf(666) divisible by 6?
print(f'=== stf(666) divisibility ===')
print(f'  stf(666) mod 2 = {stf_666 % 2}')
print(f'  stf(666) mod 3 = {stf_666 % 3}')
print(f'  stf(666) mod 6 = {stf_666 % 6}')
div6 = stf_666 % 6 == 0
print(f'  Divisible by 6? {div6}')

if div6:
    quotient = stf_666 // 6
    print(f'  stf(666) / 6 = {quotient}')
    print(f'  Number of digits in quotient: {len(str(quotient))}')

print()

# 3. What does this mean for primesum(n,2) = stf(666)?
print(f'=== Constraint check for stf(666) = primesum(n,2) ===')
print(f'  stf side: r = {r} = {isqrt(r)}^2 (perfect square) -> stf-k^2 conjecture APPLIES')
print(f'  stf(666) mod 6 = {stf_666 % 6}')
if div6:
    print(f'  CONSISTENT: stf(666) is divisible by 6, as predicted by stf-k^2')
    print(f'  primesum side: for primesum(n,2) = stf(666), need n = 1 (mod 6)')
    print(f'  This means n must be in {{7, 13, 19, 25, 31, 37, 43, ...}}')
    print(f'  This DOES NOT rule out stf(666) = primesum(n,2)')
    print(f'  It tells us: if a match exists, n = 1 (mod 6)')
else:
    print(f'  INCONSISTENT: stf(666) NOT divisible by 6 despite r being perfect square')
    print(f'  This would DISPROVE the stf-k^2 conjecture!')

print()

# 4. Can we determine more about n?
# primesum(n,2) ~ n * p_n^2 / 3 for large n (by prime number theorem)
# p_n ~ n * ln(n), so primesum(n,2) ~ n^3 * ln(n)^2 / 3
# stf(666) ~ 3.7 * 10^97
# Need n^3 * ln(n)^2 / 3 ~ 3.7 * 10^97
import math
print(f'=== Rough estimate of n for primesum(n,2) = stf(666) ===')
target = float(stf_666)
# Approximate: sum of p^2 for first n primes ~ n^3 * (ln n)^2 / 3
# Solving for n: n ~ (3*target)^(1/3) / ln(n)
# Iterate
n_est = int((3 * target) ** (1/3))
for _ in range(20):
    if n_est > 1:
        n_est = int((3 * target / math.log(n_est)**2) ** (1/3))
print(f'  Rough estimate: n ~ {n_est}')
print(f'  n mod 6 = {n_est % 6}')
print(f'  Nearest n = 1 (mod 6): {n_est - (n_est % 6) + 1} or {n_est - (n_est % 6) + 7}')

# The 6k±1 connection
print()
print(f'=== The 6k+-1 connection ===')
print(f'  All primes p > 3 satisfy p = 6k +/- 1 for some integer k.')
print(f'  Therefore p^2 = (6k +/- 1)^2 = 36k^2 +/- 12k + 1')
print(f'  p^2 mod 6 = (36k^2 +/- 12k + 1) mod 6 = 1')
print(f'  This is EXACTLY why primesum(n,2) mod 6 = (n+5) mod 6.')
print(f'  The primesum mod 6 result IS the 6k+-1 property of primes, applied to squares.')
print(f'  It is a well-known consequence, not a new discovery.')
print(f'  However, stating it as primesum(n,2) = (n+5) mod 6 is a clean formulation')
print(f'  that could be proved in Lean as a useful lemma.')
