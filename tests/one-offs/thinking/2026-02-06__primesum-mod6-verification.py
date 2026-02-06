"""
Verify Gemini's claim: primesum(n,2) mod 6 = (n+5) mod 6 for n >= 3.
Therefore primesum(n,2) divisible by 6 iff n = 1 (mod 6).

Also: p^2 mod 6 for all primes p > 3 should be 1.
"""
from math import isqrt


def sieve(limit):
    s = [True] * (limit + 1)
    s[0] = s[1] = False
    for i in range(2, isqrt(limit) + 1):
        if s[i]:
            for j in range(i*i, limit + 1, i):
                s[j] = False
    return [i for i in range(2, limit + 1) if s[i]]


primes = sieve(500)

# Verify: p^2 mod 6 for primes
print('=== p^2 mod 6 for primes ===')
for p in primes[:20]:
    print(f'  p={p:>3}: p^2={p**2:>6}, p^2 mod 6 = {p**2 % 6}')

print()
print('=== primesum(n, 2) mod 6 ===')
running_sum = 0
for i, p in enumerate(primes[:30], 1):
    running_sum += p ** 2
    predicted = (i + 5) % 6 if i >= 3 else '(formula for n>=3)'
    match = running_sum % 6 == predicted if i >= 3 else 'N/A'
    div6 = running_sum % 6 == 0
    n_mod6 = i % 6
    print(f'  n={i:>2}: primesum={running_sum:>10}, mod6={running_sum%6}, '
          f'predicted={(i+5)%6 if i>=3 else "N/A":>3}, '
          f'match={str(match):>5}, n%6={n_mod6}, div6={div6}')

print()
print('=== n where primesum(n,2) div 6 ===')
running_sum = 0
for i, p in enumerate(primes[:50], 1):
    running_sum += p ** 2
    if running_sum % 6 == 0:
        print(f'  n={i}: primesum={running_sum}, n%6={i%6}')

# Gemini claims: n=1 (mod 6) => div by 6
# n=7: 7%6=1 YES, n=13: 13%6=1, n=19: 19%6=1, etc.
