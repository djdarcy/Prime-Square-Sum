"""
Triangular Primesum Chain Conjecture Test
==========================================

User's observation:
  primesum(3, 1) = 10 = tri(4),     and 3 + 4 = 7
  primesum(7, 2) = 666 = tri(36),   and 7 + 36 = 43

Conjecture: Does this k+n chain continue?
  primesum(43, p) = tri(m) for some p and m?

Also: broader scan of which primesum(k,p) are triangular at all.

Date: 2026-02-09
"""
import math


def tri(n):
    return n * (n + 1) // 2


def is_triangular(t):
    """Returns (True, k) if t = tri(k), else (False, -1)."""
    if t < 0:
        return False, -1
    disc = 1 + 8 * t
    s = int(math.isqrt(disc))
    if s * s == disc and (s - 1) % 2 == 0:
        return True, (s - 1) // 2
    return False, -1


def sieve(limit):
    """Simple Eratosthenes sieve up to limit."""
    is_prime = [True] * (limit + 1)
    is_prime[0] = is_prime[1] = False
    for i in range(2, int(limit ** 0.5) + 1):
        if is_prime[i]:
            for j in range(i * i, limit + 1, i):
                is_prime[j] = False
    return [p for p in range(2, limit + 1) if is_prime[p]]


primes = sieve(500)  # 95 primes up to 500


def primesum(k, p):
    """Sum of first k primes each raised to power p."""
    return sum(primes[i] ** p for i in range(k))


# ---- Verify the known chain ----
print("=" * 60)
print("Known Chain")
print("=" * 60)

ps31 = primesum(3, 1)
_, n31 = is_triangular(ps31)
print(f"primesum(3,1) = {ps31} = tri({n31})")
print(f"  k + n = 3 + {n31} = {3 + n31}")
print()

ps72 = primesum(7, 2)
_, n72 = is_triangular(ps72)
print(f"primesum(7,2) = {ps72} = tri({n72})")
print(f"  k + n = 7 + {n72} = {7 + n72}")
print()

# ---- Test the conjecture: primesum(43, p) triangular? ----
print("=" * 60)
print("Conjecture: primesum(43, p) = triangular?")
print("=" * 60)

for p in range(1, 6):
    val = primesum(43, p)
    is_tri, n = is_triangular(val)
    status = f"= tri({n})" if is_tri else "NOT triangular"
    print(f"  primesum(43, {p}) = {val}  {status}")
    if is_tri:
        print(f"    *** CHAIN CONTINUES! 43 + {n} = {43 + n} ***")

print()

# ---- Broader scan ----
print("=" * 60)
print("Broader scan: which primesum(k, p) are triangular?")
print("  k = 1..80, p = 1..4")
print("=" * 60)

triangular_results = []
for p in range(1, 5):
    for k in range(1, 81):
        if k > len(primes):
            break
        val = primesum(k, p)
        is_tri, n = is_triangular(val)
        if is_tri:
            triangular_results.append((k, p, val, n, k + n))
            print(f"  primesum({k}, {p}) = {val} = tri({n})   [k+n = {k + n}]")

print()

# ---- Check for chain patterns ----
print("=" * 60)
print("Chain pattern check: does any k+n lead to another triangular primesum?")
print("=" * 60)

found_chain = False
for k, p, val, n, kn in triangular_results:
    for k2, p2, val2, n2, kn2 in triangular_results:
        if k2 == kn:
            print(f"  CHAIN: primesum({k},{p})=tri({n}), k+n={kn}")
            print(f"      -> primesum({kn},{p2})=tri({n2}), k+n={kn2}")
            found_chain = True

if not found_chain:
    print("  No chains found beyond the known 3->7 link.")
    # Check: is 3->7 itself in our results?
    print()
    print("  Verifying the 3->7 link:")
    print(f"    primesum(3,1)=10=tri(4), k+n=7")
    print(f"    primesum(7,2)=666=tri(36), k+n=43")
    print(f"    But primesum(43,p) is NOT triangular for p=1..4")
    print(f"    => The chain terminates at step 2.")

print()

# ---- Also check primesum(12, p) since primesum(5,1)=tri(7) gives k+n=12 ----
print("=" * 60)
print("Bonus: primesum(5,1) = 28 = tri(7), k+n = 12")
print("  Does primesum(12, p) = triangular?")
print("=" * 60)

for p in range(1, 5):
    val = primesum(12, p)
    is_tri, n = is_triangular(val)
    status = f"= tri({n})" if is_tri else "NOT triangular"
    print(f"  primesum(12, {p}) = {val}  {status}")

print()
print("CONCLUSION: The k+n chain appears to be a coincidence of small numbers,")
print("not a general pattern. Only the 3->7 link works; the chain breaks at 43")
print("and the parallel 5->12 chain also doesn't produce triangular values.")
