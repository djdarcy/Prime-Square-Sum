"""
Verify the user's specific algebraic example and explore
the combinatorial number system (combinadic) connection.
"""
from math import comb


def verify_user_example():
    """User's example: (a+b)^2 = a^2 + 2ab + b^2 = 6, with a=1.

    Setting a=1: 1 + 2b + b^2 = 6
    => b^2 + 2b - 5 = 0
    => b = (-2 +/- sqrt(4+20))/2 = (-2 +/- sqrt(24))/2
    => b = (-2 + 4.899)/2 = 1.449 or b = (-2 - 4.899)/2 = -3.449

    User claimed b=6 and ab=-15.5. Let me check their calculation.
    """
    print('=== Verify user algebraic example ===')
    import math

    # User's claim: a=1, b=6
    a, b = 1, 6
    result = a**2 + 2*a*b + b**2
    print(f'  (a+b)^2 with a={a}, b={b}: {a}^2 + 2*{a}*{b} + {b}^2 = {result}')
    print(f'  This equals (1+6)^2 = 49, NOT 6')

    # User's alternative interpretation: treat a,b as INDEPENDENT variables
    # 1*a^2 + 2*(ab) + 1*b^2 = 6
    # If a=1, b=6: 1 + 2*6 + 36 = 49, not 6
    # User then says ab = (1/2)(6 - a^2 - b^2) = (1/2)(6 - 1 - 36) = -15.5
    ab = 0.5 * (6 - a**2 - b**2)
    print(f'  User formula: ab = (1/2)(6 - a^2 - b^2) = {ab}')
    check = a**2 + 2*ab + b**2
    print(f'  Check: a^2 + 2*ab + b^2 = {a**2} + 2*{ab} + {b**2} = {check}')
    print(f'  This works! But ab is being treated as an INDEPENDENT variable')
    print(f'  Not as the product a*b = {a*b}')

    print()
    print('  KEY INSIGHT: The user is proposing to DECOUPLE the binomial terms.')
    print('  Instead of (a+b)^2 = a^2 + 2ab + b^2 where ab=a*b,')
    print('  they treat each term as an independent "digit" with Pascal weights.')
    print('  So: 1*D0 + 2*D1 + 1*D2 = X where D0,D1,D2 are free variables.')


def explore_combinatorial_number_system():
    """The combinatorial number system (combinadic) is a known system
    that represents numbers using binomial coefficients.

    Every non-negative integer N has a UNIQUE representation:
    N = C(c_k, k) + C(c_{k-1}, k-1) + ... + C(c_1, 1)
    where c_k > c_{k-1} > ... > c_1 >= 0

    This IS a number system based on Pascal's triangle!
    """
    print('\n=== Combinatorial Number System (Combinadic) ===')
    print('Known result: every N has unique representation as sum of')
    print('binomial coefficients from different Pascal diagonals.')
    print()

    # Encode numbers 0..20 in combinadic (k=3)
    def to_combinadic(n, k):
        """Convert n to combinadic with k terms."""
        result = []
        remaining = n
        for i in range(k, 0, -1):
            # Find largest c such that C(c, i) <= remaining
            c = i
            while comb(c + 1, i) <= remaining:
                c += 1
            result.append(c)
            remaining -= comb(c, i)
        return result

    print('k=3 combinadic (N = C(c3,3) + C(c2,2) + C(c1,1)):')
    for n in range(20):
        rep = to_combinadic(n, 3)
        terms = [f'C({c},{i+1})={comb(c,i+1)}' for i, c in enumerate(reversed(rep))]
        check = sum(comb(c, k+1) for k, c in enumerate(reversed(rep)))
        print(f'  {n:2d} = {" + ".join(terms)} (check={check})')


def explore_zeckendorf():
    """Zeckendorf's theorem: every positive integer has a unique
    representation as a sum of non-consecutive Fibonacci numbers.

    Since Fibonacci numbers come from Pascal diagonal sums,
    this is ANOTHER Pascal-based number system!
    """
    print('\n=== Zeckendorf Representation (Fibonacci-Pascal) ===')
    fibs = [1, 2, 3, 5, 8, 13, 21, 34, 55, 89]

    def to_zeckendorf(n):
        result = []
        remaining = n
        for f in reversed(fibs):
            if f <= remaining:
                result.append(f)
                remaining -= f
        return result

    for n in range(1, 25):
        rep = to_zeckendorf(n)
        bits = ''.join('1' if f in rep else '0' for f in reversed(fibs[:6]))
        print(f'  {n:2d} = {" + ".join(str(x) for x in rep):20s} [{bits}]')


def explore_prime_patterns():
    """Look for patterns in how primes appear across different
    Pascal-based representations."""
    print('\n=== Prime patterns across representations ===')

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]

    # Row-weighted: X = sum d_k * C(n, k)
    # With greedy canonical form
    def pascal_greedy(X, n):
        weights = [comb(n, k) for k in range(n+1)]
        remaining = X
        digits = [0] * (n + 1)
        for i in sorted(range(n+1), key=lambda j: weights[j], reverse=True):
            digits[i] = remaining // weights[i]
            remaining -= digits[i] * weights[i]
        return digits

    print('Row 4 greedy [weights: 1,4,6,4,1]:')
    for p in primes:
        d = pascal_greedy(p, 4)
        print(f'  {p:2d} -> {d}')

    # Look for which primes have d_middle = 0
    print('\nPrimes where center digit (weight 6) is 0 vs nonzero:')
    for p in primes:
        d = pascal_greedy(p, 4)
        center = d[2]
        print(f'  {p:2d}: center={center} {"***" if center == 0 else ""}')


if __name__ == '__main__':
    verify_user_example()
    explore_combinatorial_number_system()
    explore_zeckendorf()
    explore_prime_patterns()
