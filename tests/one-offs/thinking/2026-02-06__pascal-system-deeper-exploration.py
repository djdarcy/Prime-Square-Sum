"""
Deeper exploration of Pascal-weighted number systems.
Focus: uniqueness, canonical forms, prime visibility, stf() connection.
"""
from math import comb, isqrt
import numpy as np


def explore_uniqueness():
    """How unique are Pascal-weighted representations?

    Standard positional (base B): each number has exactly ONE representation.
    Pascal-weighted: multiple representations exist. Is there a canonical form?
    """
    print('=== Uniqueness of Pascal-weighted representations ===')
    # Row 3 weights: [1, 3, 3, 1]
    # X = d0 + 3*d1 + 3*d2 + d3
    n = 3
    weights = [comb(n, k) for k in range(n+1)]
    print(f'Row {n} weights: {weights}')

    for X in [6, 10, 15, 666]:
        count = 0
        first = None
        # Limit search for large X
        max_d = min(X, 50)
        for d0 in range(max_d+1):
            for d1 in range((X - d0) // 3 + 1):
                for d2 in range((X - d0 - 3*d1) // 3 + 1):
                    d3 = X - d0 - 3*d1 - 3*d2
                    if d3 >= 0:
                        count += 1
                        if first is None:
                            first = (d0, d1, d2, d3)
        print(f'  X={X}: {count} representations (first: {first})')


def explore_canonical_forms():
    """Can we define a canonical (unique) Pascal representation?

    Idea 1: "greedy" - use largest weight first (like standard positional)
    Idea 2: "balanced" - minimize max digit
    Idea 3: "symmetric" - prefer symmetric digit patterns
    """
    print('\n=== Canonical form exploration ===')

    for row_n in [2, 3, 4]:
        weights = [comb(row_n, k) for k in range(row_n+1)]
        print(f'\nRow {row_n} weights: {weights}')

        for X in [6, 10, 15, 21]:
            # Greedy: assign digits from largest weight down
            remaining = X
            sorted_positions = sorted(range(len(weights)),
                                     key=lambda i: weights[i], reverse=True)
            digits_greedy = [0] * (row_n + 1)
            for pos in sorted_positions:
                if weights[pos] > 0:
                    digits_greedy[pos] = remaining // weights[pos]
                    remaining -= digits_greedy[pos] * weights[pos]

            check = sum(d * w for d, w in zip(digits_greedy, weights))
            print(f'  X={X:3d}: greedy={digits_greedy} (check={check})')


def explore_prime_visibility():
    """How do primes look in Pascal-weighted representation?"""
    print('\n=== Primes in Pascal-weighted representation ===')

    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

    # Row 2: weights [1, 2, 1]
    print('Row 2 weights [1, 2, 1]:')
    for p in primes:
        # Canonical: maximize middle digit first (weight 2)
        d1 = p // 2
        remainder = p - 2 * d1
        # Put remainder in d0
        print(f'  {p:2d} = {remainder}*1 + {d1}*2 + 0*1 = ({remainder},{d1},0)')

    # Row 3: weights [1, 3, 3, 1]
    print('\nRow 3 weights [1, 3, 3, 1]:')
    for p in primes:
        d1 = p // 3
        r1 = p - 3 * d1
        print(f'  {p:2d} = {r1}*1 + {d1}*3 + 0*3 + 0*1 = ({r1},{d1},0,0)')


def explore_stf_connection():
    """How does stf() relate to Pascal representation?

    stf(b) = sum of squared primes for triangular bases
    stf(10) = 2^2 + 3^2 + 5^2 + 7^2 + 11^2 + 13^2 + 17^2 = 666

    T(10) = 55 (10th triangular number)
    pi(10) = 4 primes <= 10, but we use 7 primes (primes <= T(10)? No...)
    Actually: 7 = pi(17), and 17 is the 7th prime
    """
    print('\n=== stf() and Pascal triangle connection ===')

    # stf(b) uses pi(b*(b-1)/2) primes? Let's check
    # T(n) = n*(n+1)/2 ... but stf uses "triangular base" concept
    # Actually for stf(10): base 10, and we sum p^2 for first pi(base) primes?
    # No: stf(10) = 666 uses 7 primes. pi(10) = 4.
    # 7 = number of primes <= 17. 17 = ?

    # Let me just verify the relationship
    first_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

    for b in [10]:
        print(f'Base b={b}:')
        print(f'  T({b}) = {b*(b+1)//2}')

        n_primes = 7
        primes = first_primes[:n_primes]
        total = sum(p**2 for p in primes)
        print(f'  First {n_primes} primes: {primes}')
        print(f'  Sum of squares: {total}')

        # Pascal row 6 (7 elements): [1, 6, 15, 20, 15, 6, 1]
        row6 = [comb(6, k) for k in range(7)]
        print(f'  Pascal row 6 (matching 7 primes): {row6}')

        # What if we weight the squared primes by Pascal coefficients?
        pascal_weighted = sum(c * p**2 for c, p in zip(row6, primes))
        print(f'  Pascal-weighted sum of p^2: {pascal_weighted}')

        # Connection: 666 in Pascal digit form
        print(f'\n  666 in various Pascal rows:')
        for rn in range(2, 7):
            w = [comb(rn, k) for k in range(rn+1)]
            # Greedy decomposition
            remaining = 666
            digits = []
            for wi in sorted(range(len(w)), key=lambda i: w[i], reverse=True):
                d = remaining // w[wi]
                digits.append((wi, d))
                remaining -= d * w[wi]
            digits.sort()
            d_vals = [0]*(rn+1)
            for pos, val in digits:
                d_vals[pos] = val
            check = sum(d*wt for d, wt in zip(d_vals, w))
            print(f'    Row {rn} {w}: digits={d_vals} (check={check}, remainder={666-check})')


def explore_mixed_base_pascal():
    """What if we use DIFFERENT Pascal rows for different digit positions?

    Like mixed-radix but with Pascal weights:
    X = d_0 * C(0,0) + d_1 * C(1,1) + d_2 * C(2,1) + d_3 * C(3,1) + ...
    i.e., weights from a diagonal of Pascal's triangle
    """
    print('\n=== Mixed Pascal: diagonal weights ===')

    # Diagonal 1 (natural numbers): 1, 1, 1, 1, ...  (trivial, unary-like)
    # Diagonal 2 (natural numbers): 1, 2, 3, 4, 5, ...
    # Diagonal 3 (triangular): 1, 3, 6, 10, 15, ...
    # Diagonal 4 (tetrahedral): 1, 4, 10, 20, 35, ...

    print('Diagonal 2 weights (natural numbers as weights):')
    n_positions = 6
    weights_d2 = [k+1 for k in range(n_positions)]  # 1, 2, 3, 4, 5, 6
    print(f'  Weights: {weights_d2}')

    print('\nDiagonal 3 weights (triangular numbers as weights):')
    weights_d3 = [comb(k+2, 2) for k in range(n_positions)]  # 1, 3, 6, 10, 15, 21
    print(f'  Weights: {weights_d3}')

    # This is INTERESTING because triangular numbers ARE what stf() is about!
    print('\n  stf() connection: triangular number weights!')
    print('  If digits are prime squares, this directly models stf()')

    # Verify: using triangular weights with specific digits
    # X = d0*1 + d1*3 + d2*6 + d3*10 + d4*15 + d5*21
    for X in [6, 10, 28, 55, 666]:
        # Simple greedy
        remaining = X
        digits = [0] * n_positions
        for i in range(n_positions - 1, -1, -1):
            digits[i] = remaining // weights_d3[i]
            remaining -= digits[i] * weights_d3[i]
        check = sum(d*w for d, w in zip(digits, weights_d3))
        print(f'  X={X:3d}: digits={digits} weights={weights_d3} check={check}')


if __name__ == '__main__':
    explore_uniqueness()
    explore_canonical_forms()
    explore_prime_visibility()
    explore_stf_connection()
    explore_mixed_base_pascal()
