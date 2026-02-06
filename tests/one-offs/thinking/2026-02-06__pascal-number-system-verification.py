"""
Verification scripts for Pascal-weighted number system analysis.
2026-02-06: Exploring whether binomial coefficients can serve as
positional weights in a counting system.
"""
from math import comb
import numpy as np


def verify_11n_pascal_rows():
    """Verify: 11^n encodes Pascal row coefficients (up to n=4)."""
    print('=== 11^n vs Pascal rows ===')
    for n in range(8):
        row = [comb(n, k) for k in range(n+1)]
        val_11 = 11**n
        print(f'  11^{n} = {val_11:>10}  Pascal row {n}: {row}')
    print()
    # Digit carry problem at n>=5
    print('=== Digit carry problem at n=5 ===')
    row5 = [comb(5, k) for k in range(6)]
    print(f'  Pascal row 5: {row5}')
    print(f'  11^5 = {11**5} (digits: 1,6,1,0,5,1 -- NOT 1,5,10,10,5,1)')
    print(f'  Because 10 carries into adjacent digit')


def verify_base_selection():
    """PascalRow function: choosing base = max(coefficients)+1 avoids carry."""
    print('\n=== Base selection to avoid carry ===')
    for n in range(1, 9):
        row = [comb(n, k) for k in range(n+1)]
        max_coeff = max(row)
        base = max_coeff + 1
        val = sum(c * base**(n - i) for i, c in enumerate(row))
        print(f'  n={n}: row={row}, base={base}, value={val}, (base+1)^n={(base+1)**n}')


def verify_stf():
    """Verify stf(10) = 666."""
    print('\n=== stf(10) = 666 verification ===')
    primes_7 = [2, 3, 5, 7, 11, 13, 17]
    stf_10 = sum(p**2 for p in primes_7)
    print(f'  stf(10) = sum of p^2 for first 7 primes = {stf_10}')


def explore_representability():
    """Can every natural be represented as (a+b)^n?"""
    print('\n=== Representability: (a+b)^n = X ===')
    print('  Trivially: n=1, a=0, b=X -> (0+X)^1 = X')
    print('  For n=2: (a+b)^2 = X requires X to be a perfect square')
    print()
    print('  Key insight: sum_k C(n,k) * a^(n-k) * b^k = (a+b)^n ALWAYS')
    print('  So Pascal coefficients with two bases a,b always give (a+b)^n')


def explore_digit_weighted():
    """Digit-weighted representation: X = sum d_k * C(n,k)."""
    print('\n=== Digit-weighted representation (row 2: weights 1,2,1) ===')
    for X in range(1, 21):
        solutions = []
        for d0 in range(X+1):
            for d1 in range((X-d0)//2 + 1):
                d2 = X - d0 - 2*d1
                if d2 >= 0:
                    solutions.append((d0, d1, d2))
        print(f'  X={X:2d}: {len(solutions):3d} reps as d0+2*d1+d2 (first: {solutions[0]})')


def explore_pascal_diagonals():
    """Pascal diagonals encode figurate numbers."""
    print('\n=== Pascal diagonals encode figurate numbers ===')
    print('Diagonal 1: natural numbers')
    for n in range(7):
        print(f'  C({n+1},{1}) = {comb(n+1,1)}')
    print('Diagonal 2: triangular numbers')
    for n in range(7):
        print(f'  C({n+2},{2}) = {comb(n+2,2)}')
    print('Diagonal 3: tetrahedral numbers')
    for n in range(7):
        print(f'  C({n+3},{3}) = {comb(n+3,3)}')


def explore_fibonacci_from_pascal():
    """Fibonacci sequence from shallow diagonals."""
    print('\n=== Fibonacci from Pascal shallow diagonals ===')
    for n in range(10):
        fib_val = sum(comb(n - k, k) for k in range(n // 2 + 1))
        print(f'  Fib sum for n={n}: {fib_val}')


def explore_bounded_digit_coverage():
    """With bounded digits, does Pascal-weighted representation have gaps?"""
    print('\n=== Bounded digit coverage ===')
    n = 4  # Row 4: weights 1, 4, 6, 4, 1
    weights = [comb(n, k) for k in range(n+1)]
    print(f'Row {n} weights: {weights}')
    print(f'Sum of weights (all d=1): {sum(weights)} = 2^{n}')

    max_digit = 5
    representable = set()
    for d0 in range(max_digit+1):
        for d1 in range(max_digit+1):
            for d2 in range(max_digit+1):
                for d3 in range(max_digit+1):
                    for d4 in range(max_digit+1):
                        val = d0*1 + d1*4 + d2*6 + d3*4 + d4*1
                        representable.add(val)
    max_rep = max(representable)
    gaps = [x for x in range(max_rep+1) if x not in representable]
    print(f'With digits 0..{max_digit}, row {n}: covers 0..{max_rep}')
    print(f'Gaps in coverage: {gaps[:20]}... ({len(gaps)} total gaps)')

    print('\n=== Key insight ===')
    print('Since C(n,0) = C(n,n) = 1, the first and last weights are always 1.')
    print('With unbounded digits, d_0 alone covers all naturals.')
    print('The INTERESTING question is: with BOUNDED digits (0..B-1),')
    print('what is the most compact Pascal-weighted representation?')


if __name__ == '__main__':
    verify_11n_pascal_rows()
    verify_base_selection()
    verify_stf()
    explore_representability()
    explore_digit_weighted()
    explore_pascal_diagonals()
    explore_fibonacci_from_pascal()
    explore_bounded_digit_coverage()
