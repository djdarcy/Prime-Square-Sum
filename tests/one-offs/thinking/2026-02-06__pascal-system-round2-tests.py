"""
Round 2 tests for collaborate3: Investigating Gemini's suggestions.
1. Primes 4k+1 vs 4k+3 in Pascal representation
2. Multiplicity N(X, n) for primes vs composites
3. stf(b) for small triangular bases in Pascal/figurate representations
4. primesum(15, 3) analysis
5. 666 divisibility by central coefficients — is it special or common?
"""
from math import comb, isqrt
import numpy as np


def greedy_canonical(X, weights):
    """Greedy decomposition: largest weight first."""
    remaining = X
    n = len(weights)
    digits = [0] * n
    for i in sorted(range(n), key=lambda j: weights[j], reverse=True):
        if weights[i] > 0:
            digits[i] = remaining // weights[i]
            remaining -= digits[i] * weights[i]
    return digits


def test_prime_classes_in_pascal():
    """Gemini Q4: Do 4k+1 vs 4k+3 primes look different in Pascal form?"""
    print('=== Primes by class in Row 4 [1,4,6,4,1] ===')
    weights = [comb(4, k) for k in range(5)]

    # First 50 primes
    def sieve(n):
        s = [True] * (n+1)
        s[0] = s[1] = False
        for i in range(2, isqrt(n)+1):
            if s[i]:
                for j in range(i*i, n+1, i):
                    s[j] = False
        return [i for i in range(2, n+1) if s[i]]

    primes = sieve(250)

    print(f'  {"p":>4} {"class":>5} {"digits":>20} {"d0":>3} {"d1":>3} {"d2":>3} {"d3":>3} {"d4":>3}')
    class_1_patterns = []
    class_3_patterns = []

    for p in primes[:30]:
        d = greedy_canonical(p, weights)
        cls = p % 4
        cls_str = f'{cls}k+{p%4}' if p > 2 else 'even'
        print(f'  {p:>4} {cls_str:>5} {str(d):>20} {d[0]:>3} {d[1]:>3} {d[2]:>3} {d[3]:>3} {d[4]:>3}')
        if p > 2:
            if cls == 1:
                class_1_patterns.append(d)
            else:
                class_3_patterns.append(d)

    # Analyze: d0 parity
    print(f'\n  4k+1 primes: d0 values = {[d[0] for d in class_1_patterns]}')
    print(f'  4k+3 primes: d0 values = {[d[0] for d in class_3_patterns]}')
    print(f'  4k+1 primes: d1 values = {[d[1] for d in class_1_patterns]}')
    print(f'  4k+3 primes: d1 values = {[d[1] for d in class_3_patterns]}')


def test_multiplicity_primes_vs_composites():
    """Gemini Q2: Is N(prime, ...) < N(composite, ...) consistently?"""
    print('\n=== Multiplicity: primes vs composites in Row 3 [1,3,3,1] ===')
    weights = [1, 3, 3, 1]

    def count_representations(X, weights, max_digit=None):
        if max_digit is None:
            max_digit = X
        count = 0
        for d0 in range(min(X, max_digit) + 1):
            for d1 in range(min((X - d0) // 3, max_digit) + 1):
                for d2 in range(min((X - d0 - 3*d1) // 3, max_digit) + 1):
                    d3 = X - d0 - 3*d1 - 3*d2
                    if 0 <= d3 <= max_digit:
                        count += 1
        return count

    def is_prime(n):
        if n < 2: return False
        if n < 4: return True
        if n % 2 == 0 or n % 3 == 0: return False
        i = 5
        while i*i <= n:
            if n % i == 0 or n % (i+2) == 0: return False
            i += 6
        return True

    # Compare multiplicity for bounded digits (0..10)
    max_d = 10
    print(f'  Bounded digits 0..{max_d}:')
    print(f'  {"X":>4} {"type":>10} {"N(X)":>8}')
    for X in range(2, 31):
        t = "PRIME" if is_prime(X) else "comp"
        n = count_representations(X, weights, max_d)
        print(f'  {X:>4} {t:>10} {n:>8}')


def test_stf_small_bases():
    """Gemini medium-term: stf(b) for small triangular bases."""
    print('\n=== stf(b) for small triangular bases ===')

    def stf(b):
        """Compute stf(b) = sum of triangular row values in base b."""
        r = int((-1 + (1 + 8*b)**0.5) / 2)
        if r*(r+1)//2 != b:
            return None  # not a triangular number

        # Build digits 0..b-1 in triangular rows
        digits = list(range(b))
        total = 0
        pos = 0
        for z in range(r, 0, -1):  # bottom row (size r) to top (size 1)
            row_digits = digits[pos:pos+z]
            # Interpret as base-b number
            row_val = 0
            for d in row_digits:
                row_val = row_val * b + d
            total += row_val
            pos += z
        return total

    # Triangular numbers: 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105
    tri_nums = [n*(n+1)//2 for n in range(1, 15)]

    for b in tri_nums:
        val = stf(b)
        if val is not None and b > 1:
            # Pascal row representations
            for row_n in [2, 3, 4]:
                w = [comb(row_n, k) for k in range(row_n+1)]
                d = greedy_canonical(val, w)
                print(f'  stf({b:>3}) = {val:>10} | Row {row_n} {w}: {d}')

            # Triangular weight representation
            tri_w = [comb(k+2, 2) for k in range(8)]  # [1,3,6,10,15,21,28,36]
            d_tri = greedy_canonical(val, tri_w)
            print(f'  {"":>22} | Tri weights: {d_tri}')
            print()


def test_primesum_15_3():
    """Gemini suggestion: compute primesum(15, 3)."""
    print('\n=== primesum(15, 3) ===')

    def sieve(n):
        s = [True] * (n+1)
        s[0] = s[1] = False
        for i in range(2, isqrt(n)+1):
            if s[i]:
                for j in range(i*i, n+1, i):
                    s[j] = False
        return [i for i in range(2, n+1) if s[i]]

    primes = sieve(100)[:15]
    print(f'  First 15 primes: {primes}')

    ps15_3 = sum(p**3 for p in primes)
    print(f'  primesum(15, 3) = sum(p^3) = {ps15_3}')

    # Is it triangular?
    # tri(n) = n*(n+1)/2, so n = (-1 + sqrt(1+8*X))/2
    disc = 1 + 8*ps15_3
    sqrt_disc = isqrt(disc)
    is_tri = sqrt_disc * sqrt_disc == disc and (sqrt_disc - 1) % 2 == 0
    print(f'  Is triangular? {is_tri} (discriminant={disc}, sqrt={sqrt_disc})')

    # Pascal representations
    for row_n in [2, 3, 4, 5]:
        w = [comb(row_n, k) for k in range(row_n+1)]
        d = greedy_canonical(ps15_3, w)
        print(f'  Row {row_n} {w}: {d}')

    # Triangular weights
    tri_w = [comb(k+2, 2) for k in range(10)]
    d_tri = greedy_canonical(ps15_3, tri_w)
    print(f'  Tri weights {tri_w}: {d_tri}')


def test_666_divisibility_special():
    """Is 666's divisibility by central coefficients special?
    Compare against nearby numbers."""
    print('\n=== Is 666 divisibility by central coefficients special? ===')

    for X in [660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670]:
        divs = []
        for row_n in range(2, 8):
            center = max(comb(row_n, k) for k in range(row_n+1))
            if X % center == 0:
                quotient = X // center
                # Is quotient a repdigit?
                s = str(quotient)
                is_rep = len(set(s)) == 1
                divs.append(f'C({row_n})={center}→{quotient}{"*" if is_rep else ""}')

        marker = " <<<" if X == 666 else ""
        print(f'  {X}: {", ".join(divs)}{marker}')


if __name__ == '__main__':
    test_prime_classes_in_pascal()
    test_multiplicity_primes_vs_composites()
    test_stf_small_bases()
    test_primesum_15_3()
    test_666_divisibility_special()
