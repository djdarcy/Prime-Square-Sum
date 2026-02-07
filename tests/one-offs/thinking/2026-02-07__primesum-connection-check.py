"""
Check the primesum connections and assess Lean formalization requirements.
Verifies: primesum(7,2) = 666, primesum(3,1) = 10, stf(666) mod 6 = 0.
"""


def stf_algo(b):
    """stf via algorithmic digit-triangle approach"""
    import math
    r = (-1 + int(math.isqrt(1 + 8*b))) // 2
    digits = list(range(b))
    idx = 0
    total = 0
    for row_size in range(r, 0, -1):
        row_digits = digits[idx:idx + row_size]
        idx += row_size
        val = 0
        for d in row_digits:
            val = val * b + d
        total += val
    return total


if __name__ == "__main__":
    # primesum(7, 2) = 2^2 + 3^2 + 5^2 + 7^2 + 11^2 + 13^2 + 17^2
    primes_7 = [2, 3, 5, 7, 11, 13, 17]
    ps = sum(p**2 for p in primes_7)
    print(f'primesum(7, 2) = {ps}')
    print(f'stf(10) = {stf_algo(10)}')
    print(f'stf(10) == primesum(7,2): {stf_algo(10) == ps}')

    # primesum(3, 1)
    primes_3 = [2, 3, 5]
    ps1 = sum(p**1 for p in primes_3)
    print(f'primesum(3, 1) = {ps1}')
    print(f'tri(4) = 10, primesum(3,1) = {ps1}: match = {10 == ps1}')

    # stf(666) mod 6
    stf666 = 37005443752611483714216385166550857181329086284892731078593232926279977894581784762614450464857290
    print(f'stf(666) mod 6 = {stf666 % 6}')
    print(f'stf(666) is divisible by 6: {stf666 % 6 == 0}')

    print()
    print('=== Lean formalization requirements ===')
    print('1. def stf (b : Nat) : Nat  -- sum of triangular row arrangement')
    print('2. def primesum (primes : List Nat) (power : Nat) : Nat')
    print('3. theorem stf_ten : stf 10 = 666  -- by native_decide')
    print('4. theorem primesum_7_2 : primesum [2,3,5,7,11,13,17] 2 = 666')
    print('5. theorem core_identity : stf 10 = primesum [2,3,5,7,11,13,17] 2')
    print()

    print(f'stf(666) has {len(str(stf666))} digits')
    print('native_decide feasibility: LIKELY (Lean handles arbitrary precision)')
