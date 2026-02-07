"""
Deeper analysis of what tf computes for each row, and design of a
Lean-friendly algorithmic stf definition.

tf(b, z) where z counts from TOP (z=1 is top/smallest row)
For base 10, rows are:
  z=1 (top):    [9]          -> 9     in base 10
  z=2:          [7, 8]       -> 78    in base 10
  z=3:          [4, 5, 6]    -> 456   in base 10
  z=4 (bottom): [0, 1, 2, 3] -> 123   in base 10
"""


def tri(n):
    return n * (n + 1) // 2


def tf_closed(b, z):
    num = (-2 + 2*b - 2*b**2 + z - b*z - z**2 + b*z**2 + b**z * (2 + 2*b**2 + z + z**2 - b*(2 + z + z**2)))
    den = 2 * (b - 1)**2
    return num // den


def row_value_algo(b, z):
    """Row z from top has z digits, starting at digit b - tri(z)"""
    start = b - tri(z)
    val = 0
    for i in range(z):
        val = val * b + (start + i)
    return val


if __name__ == "__main__":
    # Verify row structure for base 10
    print('=== Row structure for base 10 (z from top) ===')
    b = 10
    for z in range(1, 5):
        start = b - tri(z)
        digits = [start + i for i in range(z)]
        val = row_value_algo(b, z)
        print(f'  z={z}: digits={digits}, value={val}')

    print()
    print('=== Algorithmic vs closed-form for Lean ===')
    print()
    print('Algorithmic stf:')
    print('  - No division needed')
    print('  - Build digit list, form base-b numbers, sum')
    print('  - Straightforward Lean definition using List.foldl')
    print('  - native_decide works for concrete values')
    print()
    print('Closed-form tf:')
    print('  - Division by 2*(b-1)^2')
    print('  - Requires proving divisibility (like tri_is_triangular)')
    print('  - More algebraically powerful for general theorems')
    print('  - But harder to prove correct in Lean')
    print()

    # Lean definition sketch
    print('=== Lean definition sketch ===')
    print('''
-- Helper: interpret a list of digits as a base-b number
def digitsToNat (b : Nat) (digits : List Nat) : Nat :=
  digits.foldl (fun acc d => acc * b + d) 0

-- Row z from top: z digits starting at b - tri(z)
def rowValue (b z : Nat) : Nat :=
  digitsToNat b ((List.range z).map (· + b - tri z))

-- stf: sum over all rows z = 1 to r where r = qg(b)
def stf (b : Nat) : Nat :=
  if b <= 1 then 0
  else
    let r := ...  -- qg(b)
    (List.range r).foldl (fun acc i => acc + rowValue b (i + 1)) 0
''')

    # Feasibility assessment
    print('=== Feasibility for concrete proofs ===')
    theorems = [
        ('stf_ten', 'stf 10 = 666', 'native_decide'),
        ('stf_ten_rows', 'stf 10 = 9 + 78 + 456 + 123', 'ring or native_decide'),
        ('tri_four_eq_ten', 'tri 4 = 10', 'already proved'),
        ('primesum_7_2', 'primesum [2,3,5,7,11,13,17] 2 = 666', 'native_decide'),
        ('stf_eq_primesum', 'stf 10 = primesum [2,3,5,7,11,13,17] 2', 'transitivity'),
        ('stf_is_tri', 'isTriangular (stf 10) = true', 'tri_is_triangular + stf_ten'),
        ('stf_666_value', 'stf 666 = [98-digit]', 'native_decide (may be slow)'),
        ('stf_666_mod6', 'stf 666 % 6 = 0', 'native_decide'),
    ]

    for name, stmt, approach in theorems:
        print(f'  {name}: {stmt}')
        print(f'    approach: {approach}')
        print()
