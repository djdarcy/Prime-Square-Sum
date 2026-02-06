"""
Deeper analysis of stf(b) mod 6 patterns.
The stf-k^2 conjecture holds for k=2,3,4,5.
Now let's check: is there a general pattern for stf(b) mod 6 as a function of r?
"""
from math import isqrt


def stf(b):
    """Compute stf(b)."""
    disc = 1 + 8 * b
    sqrt_disc = isqrt(disc)
    if sqrt_disc * sqrt_disc != disc:
        return None
    r = (sqrt_disc - 1) // 2
    if r * (r + 1) // 2 != b:
        return None
    if b <= 1:
        return None

    digits = list(range(b))
    total = 0
    pos = 0
    for z in range(r, 0, -1):
        row_digits = digits[pos:pos + z]
        row_val = 0
        for d in row_digits:
            row_val = row_val * b + d
        total += row_val
        pos += z
    return total


# Extended table: stf mod 2, mod 3, mod 6, and r mod 2, r mod 3, r mod 6
print('=== stf(b) mod 6 vs r mod 6 ===')
print(f'{"r":>3} {"r%6":>4} {"r%2":>4} {"r%3":>4} {"k^2?":>5} {"stf%6":>6} {"stf%2":>6} {"stf%3":>6}')
print('-' * 50)

mod6_by_rmod6 = {}

for r in range(2, 20):
    b = r * (r + 1) // 2
    val = stf(b)
    if val is not None:
        is_sq = isqrt(r) ** 2 == r
        sq_str = f'k={isqrt(r)}' if is_sq else ''
        s6 = val % 6
        s2 = val % 2
        s3 = val % 3
        r6 = r % 6
        print(f'{r:>3} {r6:>4} {r%2:>4} {r%3:>4} {sq_str:>5} {s6:>6} {s2:>6} {s3:>6}')

        if r6 not in mod6_by_rmod6:
            mod6_by_rmod6[r6] = []
        mod6_by_rmod6[r6].append(s6)

print()
print('=== Pattern: stf mod 6 grouped by r mod 6 ===')
for r6 in sorted(mod6_by_rmod6.keys()):
    vals = mod6_by_rmod6[r6]
    print(f'  r mod 6 = {r6}: stf mod 6 values = {vals}')

# Check: is the pattern deterministic (same r%6 always gives same stf%6)?
print()
print('=== Is stf%6 determined by r%6? ===')
for r6 in sorted(mod6_by_rmod6.keys()):
    vals = mod6_by_rmod6[r6]
    unique = set(vals)
    deterministic = len(unique) == 1
    print(f'  r%6={r6}: {"DETERMINISTIC" if deterministic else "VARIES"} -> {unique}')

# Check r mod 12 for finer pattern
print()
print('=== Try r mod 12 ===')
mod12_by = {}
for r in range(2, 20):
    b = r * (r + 1) // 2
    val = stf(b)
    if val is not None:
        r12 = r % 12
        s6 = val % 6
        if r12 not in mod12_by:
            mod12_by[r12] = []
        mod12_by[r12].append(s6)

for r12 in sorted(mod12_by.keys()):
    vals = mod12_by[r12]
    unique = set(vals)
    deterministic = len(unique) == 1
    print(f'  r%12={r12:>2}: stf%6 = {vals} {"DETERMINISTIC" if deterministic else "VARIES"}')

# Perfect squares mod 6: k^2 mod 6 cycles as 1,4,3,4,1,0 for k=1..6
print()
print('=== Perfect squares mod 6 ===')
for k in range(1, 10):
    r = k*k
    print(f'  k={k}: r=k^2={r}, r%6={r%6}, r%12={r%12}')

# Key question: perfect squares mod 6 are always 0, 1, 3, or 4
# r=4: 4%6=4, r=9: 9%6=3, r=16: 16%6=4, r=25: 25%6=1
# These are NOT all the same mod 6! Yet all give stf%6=0.
# So the pattern is deeper than just r%6.
