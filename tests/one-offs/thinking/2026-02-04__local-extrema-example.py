"""
Verification calculations for Issue #23: Smart Early Termination
Local extrema example with f(x) = x^3 - 3x

This demonstrates why simple threshold termination can fail for non-monotonic functions.
"""
from scipy.optimize import fsolve

def f(x):
    """Example function with local extrema: f(x) = x^3 - 3x"""
    return x**3 - 3*x

# Find where f(x) = 5
def equation(x):
    return f(x) - 5

solution = fsolve(equation, 2.0)[0]
print('=' * 60)
print('Issue #23: Local Extrema Example')
print('Function: f(x) = x^3 - 3x')
print('=' * 60)
print()
print('Solution to f(x) = 5: x = %.5f' % solution)
print('Verification: f(%.5f) = %.6f' % (solution, f(solution)))
print()
print('Function values at key points:')
print('-' * 40)
for x in [-2, -1, 0, 1, 2, 2.27902, 3]:
    print('  f(%7.4f) = %8.4f' % (x, f(x)))
print()
print('Key observations:')
print('  - Local maximum at x = -1, f(-1) = 2')
print('  - Local minimum at x = 1, f(1) = -2')
print('  - Solution f(x) = 5 is at x = 2.27902')
print()
print('Problem scenario:')
print('  - Searching for f(n) == 5')
print('  - User sets --min-lhs-value -2 (stop when LHS falls to -2)')
print('  - At n=1, f(1) = -2 hits the threshold')
print('  - Iteration terminates')
print('  - Valid solution at x = 2.27902 is never found')
