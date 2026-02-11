"""
Test: Does argparse's prefix matching cause `-m` to collide with `--min`?

Scenarios:
1. --min, --max alongside --max-n, --max-m
2. Single-dash -min, -max alongside -m, -n
3. Abbreviation: does --ma match --max or --max-n?
"""
import argparse
import sys

def test_double_dash_aliases():
    """Test --min/--max as aliases for --iter-start/--iter-stop."""
    print("=" * 60)
    print("TEST 1: --min/--max as aliases (double-dash)")
    print("=" * 60)

    p = argparse.ArgumentParser()
    p.add_argument('--min', '--iter-start', dest='iter_start', action='append',
                   metavar='VAR:VALUE')
    p.add_argument('--max', '--iter-stop', dest='iter_stop', action='append',
                   metavar='VAR:VALUE')
    p.add_argument('--max-n', type=int, default=1000000)
    p.add_argument('--max-m', type=int, default=10000)

    # Test: --min and --max work
    args = p.parse_args(['--min', 'n:100', '--max', 'n:5000'])
    print(f"  --min n:100 --max n:5000  => iter_start={args.iter_start}, iter_stop={args.iter_stop}")
    assert args.iter_start == ['n:100']
    assert args.iter_stop == ['n:5000']
    print("  PASS")

    # Test: --iter-start and --iter-stop still work (same dest)
    args = p.parse_args(['--iter-start', 'n:100', '--iter-stop', 'n:5000'])
    print(f"  --iter-start/stop       => iter_start={args.iter_start}, iter_stop={args.iter_stop}")
    assert args.iter_start == ['n:100']
    assert args.iter_stop == ['n:5000']
    print("  PASS")

    # Test: --max-n still works alongside --max
    args = p.parse_args(['--max', 'n:5000', '--max-n', '999'])
    print(f"  --max n:5000 --max-n 999 => iter_stop={args.iter_stop}, max_n={args.max_n}")
    assert args.iter_stop == ['n:5000']
    assert args.max_n == 999
    print("  PASS")

    # Test: mixing --min and --iter-start appends to same list
    args = p.parse_args(['--min', 'n:100', '--iter-start', 'm:50'])
    print(f"  --min n:100 --iter-start m:50 => iter_start={args.iter_start}")
    assert args.iter_start == ['n:100', 'm:50']
    print("  PASS")

    # Test: does --ma cause ambiguity?
    print("\n  Testing abbreviation --ma ...")
    try:
        args = p.parse_args(['--ma', 'n:5000'])
        print(f"  --ma n:5000 => MATCHED (iter_stop={args.iter_stop}, max_n={args.max_n}, max_m={args.max_m})")
    except SystemExit:
        print("  --ma n:5000 => AMBIGUOUS (argparse error, as expected)")

    print()


def test_single_dash_collision():
    """Test whether -m collides with -min (single-dash)."""
    print("=" * 60)
    print("TEST 2: Single-dash -min/-max collision with -m")
    print("=" * 60)

    p = argparse.ArgumentParser()
    p.add_argument('-min', '--iter-start', dest='iter_start', action='append')
    p.add_argument('-max', '--iter-stop', dest='iter_stop', action='append')
    p.add_argument('-m', '--max-m', type=int, default=10000)
    p.add_argument('-n', '--max-n', type=int, default=1000000)

    # Test: -min works?
    print("\n  Testing -min n:100 ...")
    try:
        args = p.parse_args(['-min', 'n:100'])
        print(f"  -min n:100 => iter_start={args.iter_start}")
        print("  PASS")
    except SystemExit as e:
        print(f"  -min n:100 => FAILED (argparse error)")

    # Test: -m 500 — does it match -m (max_m) or -min?
    print("\n  Testing -m 500 (should match --max-m, not -min)...")
    try:
        args = p.parse_args(['-m', '500'])
        print(f"  -m 500 => max_m={args.max_m}, iter_start={args.iter_start}")
        if args.max_m == 500:
            print("  PASS: -m correctly matched --max-m")
        else:
            print("  UNEXPECTED: -m matched something else")
    except SystemExit:
        print("  -m 500 => AMBIGUOUS or ERROR")

    # Test: -ma — does it collide?
    print("\n  Testing -ma n:5000 ...")
    try:
        args = p.parse_args(['-ma', 'n:5000'])
        print(f"  -ma n:5000 => iter_stop={args.iter_stop}")
    except SystemExit:
        print("  -ma n:5000 => FAILED/AMBIGUOUS")

    print()


def test_two_letter_short_flags():
    """Test two-letter short flags as a safe middle ground."""
    print("=" * 60)
    print("TEST 3: Two-letter short flags (-mn, -mx)")
    print("=" * 60)

    p = argparse.ArgumentParser()
    p.add_argument('-mn', '--min', '--iter-start', dest='iter_start', action='append')
    p.add_argument('-mx', '--max', '--iter-stop', dest='iter_stop', action='append')
    p.add_argument('--max-n', type=int, default=1000000)
    p.add_argument('--max-m', type=int, default=10000)

    args = p.parse_args(['-mn', 'n:100', '-mx', 'n:5000'])
    print(f"  -mn n:100 -mx n:5000 => iter_start={args.iter_start}, iter_stop={args.iter_stop}")
    assert args.iter_start == ['n:100']
    assert args.iter_stop == ['n:5000']
    print("  PASS")

    # --min and --max long forms
    args = p.parse_args(['--min', 'n:100', '--max', 'n:5000'])
    print(f"  --min n:100 --max n:5000 => iter_start={args.iter_start}, iter_stop={args.iter_stop}")
    assert args.iter_start == ['n:100']
    assert args.iter_stop == ['n:5000']
    print("  PASS")

    # --max-n still works
    args = p.parse_args(['--max-n', '999', '--max', 'n:5000'])
    print(f"  --max-n 999 --max n:5000 => max_n={args.max_n}, iter_stop={args.iter_stop}")
    assert args.max_n == 999
    assert args.iter_stop == ['n:5000']
    print("  PASS")

    print()


if __name__ == '__main__':
    test_double_dash_aliases()
    test_single_dash_collision()
    test_two_letter_short_flags()
    print("All tests complete.")
