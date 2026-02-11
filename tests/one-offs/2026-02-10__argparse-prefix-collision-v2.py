"""
Test: Can -min, -max, and -m all coexist without collision?

Verifies that argparse exact-matching prevents -m from being
swallowed by -min or -max, leaving -m free for other purposes.
"""
import argparse
import sys


def build_parser():
    """Build a parser mimicking our planned CLI layout."""
    p = argparse.ArgumentParser()

    # New unified bounds: -min/-max as short forms of --iter-start/--iter-stop
    p.add_argument('-min', '--min', '--iter-start', dest='iter_start',
                   action='append', metavar='VAR:VALUE',
                   help='Set minimum (start) value for variable')
    p.add_argument('-max', '--max', '--iter-stop', dest='iter_stop',
                   action='append', metavar='VAR:VALUE',
                   help='Set maximum (stop) value for variable')

    # Legacy convenience flags (to be deprecated later)
    p.add_argument('--max-n', type=int, default=1000000)
    p.add_argument('--max-m', type=int, default=10000)

    # -m reserved for something else (using --version-string as dummy)
    p.add_argument('-m', '--mock-flag', type=str, default=None,
                   help='Dummy flag to prove -m is independent')

    # -e for --expr (already exists in real CLI)
    p.add_argument('-e', '--expr', type=str, default=None)

    return p


def run_test(label, argv, checks):
    """Run a parse test and validate expectations."""
    p = build_parser()
    try:
        args = p.parse_args(argv)
        results = []
        all_pass = True
        for desc, actual, expected in checks(args):
            ok = actual == expected
            status = "PASS" if ok else "FAIL"
            results.append(f"    {status}: {desc} (got {actual!r}, expected {expected!r})")
            if not ok:
                all_pass = False
        print(f"  [{('PASS' if all_pass else 'FAIL')}] {label}")
        for r in results:
            print(r)
        return all_pass
    except SystemExit:
        print(f"  [FAIL] {label}")
        print(f"    argparse rejected: {' '.join(argv)}")
        return False


def main():
    print("=" * 65)
    print("Argparse coexistence: -min, -max, -m, --max-n, --max-m")
    print("=" * 65)
    print()

    results = []

    # 1. -min works
    results.append(run_test(
        "-min n:100 sets iter_start",
        ['-min', 'n:100'],
        lambda a: [("iter_start", a.iter_start, ['n:100']),
                    ("mock_flag", a.mock_flag, None)]
    ))

    # 2. -max works
    results.append(run_test(
        "-max n:5000 sets iter_stop",
        ['-max', 'n:5000'],
        lambda a: [("iter_stop", a.iter_stop, ['n:5000']),
                    ("mock_flag", a.mock_flag, None)]
    ))

    # 3. -m is independent (does NOT collide with -min or -max)
    results.append(run_test(
        "-m 'hello' sets mock_flag, not iter_start/stop",
        ['-m', 'hello'],
        lambda a: [("mock_flag", a.mock_flag, 'hello'),
                    ("iter_start", a.iter_start, None),
                    ("iter_stop", a.iter_stop, None)]
    ))

    # 4. All three simultaneously
    results.append(run_test(
        "-min n:100 -max n:5000 -m 'test' all coexist",
        ['-min', 'n:100', '-max', 'n:5000', '-m', 'test'],
        lambda a: [("iter_start", a.iter_start, ['n:100']),
                    ("iter_stop", a.iter_stop, ['n:5000']),
                    ("mock_flag", a.mock_flag, 'test')]
    ))

    # 5. --min long form also works
    results.append(run_test(
        "--min n:100 (double-dash) same dest as -min",
        ['--min', 'n:100'],
        lambda a: [("iter_start", a.iter_start, ['n:100'])]
    ))

    # 6. --iter-start long form also works
    results.append(run_test(
        "--iter-start n:100 (original long form) same dest",
        ['--iter-start', 'n:100'],
        lambda a: [("iter_start", a.iter_start, ['n:100'])]
    ))

    # 7. Mix -min and --iter-start (append to same list)
    results.append(run_test(
        "-min n:100 --iter-start m:50 both append to iter_start",
        ['-min', 'n:100', '--iter-start', 'm:50'],
        lambda a: [("iter_start", a.iter_start, ['n:100', 'm:50'])]
    ))

    # 8. --max-n coexists with -max
    results.append(run_test(
        "--max-n 999 and -max n:5000 coexist (different dests)",
        ['--max-n', '999', '-max', 'n:5000'],
        lambda a: [("max_n", a.max_n, 999),
                    ("iter_stop", a.iter_stop, ['n:5000'])]
    ))

    # 9. Multiple -min appends
    results.append(run_test(
        "-min n:100 -min m:50 appends both",
        ['-min', 'n:100', '-min', 'm:50'],
        lambda a: [("iter_start", a.iter_start, ['n:100', 'm:50'])]
    ))

    # 10. -e for --expr still works alongside everything
    results.append(run_test(
        "-e 'does_exist tri(n)==666' -min n:1 -max n:100 -m debug",
        ['-e', 'does_exist tri(n)==666', '-min', 'n:1', '-max', 'n:100', '-m', 'debug'],
        lambda a: [("expr", a.expr, 'does_exist tri(n)==666'),
                    ("iter_start", a.iter_start, ['n:1']),
                    ("iter_stop", a.iter_stop, ['n:100']),
                    ("mock_flag", a.mock_flag, 'debug')]
    ))

    # 11. Abbreviation -ma -- should be AMBIGUOUS
    print()
    print("  Edge case: abbreviation -ma (expected: ambiguous)")
    p = build_parser()
    try:
        p.parse_args(['-ma', 'n:5000'])
        print("  [INFO] -ma was accepted (matched something)")
    except SystemExit:
        print("  [INFO] -ma was rejected (ambiguous, as expected)")

    # 12. Abbreviation -mi -- should match -min or be ambiguous?
    print()
    print("  Edge case: abbreviation -mi (does it match -min?)")
    p = build_parser()
    try:
        args = p.parse_args(['-mi', 'n:100'])
        print(f"  [INFO] -mi was accepted: iter_start={args.iter_start}")
    except SystemExit:
        print("  [INFO] -mi was rejected (ambiguous or unrecognized)")

    print()
    passed = sum(results)
    total = len(results)
    print(f"Results: {passed}/{total} passed")
    if passed == total:
        print("ALL CLEAR: -min, -max, and -m coexist without collision.")
    else:
        print("ISSUES FOUND - see failures above.")


if __name__ == '__main__':
    main()
