#!/usr/bin/env python3
"""
Test runner for Prime-Square-Sum - runs all tests and provides coverage report.

Usage:
    python run_tests.py                 # Run all tests
    python run_tests.py -v              # Run with verbose output
    python run_tests.py --coverage      # Run with coverage report
    python run_tests.py test_gpu        # Run specific test module
    python run_tests.py --list          # List available tests
"""

import sys
import os
import unittest
import argparse
from pathlib import Path

# Add current directory to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def setup_test_environment():
    """Set up the test environment."""
    # Initialize GPU for tests that need it
    try:
        from utils import gpu as gpu_utils
        gpu_utils.init_gpu()
        if gpu_utils.GPU_AVAILABLE:
            print(f"GPU: {gpu_utils.GPU_INFO['name']}")
        else:
            print("GPU: Not available (CPU fallback will be tested)")
    except ImportError:
        print("GPU utilities not available")

    print("Test environment setup complete.\n")


def run_tests(test_pattern="test_*.py", verbosity=2, test_dir="tests"):
    """Run the unit tests."""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Get test files but exclude one-offs directory
    test_path = Path(test_dir)
    for test_file in test_path.glob(test_pattern):
        # Skip files in subdirectories like one-offs
        if test_file.parent == test_path:
            module_name = f"{test_dir}.{test_file.stem}"
            try:
                module = __import__(module_name, fromlist=[''])
                suite.addTests(loader.loadTestsFromModule(module))
            except ImportError as e:
                print(f"Warning: Could not import {module_name}: {e}")

    # Run tests
    runner = unittest.TextTestRunner(verbosity=verbosity)
    result = runner.run(suite)

    return result.wasSuccessful()


def run_with_coverage(test_pattern="test_*.py", test_dir="tests"):
    """Run tests with coverage reporting."""
    try:
        import coverage
    except ImportError:
        print("Coverage package not installed. Install with: pip install coverage")
        return False

    # Initialize coverage
    cov = coverage.Coverage(
        source=["utils"],
        omit=[
            "*/tests/*",
            "*/test_*.py",
            "*/__pycache__/*",
        ]
    )

    # Start coverage
    cov.start()

    # Run tests
    success = run_tests(test_pattern, verbosity=2, test_dir=test_dir)

    # Stop coverage
    cov.stop()
    cov.save()

    # Generate report
    print("\n" + "=" * 70)
    print("COVERAGE REPORT")
    print("=" * 70)
    cov.report()

    return success


def run_specific_test(test_name, verbosity=2):
    """Run a specific test module or test case."""
    loader = unittest.TestLoader()

    try:
        if '.' in test_name:
            # Full test path like test_gpu.TestCPUPowerSum.test_power2
            suite = loader.loadTestsFromName(f"tests.{test_name}")
        else:
            # Module name like test_gpu
            suite = loader.loadTestsFromModule(
                __import__(f"tests.{test_name}", fromlist=[''])
            )
    except (ImportError, AttributeError) as e:
        print(f"Error loading test '{test_name}': {e}")
        return False

    runner = unittest.TextTestRunner(verbosity=verbosity)
    result = runner.run(suite)

    return result.wasSuccessful()


def list_tests():
    """List all available test modules."""
    test_dir = Path("tests")
    test_files = sorted(test_dir.glob("test_*.py"))

    print("\nAvailable test modules:")
    print("-" * 40)
    for test_file in test_files:
        module_name = test_file.stem
        print(f"  {module_name}")

        try:
            module = __import__(f"tests.{module_name}", fromlist=[''])
            for name in dir(module):
                if name.startswith('Test'):
                    cls = getattr(module, name)
                    if isinstance(cls, type) and issubclass(cls, unittest.TestCase):
                        print(f"    - {name}")
        except ImportError:
            pass

    print("-" * 40)
    print("\nRun specific test with: python run_tests.py <test_name>")


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Run Prime-Square-Sum test suite",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  python run_tests.py                    # Run all tests
  python run_tests.py -v                 # Run with verbose output
  python run_tests.py --coverage         # Run with coverage report
  python run_tests.py test_gpu           # Run specific test module
  python run_tests.py --list             # List available tests
        """
    )

    parser.add_argument(
        "test",
        nargs="?",
        help="Specific test module or test case to run"
    )
    parser.add_argument(
        "-v", "--verbose",
        action="store_true",
        help="Verbose test output"
    )
    parser.add_argument(
        "--coverage",
        action="store_true",
        help="Run tests with coverage analysis"
    )
    parser.add_argument(
        "--list",
        action="store_true",
        help="List available test modules"
    )
    parser.add_argument(
        "--test-dir",
        default="tests",
        help="Directory containing test files (default: tests)"
    )

    args = parser.parse_args()

    # Setup test environment
    setup_test_environment()

    # List tests if requested
    if args.list:
        list_tests()
        return 0

    # Determine verbosity
    verbosity = 2 if args.verbose else 1

    # Run tests
    print("=" * 70)
    print("PRIME-SQUARE-SUM TEST SUITE")
    print("=" * 70)

    if args.test:
        print(f"\nRunning specific test: {args.test}")
        success = run_specific_test(args.test, verbosity)
    elif args.coverage:
        print("\nRunning tests with coverage analysis...")
        success = run_with_coverage(test_dir=args.test_dir)
    else:
        print("\nRunning all tests...")
        success = run_tests(verbosity=verbosity, test_dir=args.test_dir)

    # Report results
    print("\n" + "=" * 70)
    if success:
        print("ALL TESTS PASSED [OK]")
    else:
        print("SOME TESTS FAILED [FAIL]")
    print("=" * 70)

    return 0 if success else 1


if __name__ == "__main__":
    sys.exit(main())
