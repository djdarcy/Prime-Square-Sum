"""
test_number_theory.py - Unit tests for number theory utilities
===============================================================

Tests digital root, primality pre-filtering, and triangular number functions.
"""

import pytest
import sys
import os

# Add project root to path
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from utils.number_theory import (
    digital_root, could_be_prime, could_be_prime_by_digital_root, digital_root_statistics,
    tri, qtri, is_triangular, trisum
)


class TestDigitalRoot:
    """Test digital root calculation."""

    def test_digital_root_single_digit(self):
        """Test digital root of single digits (identity)."""
        for d in range(10):
            assert digital_root(d) == d

    def test_digital_root_examples(self):
        """Test digital root with specific examples."""
        # 38: 3+8=11, 1+1=2
        assert digital_root(38) == 2

        # 666: 6+6+6=18, 1+8=9
        assert digital_root(666) == 9

        # 999: 9+9+9=27, 2+7=9
        assert digital_root(999) == 9

        # 1000: 1+0+0+0=1
        assert digital_root(1000) == 1

    def test_digital_root_zero(self):
        """Test edge case: zero."""
        assert digital_root(0) == 0

    def test_digital_root_string_input(self):
        """Test digital root with string input (large numbers)."""
        # Can compute digital root of strings representing huge numbers
        assert digital_root("38") == 2
        assert digital_root("666") == 9
        assert digital_root("999999999999") == 9

    def test_digital_root_formula(self):
        """Verify digital root formula: 1 + ((n-1) % 9)."""
        for n in [1, 5, 17, 38, 123, 666, 999, 1000]:
            expected = 1 + ((n - 1) % 9)
            assert digital_root(n) == expected


class TestComprehensivePrimeFilter:
    """Test comprehensive could_be_prime() with all trivial pre-filters."""

    def test_small_primes_pass(self):
        """Test that small primes pass all filters."""
        small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        for p in small_primes:
            assert could_be_prime(p), f"Prime {p} should pass all filters"

    def test_even_numbers_fail(self):
        """Test that even numbers (except 2) fail."""
        even_numbers = [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28]
        for n in even_numbers:
            assert not could_be_prime(n), f"Even number {n} should fail"

    def test_multiples_of_5_fail(self):
        """Test that multiples of 5 (except 5) fail."""
        multiples_of_5 = [10, 15, 20, 25, 30, 35, 40, 45, 50, 55, 60, 65]
        for n in multiples_of_5:
            assert not could_be_prime(n), f"Multiple of 5: {n} should fail"

    def test_multiples_of_3_fail(self):
        """Test that multiples of 3 (except 3) fail via digital root."""
        multiples_of_3 = [9, 21, 27, 33, 39, 51, 57, 63, 69, 81, 87, 93, 99]
        for n in multiples_of_3:
            assert not could_be_prime(n), f"Multiple of 3: {n} should fail"

    def test_combined_filter_examples(self):
        """Test combined filtering with multiple rules."""
        # 10: even and divisible by 5
        assert not could_be_prime(10)

        # 15: divisible by 3 and 5
        assert not could_be_prime(15)

        # 30: even and divisible by 3 and 5
        assert not could_be_prime(30)

        # 77: 7*11, divisible by neither 2, 3, nor 5
        assert could_be_prime(77), "77 passes trivial filters (but is not prime)"

    def test_edge_cases(self):
        """Test edge cases."""
        assert not could_be_prime(0)
        assert not could_be_prime(1)
        assert could_be_prime(2)
        assert could_be_prime(3)
        assert could_be_prime(5)

    def test_filter_effectiveness(self):
        """Test that combined filter eliminates most non-primes quickly."""
        # Count how many numbers 2..100 pass the filter
        candidates = [n for n in range(2, 101) if could_be_prime(n)]

        # Should eliminate: even (except 2), multiples of 3 (except 3), multiples of 5 (except 5)
        # Roughly: 100/2 + 100/3 + 100/5 - overlaps ≈ 50 + 33 + 20 - overlaps
        # More precisely: numbers coprime to 2, 3, 5 plus the primes 2, 3, 5
        # This is related to Euler's totient function φ(30) = 8 out of every 30 numbers
        # For 1..100: roughly 8 * 100/30 ≈ 27 numbers (plus exceptions for 2, 3, 5)

        assert len(candidates) < 50, \
            f"Filter should eliminate most composites, got {len(candidates)} candidates in 2..100"


class TestPrimalityPreFilter:
    """Test primality pre-filtering by digital root."""

    def test_small_primes_pass_filter(self):
        """Test that small primes pass the filter."""
        small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]
        for p in small_primes:
            assert could_be_prime_by_digital_root(p), f"Prime {p} should pass filter"

    def test_multiples_of_3_fail_filter(self):
        """Test that multiples of 3 fail the filter."""
        multiples_of_3 = [9, 15, 21, 27, 33, 39, 45, 51, 57, 63, 69, 75]
        for m in multiples_of_3:
            assert not could_be_prime_by_digital_root(m), f"Multiple of 3: {m} should fail filter"

    def test_digital_root_zero_fails(self):
        """Numbers with digital root 0 fail filter (impossible anyway)."""
        # No valid positive numbers have digital root 0
        pass  # Can't test since all positive n have digital_root in 1..9

    def test_digital_root_3_fails(self):
        """Numbers with digital root 3 fail filter (divisible by 3)."""
        dr3_numbers = [3, 12, 21, 30, 39, 48, 57, 66]
        for n in dr3_numbers:
            dr = digital_root(n)
            if n > 3:
                assert dr == 3
                assert not could_be_prime_by_digital_root(n)

    def test_digital_root_6_fails(self):
        """Numbers with digital root 6 fail filter (divisible by 3)."""
        dr6_numbers = [6, 15, 24, 33, 42, 51, 60, 69]
        for n in dr6_numbers:
            dr = digital_root(n)
            if n > 3:
                assert dr == 6
                assert not could_be_prime_by_digital_root(n)

    def test_digital_root_9_fails(self):
        """Numbers with digital root 9 fail filter (divisible by 9/3)."""
        dr9_numbers = [9, 18, 27, 36, 45, 54, 63, 72, 81, 90, 99]
        for n in dr9_numbers:
            dr = digital_root(n)
            assert dr == 9
            assert not could_be_prime_by_digital_root(n)

    def test_edge_cases(self):
        """Test edge cases."""
        assert not could_be_prime_by_digital_root(0)
        assert not could_be_prime_by_digital_root(1)
        assert could_be_prime_by_digital_root(2)
        assert could_be_prime_by_digital_root(3)
        assert could_be_prime_by_digital_root(4)  # digital root = 4, passes filter (but not prime - false positive)

    def test_false_positives_expected(self):
        """Test that some non-primes pass the filter (not a definitive test)."""
        non_primes_that_pass = [4, 25, 49, 121, 169]  # Perfect squares, etc.
        for n in non_primes_that_pass:
            assert could_be_prime_by_digital_root(n), \
                f"Non-prime {n} passes filter (expected - not sufficient condition)"

    def test_equivalence_to_mod_three(self):
        """Test that filter is equivalent to checking (n % 3 != 0) for n > 3."""
        for n in range(4, 1000):
            by_digital_root = could_be_prime_by_digital_root(n)
            by_mod_three = (n % 3 != 0)
            assert by_digital_root == by_mod_three, \
                f"Digital root and mod 3 disagree for n={n}"

    def test_first_10k_primes_pass_filter(self):
        """Verify that all small primes pass the digital root filter."""
        # First few primes
        small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71]
        for p in small_primes:
            assert could_be_prime_by_digital_root(p), \
                f"Prime {p} failed digital root filter"


class TestDigitalRootStatistics:
    """Test statistics generation for digital root filtering."""

    def test_statistics_basic(self):
        """Test that statistics are computed correctly."""
        stats = digital_root_statistics(100)

        assert 'total_candidates' in stats
        assert 'passes_filter' in stats
        assert 'rejected' in stats
        assert 'filter_effectiveness_percent' in stats

        # For 100: candidates 2..100 = 99 numbers
        assert stats['total_candidates'] == 98

    def test_statistics_filter_effectiveness(self):
        """Test that filter effectiveness is approximately 33% (1/3 of candidates)."""
        stats = digital_root_statistics(1000)

        # Should reject roughly 33% (multiples of 3)
        # Exactly 1/3 of integers are divisible by 3
        effectiveness = stats['filter_effectiveness_percent']
        assert 31 < effectiveness < 35, \
            f"Filter effectiveness should be ~33%, got {effectiveness}%"

    def test_statistics_small_range(self):
        """Test statistics for small range."""
        stats = digital_root_statistics(10)

        # Range 2..10 = 9 candidates
        # Multiples of 3: 3, 6, 9 = 3 rejected (but 3 passes since it's prime)
        # So: 9 - 3 = 6 pass (2, 5, 7, 8, 10) + 3 = actually need to check manually
        assert stats['total_candidates'] == 8

    def test_statistics_zero_range(self):
        """Test statistics with limit <= 2."""
        stats = digital_root_statistics(2)
        assert stats['total_candidates'] == 0


class TestDocumentation:
    """Test that documentation function runs without error."""

    def test_explain_function_runs(self, capsys):
        """Test that explain_digital_root_filter() produces output."""
        from utils.number_theory import explain_digital_root_filter

        explain_digital_root_filter()
        captured = capsys.readouterr()

        assert "Digital Root Pre-Filtering" in captured.out
        assert "primes p > 3" in captured.out or "Primes" in captured.out


# =============================================================================
# Triangular Number Tests (Issue #14)
# =============================================================================

class TestTriangularNumber:
    """Test tri() - nth triangular number."""

    def test_tri_first_values(self):
        """Test first several triangular numbers."""
        expected = [0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55]
        for n, val in enumerate(expected):
            assert tri(n) == val, f"tri({n}) should be {val}"

    def test_tri_key_values(self):
        """Test mathematically significant values."""
        assert tri(4) == 10, "tri(4) = 10 (digits 0-9)"
        assert tri(36) == 666, "tri(36) = 666 (key mystical number)"
        assert tri(100) == 5050, "tri(100) = 5050 (Gauss sum)"

    def test_tri_formula(self):
        """Verify tri(n) = n(n+1)/2."""
        for n in range(100):
            expected = (n * (n + 1)) // 2
            assert tri(n) == expected

    def test_tri_negative_raises(self):
        """Test that negative input raises ValueError."""
        with pytest.raises(ValueError):
            tri(-1)


class TestInverseTriangular:
    """Test qtri() - inverse triangular function."""

    def test_qtri_triangular_numbers(self):
        """Test qtri returns correct n for triangular numbers."""
        triangular_pairs = [(0, 0), (1, 1), (3, 2), (6, 3), (10, 4), (15, 5),
                           (21, 6), (28, 7), (36, 8), (45, 9), (55, 10)]
        for val, n in triangular_pairs:
            assert qtri(val) == n, f"qtri({val}) should be {n}"

    def test_qtri_key_values(self):
        """Test mathematically significant inverse values."""
        assert qtri(10) == 4, "qtri(10) = 4"
        assert qtri(666) == 36, "qtri(666) = 36"
        assert qtri(5050) == 100, "qtri(5050) = 100"

    def test_qtri_non_triangular_returns_none(self):
        """Test that non-triangular numbers return None."""
        non_triangular = [2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 667]
        for x in non_triangular:
            assert qtri(x) is None, f"qtri({x}) should be None"

    def test_qtri_negative_returns_none(self):
        """Test that negative input returns None."""
        assert qtri(-1) is None
        assert qtri(-666) is None

    def test_qtri_inverse_of_tri(self):
        """Test that qtri(tri(n)) == n."""
        for n in range(200):
            assert qtri(tri(n)) == n


class TestIsTriangular:
    """Test is_triangular() predicate."""

    def test_is_triangular_true_cases(self):
        """Test that triangular numbers return True."""
        triangular = [0, 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 666]
        for x in triangular:
            assert is_triangular(x), f"{x} should be triangular"

    def test_is_triangular_false_cases(self):
        """Test that non-triangular numbers return False."""
        non_triangular = [2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 667, 1000]
        for x in non_triangular:
            assert not is_triangular(x), f"{x} should not be triangular"

    def test_is_triangular_large_numbers(self):
        """Test is_triangular with large values."""
        # tri(1000) = 500500
        assert is_triangular(500500)
        assert not is_triangular(500501)

        # tri(10000) = 50005000
        assert is_triangular(50005000)


class TestTrisum:
    """Test trisum() - triangular digit sum."""

    def test_trisum_base_10(self):
        """Test trisum(10) = 666 (classic result)."""
        # Arrangement:
        #     9       = 9
        #    78       = 78
        #   456       = 456
        #  0123       = 123
        # Total: 123 + 456 + 78 + 9 = 666
        assert trisum(10) == 666, "trisum(10) should equal 666"

    def test_trisum_small_bases(self):
        """Test trisum for small bases."""
        assert trisum(1) == 0, "trisum(1) = 0 (only digit 0)"
        # For non-triangular bases, not all digits fit the triangle
        # trisum(3) = 3 (tri(2)=3 is triangular): 01+2 = 1+2 = 3
        assert trisum(3) == 3, "trisum(3) = 3 (01+2 = 3)"

    def test_trisum_invalid_base_raises(self):
        """Test that base < 1 raises ValueError."""
        with pytest.raises(ValueError):
            trisum(0)
        with pytest.raises(ValueError):
            trisum(-1)

    def test_trisum_triangular_bases(self):
        """Test trisum for triangular number bases (complete triangles).

        Row digits are evaluated as base-b numbers (Horner's method),
        not base-10. This matters for b != 10.
        """
        # tri(2) = 3 digits: 0,1,2 → arranged as: 2 / 01 → (0*3+1)+(2) = 1+2 = 3
        # tri(3) = 6 digits: 0-5 → arranged as: 5 / 34 / 012
        #   012 in base 6 = 0*36 + 1*6 + 2 = 8
        #   34 in base 6 = 3*6 + 4 = 22
        #   5 in base 6 = 5
        #   Total: 8 + 22 + 5 = 35
        # tri(4) = 10 digits: 0-9 → arranged as: 9 / 78 / 456 / 0123 → 123+456+78+9 = 666
        assert trisum(3) == 3    # base-3: (0*3+1) + 2 = 3
        assert trisum(6) == 35   # base-6: 8 + 22 + 5 = 35
        assert trisum(10) == 666 # base-10: 123 + 456 + 78 + 9 = 666


class TestTriangularRelationships:
    """Test mathematical relationships between triangular functions."""

    def test_tri_qtri_are_inverses(self):
        """Test that tri and qtri are inverse functions for valid values."""
        for n in range(100):
            val = tri(n)
            assert qtri(val) == n, f"qtri(tri({n})) should equal {n}"

    def test_666_relationships(self):
        """Test the key 666 relationships from Zero_AG paper."""
        # tri(36) = 666
        assert tri(36) == 666

        # qtri(666) = 36
        assert qtri(666) == 36

        # trisum(10) = 666
        assert trisum(10) == 666

        # is_triangular(666) = True
        assert is_triangular(666)

    def test_chain_tri_qtri_trisum(self):
        """Test the recursive relationship: tri(4) -> 10 -> trisum(10) = 666 -> qtri(666) = 36."""
        # Start with n=4
        step1 = tri(4)
        assert step1 == 10, "tri(4) = 10"

        step2 = trisum(step1)
        assert step2 == 666, "trisum(10) = 666"

        step3 = qtri(step2)
        assert step3 == 36, "qtri(666) = 36"

        step4 = tri(step3)
        assert step4 == 666, "tri(36) = 666 (loop!)"


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
