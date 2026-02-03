"""
prime_io.py - Prime number I/O utilities
=========================================

Supports multiple formats for loading and saving prime numbers:
- NumPy binary (.npy) - fastest, recommended
- Pickle (.pkl, .dat) - backward compatible with original code
- Text (.txt) - human readable

Usage:
    from utils.prime_io import load_primes, save_primes

    # Load from any supported format
    primes = load_primes("primes.npy")
    primes = load_primes("legacy.dat")  # pickle format

    # Save in numpy format (recommended)
    save_primes(primes, "primes.npy")
"""

import numpy as np
from pathlib import Path
from typing import Union, Optional, List
import pickle
import warnings


def load_primes(filepath: Union[str, Path]) -> np.ndarray:
    """
    Load primes from file (auto-detects format).

    Supported formats:
        .npy - NumPy binary (fastest)
        .npz - NumPy compressed
        .pkl, .pickle, .dat - Python pickle (legacy)
        .txt, .csv - Text (one prime per line)

    Args:
        filepath: Path to prime file

    Returns:
        numpy array of primes (int64)

    Example:
        >>> primes = load_primes("primes.npy")
        >>> primes = load_primes("legacy.dat")  # pickle from original code
    """
    filepath = Path(filepath)

    if not filepath.exists():
        raise FileNotFoundError(f"Prime file not found: {filepath}")

    suffix = filepath.suffix.lower()

    if suffix == '.npy':
        return _load_numpy(filepath)
    elif suffix == '.npz':
        return _load_numpy_compressed(filepath)
    elif suffix in ('.pkl', '.pickle', '.dat'):
        return _load_pickle(filepath)
    elif suffix in ('.txt', '.csv'):
        return _load_text(filepath)
    else:
        # Try to auto-detect
        try:
            return _load_numpy(filepath)
        except Exception:
            try:
                return _load_pickle(filepath)
            except Exception:
                return _load_text(filepath)


def save_primes(primes: np.ndarray, filepath: Union[str, Path],
                format: Optional[str] = None) -> None:
    """
    Save primes to file.

    Args:
        primes: numpy array of primes
        filepath: Output path
        format: Force format ('npy', 'npz', 'pkl', 'txt'), or None to auto-detect

    Example:
        >>> save_primes(primes, "output.npy")
        >>> save_primes(primes, "output.dat", format='pkl')
    """
    filepath = Path(filepath)
    suffix = filepath.suffix.lower()

    if format:
        suffix = f'.{format}'

    primes = np.asarray(primes, dtype=np.int64)

    if suffix == '.npy':
        np.save(filepath, primes)
    elif suffix == '.npz':
        np.savez_compressed(filepath, primes=primes)
    elif suffix in ('.pkl', '.pickle', '.dat'):
        with open(filepath, 'wb') as f:
            pickle.dump(primes.tolist(), f, protocol=pickle.HIGHEST_PROTOCOL)
    elif suffix in ('.txt', '.csv'):
        np.savetxt(filepath, primes, fmt='%d')
    else:
        # Default to numpy
        np.save(filepath, primes)


def load_primes_range(filepath: Union[str, Path],
                      start_idx: int, end_idx: int) -> np.ndarray:
    """
    Load a range of primes from file.

    For numpy files, this is memory-efficient (uses memmap).
    For other formats, loads full file then slices.

    Args:
        filepath: Path to prime file
        start_idx: Start index (inclusive)
        end_idx: End index (exclusive)

    Returns:
        numpy array of primes[start_idx:end_idx]
    """
    filepath = Path(filepath)
    suffix = filepath.suffix.lower()

    if suffix == '.npy':
        # Memory-mapped loading - only reads what we need
        primes = np.load(filepath, mmap_mode='r')
        return np.array(primes[start_idx:end_idx], dtype=np.int64)
    else:
        # Load full file and slice
        primes = load_primes(filepath)
        return primes[start_idx:end_idx]


def convert_pickle_to_numpy(pickle_path: Union[str, Path],
                            numpy_path: Union[str, Path]) -> int:
    """
    Convert legacy pickle file to numpy format.

    The original prime-square-sum.py used pickle files that may contain
    multiple pickled chunks. This function handles that format.

    Args:
        pickle_path: Path to pickle file
        numpy_path: Output path for numpy file

    Returns:
        Number of primes converted
    """
    primes = _load_pickle(pickle_path)
    save_primes(primes, numpy_path)
    return len(primes)


def _load_numpy(filepath: Path) -> np.ndarray:
    """Load from numpy binary format."""
    return np.load(filepath).astype(np.int64)


def _load_numpy_compressed(filepath: Path) -> np.ndarray:
    """Load from numpy compressed format."""
    data = np.load(filepath)
    # Handle both single array and named array
    if isinstance(data, np.ndarray):
        return data.astype(np.int64)
    else:
        # npz file - get first array
        key = list(data.keys())[0]
        return data[key].astype(np.int64)


def _load_pickle(filepath: Path) -> np.ndarray:
    """
    Load from pickle format (backward compatible with original code).

    The original code could write multiple pickle chunks to one file,
    so we handle that case.
    """
    primes = []

    with open(filepath, 'rb') as f:
        while True:
            try:
                chunk = pickle.load(f)
                if isinstance(chunk, list):
                    primes.extend(chunk)
                elif isinstance(chunk, np.ndarray):
                    primes.extend(chunk.tolist())
                else:
                    primes.append(int(chunk))
            except EOFError:
                break
            except Exception as e:
                warnings.warn(f"Error reading pickle chunk: {e}")
                break

    return np.array(primes, dtype=np.int64)


def _load_text(filepath: Path) -> np.ndarray:
    """
    Load from text format (one prime per line, or whitespace separated).
    """
    primes = []

    with open(filepath, 'r') as f:
        for line in f:
            # Skip header lines or comments
            line = line.strip()
            if not line or line.startswith('#'):
                continue

            # Handle both single value and multiple values per line
            for token in line.split():
                try:
                    primes.append(int(token))
                except ValueError:
                    continue

    return np.array(primes, dtype=np.int64)


# Verification
if __name__ == "__main__":
    import tempfile
    import os

    # Create test primes
    test_primes = np.array([2, 3, 5, 7, 11, 13, 17, 19, 23, 29], dtype=np.int64)

    with tempfile.TemporaryDirectory() as tmpdir:
        # Test numpy format
        npy_path = os.path.join(tmpdir, "test.npy")
        save_primes(test_primes, npy_path)
        loaded = load_primes(npy_path)
        assert np.array_equal(test_primes, loaded), "NumPy round-trip failed"
        print(f"NumPy format: OK")

        # Test pickle format
        pkl_path = os.path.join(tmpdir, "test.pkl")
        save_primes(test_primes, pkl_path)
        loaded = load_primes(pkl_path)
        assert np.array_equal(test_primes, loaded), "Pickle round-trip failed"
        print(f"Pickle format: OK")

        # Test text format
        txt_path = os.path.join(tmpdir, "test.txt")
        save_primes(test_primes, txt_path)
        loaded = load_primes(txt_path)
        assert np.array_equal(test_primes, loaded), "Text round-trip failed"
        print(f"Text format: OK")

        # Test range loading
        range_loaded = load_primes_range(npy_path, 2, 5)
        assert np.array_equal(test_primes[2:5], range_loaded), "Range load failed"
        print(f"Range loading: OK")

    print("\nAll I/O tests passed!")
