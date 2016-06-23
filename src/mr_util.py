#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Various utilities used throughout the MinRank implementation."""

import hashlib
from sage.all import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"


def linear_combination(coeffs, elems):
    """Calculates a linear combination of elements given coefficients.

    Args:
        alpha: The coefficients.
        elems: The elements to combine.

    Returns:
        The linear combination of all elements given the coefficients.
    """
    return sum([coeff * elem for coeff, elem in zip(coeffs, elems)])


def random_full_rank_matrix(ring, nrows, ncols=None):
    """Generates a random, full-rank matrix over a specified ring.

    Args:
        ring: The ring over which to generate the matrix.
        nrows: The number of rows.
        ncols: The number of columns (if missing, matrix is made square).

    Returns:
        A random, full-rank matrix over a specified ring.
    """
    if ncols is None:
        ncols = nrows

    return random_matrix(ring, nrows, ncols,
                         algorithm='echelonizable',
                         rank=min(nrows, ncols))


def sha256_hash(obj):
    """Calculates a SHA256 digest of a Python object's representation.

    Args:
        obj: The object whose digest is to be calculated.

    Returns:
        The SHA256 digest of the object.
    """
    try:  # Use the str method on Sage objects if possible.
        return hashlib.sha256(obj.str()).digest()
    except:  # Else, fall back to the default repr function.
        return hashlib.sha256(repr(obj)).digest()
