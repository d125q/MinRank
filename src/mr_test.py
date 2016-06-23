#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Sample tests for the MinRank implementation."""

from mr_auth import *
from mr_attk import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Seed for reproducibility.
set_random_seed(17)

if __name__ == "__main__":
    # Parameters for challenge set A.
    m = 10
    eta = 6
    n = 6
    r = 3
    q = 65521

    MR = MinRankInstance(m, eta, n, r, q)
    print("Trying out authentication with challenge set A parameters.")

    V = Verifier(MR)
    P = Prover(MR)
    LP = LegitimateProver(MR)
    MR.give_access(LP)

    print("Illegitimate prover goes first.")
    authentication_driver(P, V)

    print("Legitimate prover next.")
    authentication_driver(LP, V)

    # Small instance parameters.
    m = 4
    eta = n = 6
    r = 3
    q = 3

    MR = MinRankInstance(m, eta, n, r, q)
    A = MinRankAttack(MR)
    print("Trying out the Groebner basis attack on a small instance.\n"
          "The y_i's are the solution.")
    print(A.run_groebner())

    print("Trying out the kernel attack on the same instance.")
    print(A.run_kernel())
