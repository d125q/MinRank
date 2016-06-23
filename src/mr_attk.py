#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Various algebraic attacks on the MinRank problem.

1) Kernel attack;
2) Groebner basis attack;
3) XL attack.

Example usage:
  >>> from mr_auth import MinRankInstance
  >>> MR = MinRankInstance(6, 5, 4, 3, 2)
  >>> A = MinRankAttack(MR)
  >>> A.run_groebner()
"""

from itertools import chain
from sage.all import *
from sage.rings.polynomial.multi_polynomial_sequence import *
from mr_util import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"


class MinRankAttack(object):
    """A class allowing the execution of various attacks on a MR instance.

    Attributes:
        MR: The MinRank instance associated to this object.
    """
    def __init__(self, MR):
        """Initialized a MinRankAttack object.

        Args:
            MR: The MinRank instance that we wish to attack.
        """
        self.__MR = MR

    @property
    def MR(self):
        """Returns the associated MinRank instance."""
        return self.__MR

    @MR.setter
    def MR(self, MR):
        """Updates the associated MinRank instance."""
        self.__MR = MR

    @staticmethod
    def __run_kernel(MR, constrained_run):
        vs = [var('y' + str(i)) for i in range(MR.m)]
        attempts = 0

        # Use this to ensure that the system is never underdetermined.
        determinedness = ceil(MR.m / MR.eta)

        while not constrained_run or attempts < q**(determinedness * MR.r):
            xs = [random_vector(MR.finite_field, MR.n)
                  for _ in range(determinedness)]
            lhs = matrix(MR.finite_field, MR.eta * determinedness, MR.m,
                         [expr.coefficient(v)
                          for exprs in [linear_combination(vs, MR.matrices) * x
                                        for x in xs]
                          for expr in exprs
                          for v in vs])
            rhs = vector(MR.finite_field,
                         chain(
                             *[(MR.offset_matrix * x).list()
                               for x in xs]
                         ))
            try:
                # The general solution is always of the form
                # particular + homogeneous.
                p_soln = lhs.solve_right(rhs)
                for h_soln in lhs.right_kernel():
                    # Check for correctness.
                    if (linear_combination(p_soln + h_soln, MR.matrices) -
                            MR.offset_matrix).rank() <= MR.r:
                        return p_soln + h_soln
            except ValueError:
                pass  # Ignore if system could not be solved.
            finally:
                attempts += 1

        return None  # Nothing could be found.

    def run_kernel(self, constrained_run=False):
        """Performs a kernel attack on MR (Courtois & Goubin).

        Repeatedly guesses vectors with hopes they fall into the nullspace.
        Under the assumption that they do, solve the corresponding linear
        system.

        Args:
            constrained_run: Run the attack only for a limited number of
                times (default False).

        Returns:
            A vector giving a solution to the MinRank instance.  If the
            constrained_run parameter is True, then the value is None in
            case no solution could be found.
        """
        return self.__run_kernel(self.__MR, constrained_run)

    @staticmethod
    def __generate_MQ_system(MR):
        """Generates an MQ system associated to a MR instance."""
        # Form the variable names.
        xs = ['x' + str(j) + '_' + str(i)
              for i in range(MR.r)
              for j in range(MR.n - MR.r)]
        ys = ['y_' + str(i) for i in range(MR.m)]

        # Create the lex-ordered polynomial ring GF(q)[vars].
        R = PolynomialRing(MR.finite_field, names=(xs + ys))
        vs = R.gens()
        xs = vs[:(MR.r * (MR.n - MR.r))]
        ys = vs[(MR.r * (MR.n - MR.r)):]

        # Form the matrices.
        lhs = linear_combination(ys, MR.matrices) - MR.offset_matrix
        rhs = matrix(R, MR.n, MR.n - MR.r,
                     chain(
                         identity_matrix(R, MR.n - MR.r).list(),
                         list(xs)
                     ))

        # Return the system and the corresponding polynomial ring.
        return lhs * rhs, R

    def run_groebner(self):
        """Attacks MR by computing a Groebner basis (Kipnis & Shamir).

        Forms a multivariate quadratic (MQ) system corresponding to a MinRank
        instance.  Attempts to solve the system using built-in Sage functions.

        Returns:
            A solution to the MQ system giving a solution to the MR instance
            at the same time.

        Raises:
            AssertionError: The generated ideal is not radical.
        """
        # Form the system.
        system, R = self.__generate_MQ_system(self.__MR)
        PS = PolynomialSequence(system, R)

        # Maybe we can fix some variables and still expect a solution?
        delta = (self.__MR.r - self.__MR.eta) * (self.__MR.n - self.__MR.r) + \
            self.__MR.m
        if delta > 0:
            PS = PS.subs({v: 0 for v in R.gens()[:delta]})

        # Form the ideal, making sure everything's OK.  The field equations
        # are added to the ideal to make sure that it is radical.
        I = R.ideal(*PS) + \
            sage.rings.ideal.FieldIdeal(R)

        # assert I.dimension() in (-1, 0)
        assert I.radical() == I

        # R is a lex-ordered polynomial ring.  What the FGLM algorithm
        # does is it computes a Groebner basis with respect to a degrevlex
        # ordering and then converts it back to lex.
        I = R.ideal(I.groebner_basis(algorithm='libsingular:stdfglm'))

        # Return the affine variety.  This should be computationally cheap
        # since the ideal is generated by a lex Groebner basis.  Furthermore,
        # note that the previous addition of the field equations does not
        # change the affine variety whatsoever.
        return I.variety(I.base_ring())

    @staticmethod
    def __run_xl(PS, D):
        def generate_monomials(R, deg):
            """Generates all monomials over R of a given degree."""
            return [R({tuple(degs): 1})
                    for degs in WeightedIntegerVectors(
                            deg, [1 for _ in range(R.ngens())]
                    )]

        def solve(PS, offset=0, soln=None):
            """Tries to solve the system after it has been run through XL."""
            if soln is None:
                soln = {}

            if len(soln) == PS.ring().ngens():  # Found a solution.
                return soln

            for i in range(offset, len(PS)):
                PS = PS.subs(soln)  # Substitute what we have so far.
                if PS[i].is_constant():
                    if PS[i] == 0:  # 0 == 0.  OK.
                        continue
                    else:  # Inconsistent.
                        return None

                if not PS[i].is_univariate():  # Multivariate.
                    continue

                # Found an univaraite polynomial.  Find its roots.
                roots = PS[i].univariate_polynomial().roots(
                    multiplicities=False
                )

                for root in roots:  # Try to solve for each root.
                    new_soln = soln.copy()
                    new_soln[PS[i].variable(0)] = root
                    result = solve(PS, soln=new_soln)

                    if result is not None:
                        return result

            return None  # Found nothing.

        # Do the eXtended Linearization (XL) step.
        PS = PolynomialSequence(
            PS.ring().change_ring(order='lex'),  # Ensure lex ordering.
            chain(
                [m * p
                 for p in PS
                 for m in generate_monomials(PS.ring(), D - 2)],
                PS
            )
        )
        # Do the Gaussian elimination step.
        A, v = PS.coefficient_matrix(sparse=False)
        PS = PolynomialSequence(A.echelon_form() * v)
        # Solve.
        return solve(PS, offset=A.nrows() - A.rank())

    def run_xl(self, D):
        """Attacks MR by using the XL algorithm (Courtois et al).

        Args:
            D: The degree parameter (>= 2) used in the linearization.

        Raises:
            AssertionError: Invalid degree parameter.
        """
        assert D >= 2
        system, R = self.__generate_MQ_system(self.__MR)
        return self.__run_xl(PolynomialSequence(R, system), D)

    def __str__(self):
        """Pretty printing."""
        return "MinRankAttack object.  Associated MR instance: " + \
            str(self.__MR) + "."
