#!/usr/bin/env sage -python
# -*- coding: utf-8 -*-

"""Zero-knowledge authentication protocol based on MinRank.

This file provides a toy implementation of a zero-knowledge authentication
protocol based on the MinRank problem from linear algebra.  It is written
as coursework at the Faculty of Computer Science and Engineering in
Skopje, Republic of Macedonia.  The protocol was proposed by
Nicolas T. Courtois; see https://eprint.iacr.org/2001/058.pdf for details.

Example usage:
  >>> MR = MinRankInstance(m, eta, n, r, q)
  >>> V = Verifier(MR)
  >>> P = Prover(MR)
  >>> authentication_driver(P, V)  # This prover should be rejected.
  >>> LP = LegitimateProver(MR)
  >>> MR.give_access(LP)
  >>> authentication_dirver(LP, V)  # This prover should _not_ be rejected.
"""

from copy import deepcopy
from sage.all import *
from mr_util import *

__author__ = "Dario Gjorgjevski"
__email__ = "gjorgjevski.dario@students.finki.ukim.mk"
__license__ = "GPLv3"

# Recommended number of rounds.
rounds = 35


class ProverNotReadyError(Exception):
    """An Exception to signify that a Prover is not ready."""
    pass


class VerifierNotReadyError(Exception):
    """An Exception to signify that a Verifier is not ready."""
    pass


class AuthenticationError(Exception):
    """An Exception to signify failed authentication."""
    pass


class Prover(object):
    """Prover class."""
    def __init__(self, MR):
        """Initializes a (naive) Prover object.

        Args:
            MR: The MR instance associated to the prover.
        """
        self._MR = MR  # Don't mangle names to allow for potential inheritance.
        self.__ready = False
        self.__awaiting_query = False

    @property
    def alpha(self):
        """Tries to compute a value for the secret vector alpha.

        This is a naive implementation which simply guesses alpha.
        Subclasses can override it and implement custom behavior.
        """
        try:
            return self.__alpha
        except AttributeError:
            self.__alpha = random_vector(self._MR.finite_field, self._MR.m)
            return self.__alpha

    def prepare_round(self):
        """Prepares a Prover object for a round of authentication."""
        # Generate the (S, T, X) triple.
        # S and T are generated as full rank eta x eta and n x n
        # matrices respectively.
        # X is a completely random eta x n matrix.
        S = random_full_rank_matrix(self._MR.finite_field, self._MR.eta)
        T = random_full_rank_matrix(self._MR.finite_field, self._MR.n)
        X = random_matrix(self._MR.finite_field,
                          self._MR.eta, self._MR.n)

        # Generate beta_1 and N_1.
        beta_1 = random_vector(self._MR.finite_field, self._MR.m)
        N_1 = linear_combination(beta_1, self._MR.matrices)

        # Generate beta_2 and N_2.
        beta_2 = self.alpha + beta_1
        N_2 = linear_combination(beta_2, self._MR.matrices)

        # These will all be used in the authentication; compute and store them.
        self.__STX = (S, T, X)
        self.__ID = (S * N_1 * T + X,
                     S * N_2 * T + X - S * self._MR.offset_matrix * T)
        self.__N = (N_1, N_2)
        self.__beta = (beta_1, beta_2)
        self.__ready = True

    def send_hashes(self, verifier):
        """Initialize the authentication by sending hashes to a Verifier.

        Args:
            verifier: A Verifier object that will perform the authentication.

        Raises:
            ProverNotReadyError: There is something that Prover still has not
                computed.
        """
        if not self.__ready:
            raise ProverNotReadyError("Prover has not computed STX and ID.")

        verifier.receive_hashes(*map(sha256_hash,
                                     (self.__STX,) + self.__ID))

        # Reset.
        self.__ready = False
        self.__awaiting_query = True

    def receive_query(self, verifier, Q):
        """Responds to a query presented by a Verifier.

        Args:
            verifier: The verifier to whom the response will be sent.
            Q: The query ID.

        Raises:
            ValueError: Invalid query ID.
        """
        if Q not in (0, 1, 2):
            raise ValueError(
                "Prover was prompted by Verifier with an invalid query."
            )
        elif not self.__awaiting_query:
            raise ProverNotReadyError(
                "Prover was not expecting a query but received one."
            )

        self.__awaiting_query = False  # Reset.

        if Q == 0:
            verifier.receive_response(Q, *self.__ID)
        elif Q == 1 or Q == 2:
            verifier.receive_response(Q, self.__STX, self.__beta[Q - 1])

    def __str__(self):
        """Pretty printing."""
        return "(Naive) Prover object.  Associated MR instance: " + \
            str(self._MR) + "."


class LegitimateProver(Prover):
    """A Legitimate Prover, i.e. one that holds a private key."""
    def __init__(self, MR, alpha=None):
        """Initializes a LegitimateProver object.

        A LegitimateProver should always authenticate successfully.
        Authentication is disallowed if either no or an incorrect
        secret vector is provided.

        Args:
            MR: The associated MinRank instance.
            alpha: The secret vector (optional).  Must be a solution
                to the associated MR instance.
        """
        super(LegitimateProver, self).__init__(MR)

        if alpha is not None:
            self.alpha = alpha

    def __check_alpha(self, alpha):
        """Checks if a given secret vector satisfies the associated MR."""
        return ((linear_combination(alpha, self._MR.matrices) -
                 self._MR.offset_matrix).rank() == self._MR.r)

    @property
    def alpha(self):
        """Computes (simply returns) the secret vector."""
        try:
            return self.__alpha
        except AttributeError:
            raise ProverNotReadyError(
                "LegitimateProver has no access to its secret vector."
            )

    @alpha.setter
    def alpha(self, alpha):
        """Receives the secret vector to a MR instance.

        Raises:
            ValueError: The secret vector is not a MR solution.
        """
        if not self.__check_alpha(alpha):
            raise ValueError("Attempt to give an invalid secret vector.")

        self.__alpha = alpha

    def __str__(self):
        """Pretty printing."""
        return "LegitimateProver object.  Associated MR instance: " + \
            str(self._MR) + "."


class Verifier(object):
    """Verifier class."""
    def __init__(self, MR):
        """Initializes a Verifier object.

        Args:
            MR: The MinRank instance associated to this verifier.
        """
        self.__MR = MR
        self.__has_hashes = False
        self.__awaiting_response = False

    def receive_hashes(self, STX_hash, ID_1_hash, ID_2_hash):
        """Receive hashes sent by a Prover.

        Args:
            STX_hash: The hash of the (S, T, X) triple.
            ID_1_hash: The hash of the first part of the Prover's ID.
            ID_2_hash: The hash of the second part of the Prover's ID.
        """
        self.__STX_hash = STX_hash
        self.__ID_hash = (ID_1_hash, ID_2_hash)
        self.__has_hashes = True

    def send_query(self, prover):
        """Sends a random query to a Prover and prompts for response.

        Args:
            prover: The prover that will be queried.

        Raises:
            HashesNotAvailableError: The Prover has not supplied hashes.
        """
        # Check if hashes are readily available.
        if not self.__has_hashes:
            raise VerifierNotReadyError(
                "Hashes must be sent to Verifier before any query is made."
            )
        # Prompt the prover for a response.
        self.__awaiting_response = True
        prover.receive_query(self, ZZ.random_element(0, 3))
        # Reset.
        self.__has_hashes = False

    def receive_response(self, Q, *args):
        """Receives and and processes a response sent by a Prover.

        Args:
            Q: The ID of the response.
            args: The contents of the response.  Meaning varies depending on
                response's ID.  If Q == 0, args is the Prover's ID.
                If Q == 1 or Q == 2, args[0] is the (S, T, X) triple and
                args[1] is the beta_Q vector.

        Raises:
            AuthenticationError: Unsuccessful authentication.
            VauleError: Invalid response ID.
        """
        if Q not in (0, 1, 2):
            raise ValueError("Invalid response type sent to Verifier.")
        elif not self.__awaiting_response:
            raise VerifierNotReadyError(
                "Verifier was not expecting a response but received one."
            )

        self.__awaiting_response = False  # Reset.

        if Q == 0:
            # Unpack arguments.
            ID = args

            # Check ID hashes.
            if tuple(map(sha256_hash, ID)) != self.__ID_hash:
                raise AuthenticationError("Invalid ID hashes.")

            # Check rank of S * M * T.
            if (ID[1] - ID[0]).rank() != self.__MR.r:
                raise AuthenticationError("Invalid rank.")
        elif Q == 1 or Q == 2:
            # Unpack arguments.
            (S, T, X) = args[0]
            beta = args[1]

            # Check nonsingularity of S and T.
            if not (S.is_invertible() and T.is_invertible()):
                raise AuthenticationError("S and T must be nonsingular.")

            # Check STX hash.
            if sha256_hash(args[0]) != self.__STX_hash:
                raise AuthenticationError("Invalid STX hash.")

            # Temporary linear combination with instance masked by S and T.
            temp = linear_combination(
                beta, [S * M * T for M in self.__MR.matrices]
            ) + X

            if Q == 1:
                if sha256_hash(temp) != self.__ID_hash[0]:
                    raise AuthenticationError("Invalid ID[0] hash.")
            else:
                if sha256_hash(temp - S * self.__MR.offset_matrix * T) != \
                       self.__ID_hash[1]:
                    raise AuthenticationError("Invalid ID[1] hash.")

    def __str__(self):
        """Pretty printing."""
        return "Verifier object.  Associated MR instance: " + \
            str(self.__MR) + "."


class MinRankInstance(object):
    """Represents an instance of the MinRank problem.

    Attributes:
        m: The size of the problem (m + 1 matrices in total).
        eta: The row dimension of each matrix.
        n: The column dimension of each matrix.
        r: The rank of the secret matrix.
        q: The size of the finite field in which arithmetic is
            performed.  Must be a prime number.
        matrices: The MR matrices (M_1, M_2, ..., M_m).
        offset_matrix: The base matrix (M_0).
        finite_field: GF(q).

    Methods:
        give_access: Gives access to the secret vector to a
            "legitimate prover".
    """
    def __init__(self, m, eta, n, r, q):
        """Initialize a MinRank instance object (a public/private key).

        Raises:
            AssertionError: Something went wrong with the computation.
        """
        # The finite field that will be used to perform arithmetic in.
        self.__finite_field = GF(q)

        # The eta x n matrix space in which the instance will be generated.
        self.__matrix_space = MatrixSpace(self.__finite_field, eta, n)

        # Generate all of the instance except for the very last matrix.
        self.__offset_matrix = self.__matrix_space.random_element()
        self.__Ms = [self.__matrix_space.random_element()
                     for _ in range(m - 1)]

        # Generate the secret eta x n matrix M of rank r.
        self.__M = random_matrix(self.__finite_field,
                                 eta, n,
                                 algorithm='echelonizable', rank=r)
        self.__M.set_immutable()

        # Generate the secret vector alpha (last component must be non-zero).
        while True:
            self.__alpha = random_vector(self.__finite_field, m)
            if self.__alpha[-1] != 0:
                break

        # Deterministically generate the last part of the instance.
        self.__Ms.append(
            ((self.__M + self.__offset_matrix -
              linear_combination(self.__alpha[:-1], self.__Ms)) /
             self.__alpha[-1])
        )

        # Assert that the instance was constructed well, i.e. the "secret
        # key" allows us to construct a matrix of rank r, namely M.
        assert (self.__M ==
                linear_combination(self.__alpha, self.__Ms) -
                self.__offset_matrix)

        # Make all matrices immutable and put them in a tuple rather than
        # a list.
        map(lambda M: M.set_immutable(), self.__Ms)
        self.__Ms = tuple(self.__Ms)

        # Store the parameters that were used.
        self.m = m
        self.eta = eta
        self.n = n
        self.r = r
        self.q = q

    @property
    def finite_field(self):
        """Returns the associated finite field."""
        return self.__finite_field

    @property
    def matrices(self):
        """Returns a tuple of the matrices associated to the instance."""
        return self.__Ms

    @property
    def offset_matrix(self):
        """Returns the offset matrix associated to the instance."""
        return self.__offset_matrix

    def give_access(self, legitimate_prover):
        """Gives access to the secret vector to a legitimate prover.

        Args:
            legitimate_prover: A LegitimateProver object (or descendant).

        Raises:
            TypeError: Not a valid LegitimateProver object.
        """
        if not isinstance(legitimate_prover, LegitimateProver):
            raise TypeError(
                "Attempted to give access to a prover who is not "
                "a LegitimateProver object."
            )

        legitimate_prover.alpha = deepcopy(self.__alpha)

    def __str__(self):
        """Pretty printing."""
        return "MR({:d}, {:d}, {:d}, {:d}, {:d})".format(
            self.m, self.eta, self.n, self.r, self.q
        )


def authentication_driver(prover, verifier, rounds=rounds):
    """Performs authentication."""
    for i in range(rounds):
        prover.prepare_round()
        prover.send_hashes(verifier)
        try:
            verifier.send_query(prover)
        except AuthenticationError as e:
            print(("Authentication unsucessful.\n"
                   "Failed at round: {:02d}\n"
                   "Reason         : {}").format(i + 1, str(e)))
            return False

    print("Authentication successful.")
    return True  # All checks passed.
