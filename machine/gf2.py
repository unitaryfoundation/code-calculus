from __future__ import annotations

from functools import lru_cache


@lru_cache(maxsize=8192)
def _basis_tuple_cached(vectors_tuple):
    basis = {}
    for vector in vectors_tuple:
        value = int(vector)
        while value:
            pivot = value.bit_length() - 1
            if pivot in basis:
                value ^= basis[pivot]
            else:
                basis[pivot] = value
                break
    return tuple(basis.items())


def basis_tuple(vectors):
    return _basis_tuple_cached(tuple(int(v) for v in vectors))


def basis(vectors):
    return dict(basis_tuple(vectors))


def rank(vectors):
    return len(basis(vectors))


def in_span(value, vectors):
    basis_map = basis(vectors)
    value = int(value)
    for pivot in sorted(basis_map, reverse=True):
        if (value >> pivot) & 1:
            value ^= basis_map[pivot]
    return value == 0


_basis_tuple = _basis_tuple_cached
_basis = basis
_rank = rank
_in_span = in_span


__all__ = [
    "basis_tuple",
    "basis",
    "rank",
    "in_span",
    "_basis_tuple",
    "_basis",
    "_rank",
    "_in_span",
]
