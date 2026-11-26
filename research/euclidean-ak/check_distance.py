#!/usr/bin/env python3
"""Finite checks on the ordinary rank-two AC exponent-matrix graph.

Rows give (x, y) exponent sums of the ordered relators. Conjugation projects
to a loop and can be omitted when minimizing length. No bounds are placed
on intermediate matrix entries. Run with python3 check_distance.py.
"""

IDENTITY = (1, 0, 0, 1)


def ak(n):
    return (n, -(n + 1), 1, -1)


def row_additions(matrix, sign):
    a, b, c, d = matrix
    return ((a + sign * c, b + sign * d, c, d),
            (a, b, c + sign * a, d + sign * b))


def neighbors(matrix, reverse=False):
    a, b, c, d = matrix
    yield (-a, -b, c, d)
    yield (a, b, -c, -d)
    # Forward right multiplication adds a row; an incoming edge subtracts it.
    yield from row_additions(matrix, -1 if reverse else 1)


def distance(start, target, outgoing, incoming):
    """Bidirectional BFS, growing a complete layer at each iteration."""
    if start == target:
        return 0
    frontier, other = {start}, {target}
    seen, seen_other = {start}, {target}
    depth = 0
    while frontier and other:
        layer = {v for u in frontier for v in outgoing(u)} - seen
        depth += 1
        if layer & seen_other:
            return depth
        seen.update(layer)
        frontier, other = other, layer
        seen, seen_other = seen_other, seen
        outgoing, incoming = incoming, outgoing
    raise ValueError("Disconnected endpoints")


def up_to_row_signs(matrix):
    """Quotient by independent row sign changes, for the addition count alone."""
    a, b, c, d = matrix
    if (a, b) < (0, 0):
        a, b = -a, -b
    if (c, d) < (0, 0):
        c, d = -c, -d
    return a, b, c, d


def addition_neighbors(matrix):
    # Inversions are free for this count, so either sign of an addition costs one.
    for sign in (-1, 1):
        for result in row_additions(matrix, sign):
            yield up_to_row_signs(result)


def witness(n):
    """Invert row 2, add it to row 1 n+1 times, invert row 1, then add to row 2."""
    a, b, c, d = ak(n)
    c, d = -c, -d
    additions, inversions = 0, 1
    for _ in range(n + 1):
        a, b = a + c, b + d
        additions += 1
    a, b = -a, -b
    inversions += 1
    c, d = c + a, d + b
    additions += 1
    return (a, b, c, d), additions, inversions


def euclidean_cost(a, b):
    a, b = abs(a), abs(b)
    count = 0
    while a and b:
        if a >= b:
            a -= b
        else:
            b -= a
        count += 1
    return count


def main():
    print("n   shortest directed length   minimum additions")
    for n in range(13):
        start = ak(n)
        length = distance(start, IDENTITY, neighbors, lambda m: neighbors(m, reverse=True))
        additions = distance(up_to_row_signs(start), IDENTITY,
                             addition_neighbors, addition_neighbors)
        endpoint, witness_additions, inversions = witness(n)
        assert endpoint == IDENTITY
        assert additions == witness_additions == n + 2
        assert inversions == 2 and length == additions + inversions == n + 4
        print(f"{n:2} {length:16} {additions:19}")

    limit = 32
    for a in range(-limit, limit + 1):
        for b in range(-limit, limit + 1):
            value = euclidean_cost(a, b)
            assert euclidean_cost(-a, b) == euclidean_cost(a, -b) == value
            assert abs(euclidean_cost(a + b, b) - value) <= 1
            assert abs(euclidean_cost(a, b + a) - value) <= 1
    print(f"Euclidean cost checked for {(2 * limit + 1) ** 2} signed pairs "
          f"in [-{limit}, {limit}]².")


if __name__ == "__main__":
    main()
