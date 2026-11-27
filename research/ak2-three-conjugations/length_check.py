"""Minimum length of an ordered AK(2) trivialization using exactly three conjugations.

Run with Python 3.9 or later; no external packages or input files are needed.
Rows are numbered 0 and 1. The six move types are inversion of row 0 or 1,
positive right multiplication of row 0 or 1, and arbitrary-word conjugation
of row 0 or 1, in that order. A conjugating word g acts by r ↦ g r g⁻¹.

The lower-bound calculation enumerates every move-type sequence of length
at most 12 with exactly three conjugations and the correct exponent sums.
A sequence is excluded if it cannot reach the marked target in at least
one finite image. The total length of intermediate words and the length of
conjugators are unrestricted. The upper bound is a free-group replay.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations_with_replacement, product


INVERT_FIRST, INVERT_SECOND, MULTIPLY_FIRST, MULTIPLY_SECOND = range(4)
CONJUGATE_FIRST, CONJUGATE_SECOND = 4, 5
CONJUGATIONS = (CONJUGATE_FIRST, CONJUGATE_SECOND)
SOURCE = ("xxYYY", "xyxYXY")
TARGET = ("x", "y")
MARKINGS = (("1230", "1302"), ("0132", "1203"), ("1203", "0213"))

# Each entry is (move type, conjugator); other moves have an empty second field.
WITNESS = (
    (INVERT_FIRST, ""), (MULTIPLY_SECOND, ""), (CONJUGATE_SECOND, "xYX"),
    (MULTIPLY_FIRST, ""), (CONJUGATE_SECOND, "yyXyyXX"),
    (MULTIPLY_SECOND, ""), (CONJUGATE_SECOND, "xYxYY"),
    (INVERT_FIRST, ""), (MULTIPLY_SECOND, ""), (MULTIPLY_FIRST, ""),
    (MULTIPLY_FIRST, ""), (MULTIPLY_SECOND, ""), (MULTIPLY_FIRST, ""),
)


def inverse_word(word):
    return word[::-1].swapcase()


def reduce_word(word):
    letters = []
    for letter in word:
        if letters and letters[-1] == letter.swapcase():
            letters.pop()
        else:
            letters.append(letter)
    return "".join(letters)


def replay_witness():
    rows = list(SOURCE)
    for move, conjugator in WITNESS:
        i = move % 2
        if move in CONJUGATIONS:
            word = conjugator + rows[i] + inverse_word(conjugator)
        elif move in (MULTIPLY_FIRST, MULTIPLY_SECOND):
            word = rows[i] + rows[1-i]
        else:
            word = inverse_word(rows[i])
        rows[i] = reduce_word(word)
    if tuple(rows) != TARGET:
        raise RuntimeError(f"Incorrect witness endpoint: {rows}")
    trace = tuple(move for move, _ in WITNESS)
    if len(trace) != 13 or sum(move in CONJUGATIONS for move in trace) != 3:
        raise RuntimeError("Incorrect witness operation counts")
    return trace


def matrix_neighbors(matrix):
    a, b, c, d = matrix
    return (
        (-a, -b, c, d),
        (a, b, -c, -d),
        (a+c, b+d, c, d),
        (a, b, c+a, d+b),
    )


def compatible_traces(max_length):
    """Insert all three conjugations in every compatible conjugation-free trace."""
    def visit(matrix, ordinary):
        if matrix == (1, 0, 0, 1):
            # Gaps are numbered before, between, and after the ordinary moves.
            # Repeated gaps allow successive conjugations, including on the same row.
            gaps = range(len(ordinary) + 1)
            for first, second, third in combinations_with_replacement(gaps, 3):
                for a, b, c in product(CONJUGATIONS, repeat=3):
                    yield (ordinary[:first] + (a,) + ordinary[first:second] + (b,)
                           + ordinary[second:third] + (c,) + ordinary[third:])
        if len(ordinary) + 3 < max_length:
            for move, neighbor in enumerate(matrix_neighbors(matrix)):
                yield from visit(neighbor, ordinary + (move,))

    return visit((2, -3, 1, -1), ())


def marking_checker(x_string, y_string):
    """Construct H=<x,y> in S4 using one-line permutations acting right-first."""
    x = tuple(map(int, x_string))
    y = tuple(map(int, y_string))
    identity = tuple(range(4))

    def compose(g, h):
        return tuple(g[i] for i in h)

    elements = [identity]
    index = {identity: 0}
    for g in elements:
        for generator in (x, y):
            value = compose(g, generator)
            if value not in index:
                index[value] = len(elements)
                elements.append(value)

    size = len(elements)
    mult = [[index[compose(g, h)] for h in elements] for g in elements]
    inverse = [row.index(0) for row in mult]
    conjugates = [tuple(sorted({mult[mult[h][g]][inverse[h]] for h in range(size)}))
                  for g in range(size)]
    class_id = [min(values) for values in conjugates]
    x_index, y_index = index[x], index[y]
    target = (x_index, y_index)

    def evaluate(word):
        letters = {"x": x_index, "y": y_index,
                   "X": inverse[x_index], "Y": inverse[y_index]}
        value = 0
        for letter in word:
            value = mult[value][letters[letter]]
        return value

    source = tuple(map(evaluate, SOURCE))

    @lru_cache(None)
    def endpoints(ops, backward):
        if not ops:
            return (target if backward else source,)
        pairs = endpoints(ops[:-1], backward)
        move = ops[-1]
        if move == INVERT_FIRST:
            return tuple((inverse[a], b) for a, b in pairs)
        if move == INVERT_SECOND:
            return tuple((a, inverse[b]) for a, b in pairs)
        if move == MULTIPLY_FIRST:
            return tuple((mult[a][inverse[b] if backward else b], b) for a, b in pairs)
        if move == MULTIPLY_SECOND:
            return tuple((a, mult[b][inverse[a] if backward else a]) for a, b in pairs)
        if move == CONJUGATE_FIRST:
            return tuple((g, b) for a, b in pairs for g in conjugates[a])
        return tuple((a, g) for a, b in pairs for g in conjugates[b])

    @lru_cache(None)
    def profiles(ops, backward, middle_move):
        pairs = endpoints(ops, backward)
        if middle_move == CONJUGATE_FIRST:
            return frozenset((class_id[a], b) for a, b in pairs)
        return frozenset((a, class_id[b]) for a, b in pairs)

    def possible(trace):
        middle = [i for i, move in enumerate(trace) if move in CONJUGATIONS][1]
        slot = trace[middle]
        left = profiles(trace[:middle], False, slot)
        right = profiles(trace[middle+1:][::-1], True, slot)
        # The untouched row must match. The other row must be conjugate in H.
        # All such conjugators are allowed in both directions.
        return not left.isdisjoint(right)

    return possible


if __name__ == "__main__":
    witness_trace = replay_witness()
    print("Free-group witness reaches (x,y): 13 moves, 3 conjugations.")
    traces = list(compatible_traces(12))
    print("Survivors by length after exponent sums:", dict(sorted(Counter(map(len, traces)).items())))
    for x_mark, y_mark in MARKINGS:
        possible = marking_checker(x_mark, y_mark)
        if not possible(witness_trace):
            raise RuntimeError(f"Finite image rejects the positive witness at {x_mark},{y_mark}")
        traces = [trace for trace in traces if possible(trace)]
        counts = dict(sorted(Counter(map(len, traces)).items()))
        print(f"Survivors after x={x_mark}, y={y_mark}:", counts)

    if traces:
        raise RuntimeError(f"{len(traces)} traces survived")
    print("Every three-conjugation trivialization requires at least 13 moves.")
