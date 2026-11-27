"""Check the shortest path for MS(1,w*) subject to exactly three conjugations.

Each trace specifies an operation and a row, leaving the conjugating words
unrestricted. Positive right products and inversions are the only other
operations. Run with Python 3.9 or later, using only the standard library.
"""

from collections import Counter
from functools import lru_cache
from itertools import combinations, product

from witness_check import WITNESS_ONE, replay, source


def exponent_step(matrix, move):
    a, b, c, d = matrix
    return ((-a, -b, c, d), (a, b, -c, -d),
            (a + c, b + d, c, d), (a, b, c + a, d + b))[move]


def traces_through_nine():
    # Codes 0,1 invert the indicated row; 2,3 multiply; 4,5 conjugate.
    for size in range(7):
        for ordinary in product(range(4), repeat=size):
            matrix = (0, -1, 1, 0)
            for move in ordinary:
                matrix = exponent_step(matrix, move)
            if matrix != (1, 0, 0, 1):
                continue
            for slots in combinations(range(size + 3), 3):
                for rows in product((4, 5), repeat=3):
                    skeleton = iter(ordinary)
                    conjugations = iter(rows)
                    yield tuple(next(conjugations) if j in slots else next(skeleton)
                                for j in range(size + 3))


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def multiply(p, q):
    return tuple(p[j] for j in q)


def finite_test(mark_x, mark_y):
    x, y = tuple(map(int, mark_x)), tuple(map(int, mark_y))
    unit = tuple(range(len(x)))
    group = [unit]
    seen = {unit}
    for p in group:
        for step in (x, y):
            q = multiply(p, step)
            if q not in seen:
                seen.add(q)
                group.append(q)

    @lru_cache(None)
    def conjugates(p):
        return frozenset(multiply(multiply(h, p), inverse(h)) for h in group)

    def evaluate(word):
        letters = {"x": x, "X": inverse(x), "y": y, "Y": inverse(y)}
        value = unit
        for c in word:
            value = multiply(value, letters[c])
        return value

    start = tuple(map(evaluate, source(1)))

    @lru_cache(None)
    def endpoints(trace, backward):
        if not trace:
            return frozenset({(x, y) if backward else start})
        previous = endpoints(trace[:-1], backward)
        move = trace[-1]
        i = move % 2
        result = set()
        for pair in previous:
            a, b = pair[i], pair[1-i]
            if move < 2:
                replacements = (inverse(a),)
            elif move < 4:
                replacements = (multiply(a, inverse(b) if backward else b),)
            else:
                replacements = conjugates(a)
            for v in replacements:
                result.add((v, b) if i == 0 else (b, v))
        return frozenset(result)

    @lru_cache(None)
    def signatures(trace, backward, row):
        return {(pair[1-row], min(conjugates(pair[row])))
                for pair in endpoints(trace, backward)}

    def survives(trace):
        # Match the untouched row and the conjugacy class across the middle C.
        mid = [j for j, move in enumerate(trace) if move >= 4][1]
        row = trace[mid] % 2
        prefix = signatures(trace[:mid], False, row)
        suffix = signatures(trace[mid+1:][::-1], True, row)
        return not prefix.isdisjoint(suffix)

    return survives


if __name__ == "__main__":
    candidates = list(traces_through_nine())
    print("Exponent-sum survivors by total length:", dict(Counter(map(len, candidates))))
    cost = {"I": 0, "M": 2, "C": 4}
    positive = tuple(cost[op] + row for op, row, *_ in WITNESS_ONE)
    for x, y in (("234510", "214503"), ("1230", "1302")):
        survives = finite_test(x, y)
        if not survives(positive):
            raise RuntimeError("A finite test rejected the ten-step positive control")
        candidates = [t for t in candidates if survives(t)]
        print(f"After x={x}, y={y}:", dict(Counter(map(len, candidates))))
    if candidates or replay(1, WITNESS_ONE, 3) != (10, 3, 10):
        raise RuntimeError("Shortestness certificate failed")
    print("The minimum length with three conjugations is 10.")
