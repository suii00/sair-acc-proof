"""Replay ordinary AC witnesses for the Miller–Schupp word w* = YxyX.

Rows are ordered and indexed from zero. Uppercase letters denote inverses.
A move C with argument h is conjugation by h on the left.
Run with Python 3.9 or later. No dependencies or input data are needed.
"""

from argparse import ArgumentParser


WITNESS_ZERO = (
    ("M", 1), ("I", 1), ("C", 1, "X"), ("M", 0), ("I", 0), ("M", 1),
)

WITNESS_ONE = (
    ("I", 0), ("C", 0, "Yx"), ("M", 1), ("I", 0), ("C", 1, "YX"),
    ("M", 0), ("I", 0), ("C", 1, "Xy"), ("M", 1), ("I", 0),
)


def inverse(word):
    return word[::-1].swapcase()


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == letter.swapcase():
            stack.pop()
        else:
            stack.append(letter)
    return "".join(stack)


def source(n):
    return reduce_word("X" + "y" * n + "x" + "Y" * (n + 1)), "xxYXy"


def uniform_moves(n):
    """Use 2**n+1 conjugations and 3*2**n+4 total moves for each n >= 1.

    In the original first row, replace each occurrence Xy by yXX. For a
    following suffix B this right-multiplies that row by B^{-1} S^{-1} B,
    where S=xxYXy is the original second relator. Carry the frame of the
    first row from one B to the next and keep S^{-1} fixed during the loop.
    After j batches the unframed, unreduced row is y^j X^(2^j) y^(n-j) x Y^(n+1).
    """
    if n < 1:
        raise ValueError("The uniform construction requires n >= 1.")
    yield ("I", 1)
    frame = ""
    for j in range(n):
        for r in range(2**j):
            suffix = "X" * (2*r) + "y" * (n-j-1) + "x" + "Y" * (n+1)
            yield ("C", 0, reduce_word(suffix + inverse(frame)))
            yield ("M", 0)
            frame = suffix

    # With m=2^n-1, the conjugated first row is x^{2-m} Y XX.
    # This power is x for n=1 and a negative power of x for n >= 2.
    m = 2**n - 1
    yield ("I", 1)
    yield ("C", 0, "x" * (m-2) if m >= 2 else "X")
    # The first row is now Y X^m; turn S into Y X^(m-1).
    yield ("M", 1)
    yield ("C", 1, "XX")
    # (Y X^m)^{-1} (Y X^(m-1)) = x. Restore the second generator.
    yield ("I", 0)
    yield ("M", 0)
    for _ in range(m - 1):
        yield ("M", 1)
    yield ("I", 1)


def replay(n, moves, expected_count):
    rows = list(source(n))
    total = count = 0
    peak = sum(map(len, rows))
    for op, i, *arguments in moves:
        total += 1
        if op == "I":
            rows[i] = inverse(rows[i])
        elif op == "M":
            rows[i] = reduce_word(rows[i] + rows[1-i])
        elif op == "C":
            conjugator, = arguments
            rows[i] = reduce_word(conjugator + rows[i] + inverse(conjugator))
            count += 1
        else:
            raise ValueError(f"Unknown operation {op}")
        peak = max(peak, sum(map(len, rows)))
    if rows != ["x", "y"] or count != expected_count:
        raise ValueError(f"Certificate for n={n} ended at {rows} with {count} conjugations")
    return total, count, peak


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=8,
                        help="replay the uniform construction through this n (default 8)")
    options = parser.parse_args()
    if options.max_n < 1:
        parser.error("--max-n must be positive")
    for n, path, cost, expected in ((0, WITNESS_ZERO, 1, (6, 1, 6)),
                                    (1, WITNESS_ONE, 3, (10, 3, 10))):
        statistics = replay(n, path, cost)
        if statistics != expected:
            raise ValueError(f"Unexpected (moves, conjugations, peak) at n={n}: {statistics}")
        print(f"MS({n},w*): moves={statistics[0]}, conjugations={cost}, peak={statistics[2]}")
    for n in range(1, options.max_n + 1):
        total, count, peak = replay(n, uniform_moves(n), 2**n + 1)
        if total != 3*2**n + 4:
            raise ValueError(f"Unexpected length for the uniform path at n={n}: {total}")
        print(f"Uniform path n={n}: moves={total}, conjugations={count}, peak={peak}")
