"""Verify sharp basepoint distortion under count-priced conjugation.

Every rank n has a fixed ordered list of n cyclic words whose choices of
a *one-letter* change of starting place realize ordinary and stable costs
0,...,n-1. All displayed input representatives are positive words.

Law for the lower bound: over F3 assign each free generator sign -1 and
d(x_i)=e_i, d(uv)=d(u)+sign(u)*d(v). An inverse rescales a row; a right
product is a row operation. Conjugation changes only one row, and hence can
raise rank by at most one. An isolated generator-relator insertion increases
rank and ambient dimension by 1; deletion reverses it at any two positions.
Thus (ambient dimension - matrix rank) bounds even stable conjugation cost.
"""
from argparse import ArgumentParser
from itertools import combinations, product


def inverse(word):
    return tuple(-letter for letter in reversed(word))


def multiply(left, right):
    stack = list(left)
    for letter in right:
        if stack and stack[-1] == -letter:
            stack.pop()
        else:
            stack.append(letter)
    return tuple(stack)


def derivative(word, n):
    result = [0] * n
    parity = 1
    for letter in word:
        # d(x^-1) = -sign(x)^-1 d(x) = d(x) for this character.
        j = abs(letter) - 1
        result[j] = (result[j] + parity) % 3
        parity = -parity
    return result


def rank(rows):
    matrix = [list(row) for row in rows]
    pivots = 0
    for j in range(len(matrix[0])):
        pivot = next((k for k in range(pivots, len(matrix)) if matrix[k][j]), None)
        if pivot is None:
            continue
        matrix[pivots], matrix[pivot] = matrix[pivot], matrix[pivots]
        value = matrix[pivots][j]
        normalized = [(a * value) % 3 for a in matrix[pivots]]  # 1,2 self-inverse
        for i in range(pivots+1, len(matrix)):
            factor = matrix[i][j]
            matrix[i] = [(a-factor*b) % 3 for a, b in zip(matrix[i], normalized)]
        pivots += 1
    return pivots


def source(n, cuts):
    anchor = (1,)
    rows = []
    for z in range(2, n+1):
        b = (z,) + anchor + (z,)
        rows.append(b[1:] + b[:1] if z in cuts else b)
        anchor = b + anchor + (z,)
    return [anchor] + rows


def moves(n, cuts):
    for z in sorted(cuts):
        yield ("C", z-1, (z,))
    # c=zazaz, b=zaz; c^-1 b=(az)^-1, b(az)^-1=z, (az)z^-1=a.
    for i in range(n-1, 0, -1):
        yield from (("I", 0), ("M", 0, i), ("M", i, 0), ("I", 0),
                    ("I", i), ("M", 0, i), ("I", i))


def replay(rows, operations):
    state = list(rows)
    cost = 0
    for op, i, *argument in operations:
        if op == "I":
            state[i] = inverse(state[i])
        elif op == "M":
            j, = argument
            if i == j:
                raise ValueError("Invalid self multiplication")
            state[i] = multiply(state[i], state[j])
        elif op == "C":
            g, = argument
            state[i] = multiply(multiply(g, state[i]), inverse(g))
            cost += 1
        else:
            raise ValueError(op)
    return state, cost


def fixes_origin(word, parameters):
    point = 0
    for letter in reversed(word):
        # Each letter is a self-inverse affine reflection on three points.
        point = (parameters[abs(letter)-1] - point) % 3
    return point == 0


def check_family(n):
    count = 0
    for k in range(n):
        for indices in combinations(range(2, n+1), k):
            cuts = set(indices)
            rows = source(n, cuts)
            lower = n - rank([derivative(w, n) for w in rows])
            endpoint, upper = replay(rows, moves(n, cuts))
            if lower != k or upper != k or endpoint != [(i,) for i in range(1, n+1)]:
                raise ArithmeticError((n, cuts, lower, upper, endpoint))
            if n <= 4:
                found = sum(all(fixes_origin(row, marking) for row in rows)
                            for marking in product(range(3), repeat=n))
                if found != 3 ** k:
                    raise ArithmeticError((n, cuts, found))
            count += 1
    return count


def check_ms_rotation():
    letters = {"x": 1, "X": -1, "y": 2, "Y": -2}
    def word(s):
        return tuple(letters[c] for c in s)
    r, s = map(word, ("XyxYY", "xxYXy"))
    rotated = r[2:] + r[:2]
    if rotated != multiply(multiply(word("Yx"), r), word("Xy")):
        raise ArithmeticError("Rotation is not conjugation by the inverse prefix")
    steps = (("I", 0), ("M", 1, 0), ("I", 0), ("C", 1, word("YX")),
             ("M", 0, 1), ("I", 0), ("C", 1, word("Xy")), ("M", 1, 0), ("I", 0))
    # The source has cost 3 by ACC-P000036, and lies one C from this tuple.
    if replay([rotated, s], steps) != ([(1,), (2,)], 2):
        raise ArithmeticError("MS rotation witness failed")


if __name__ == "__main__":
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--max-rank", type=int, default=7)
    args = parser.parse_args()
    if args.max_rank < 1:
        parser.error("max rank must be positive")
    for n in range(1, args.max_rank+1):
        print(f"rank {n}: {check_family(n)} starting-place choices, costs 0 through {n-1}.")
    check_ms_rotation()
    print("MS(1,w*): the two-letter rotation of row 0 has an exact nine-step two-C witness.")
