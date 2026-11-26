#!/usr/bin/env python3
"""Replay the two-conjugation witness and verify the permutation and matrix certificates."""

from collections import Counter
from itertools import permutations


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def inverse_word(word):
    return word[::-1].swapcase()


def reduce_word(word):
    stack = []
    for letter in word:
        if stack and stack[-1] == letter.swapcase():
            stack.pop()
        else:
            stack.append(letter)
    return "".join(stack)


def ak_relators(n):
    return "x" * n + "Y" * (n + 1), "xyx" + inverse_word("yxy")


def check_word_path():
    moves = [
        ("inv", 0), ("mul", 1, 0), ("conj", 1, "YX"),
        ("mul", 1, 0), ("conj", 1, "xyX"), ("inv", 0), ("mul", 1, 0),
        ("mul", 0, 1), ("mul", 0, 1),
    ]
    rows = list(ak_relators(1))
    for op, i, *arg in moves:
        if op == "inv":
            word = inverse_word(rows[i])
        elif op == "mul":
            j, = arg
            require(i != j, "multiplication source and target coincide")
            word = rows[i] + rows[j]
        elif op == "conj":
            w, = arg
            word = w + rows[i] + inverse_word(w)
        else:
            raise ValueError(op)
        rows[i] = reduce_word(word)
    require(rows == ["x", "y"], f"unexpected word endpoint {rows}")
    counts = Counter(move[0] for move in moves)
    require(counts == {"mul": 5, "inv": 2, "conj": 2}, f"unexpected move counts {counts}")
    print("AK(1) word replay: 9 moves (5 right products, 2 inversions, 2 conjugations), endpoint (x, y)")


PERM_ID = (0, 1, 2, 3)


def compose(p, q):
    """Apply q first, then p."""
    return tuple(p[i] for i in q)


def inverse_perm(p):
    return tuple(p.index(i) for i in PERM_ID)


def subgroup_generated_by(p, q):
    seen = {PERM_ID}
    todo = [PERM_ID]
    while todo:
        a = todo.pop()
        for g in p, q:
            b = compose(a, g)
            if b not in seen:
                seen.add(b)
                todo.append(b)
    return seen


def check_s4():
    # Cycles (0 2 1 3) and (0 1 3 2), as tables of images of 0,1,2,3.
    x, y = (2, 3, 1, 0), (1, 3, 0, 2)
    alphabet = {"x": x, "y": y, "X": inverse_perm(x), "Y": inverse_perm(y)}

    def evaluate(word):
        value = PERM_ID
        for letter in word:
            value = compose(value, alphabet[letter])
        return value

    s, second = map(evaluate, ak_relators(1))
    require((s, second) == ((0, 1, 3, 2), PERM_ID), "initial S4 images")
    sizes = Counter()
    for g in permutations(PERM_ID):
        conjugate = compose(compose(g, s), inverse_perm(g))
        group = subgroup_generated_by(s, conjugate)
        require(x not in group, f"X belongs to subgroup for conjugator {g}")
        sizes[len(group)] += 1
    require(sizes == {2: 4, 4: 4, 6: 16}, f"unexpected S4 sizes {sizes}")
    print("S4: all 24 conjugators exclude X; subgroup orders 2, 4, 6 occur 4, 4, 16 times")


IDENTITY = (1, 0, 0, 1)


def modulo(matrix, m):
    return tuple(a % m for a in matrix)


def matmul(left, right, m):
    a, b, c, d = left
    e, f, g, h = right
    return modulo((a*e + b*g, a*f + b*h, c*e + d*g, c*f + d*h), m)


def matpow(matrix, exponent, m):
    result = IDENTITY
    for _ in range(exponent):
        result = matmul(result, matrix, m)
    return result


def check_modular(n):
    m = n*(n + 1) + 2
    x, y, y_inv = (1, 1, 0, 1), (1, 0, -1, 1), (1, 0, 1, 1)
    require(matmul(y, y_inv, m) == IDENTITY, f"inverse at n={n}")
    xy = matmul(x, y, m)
    require(matmul(xy, x, m) == matmul(y, xy, m), f"braid at n={n}")
    first = matmul(matpow(x, n, m), matpow(y_inv, n+1, m), m)
    require(first == modulo((1+n*(n+1), n, n+1, 1), m), f"first relator at n={n}")
    a, b, c, d = first
    require((a+d) % m == 0 and (a*d-b*c) % m == 1, f"trace or determinant at n={n}")
    require(matmul(first, first, m) == modulo((-1, 0, 0, -1), m), f"first square at n={n}")
    x2, xy2 = matpow(x, 2, m), matpow(xy, 2, m)
    left, right = matmul(x2, xy2, m), matmul(xy2, x2, m)
    require(left == modulo((-3, 1, -1, 0), m), f"left product at n={n}")
    require(right == modulo((-1, -1, -1, -2), m), f"right product at n={n}")
    # Apply both products to the vector (0,1) and identify vectors with their negatives.
    lvec, rvec = (left[1], left[3]), (right[1], right[3])
    distinct = lvec not in (rvec, modulo((-rvec[0], -rvec[1]), m))
    require(distinct == (n > 0), f"projective witness at n={n}, m={m}")
    if n == 0:
        require(left == right, "the square products should coincide modulo 2")


if __name__ == "__main__":
    check_word_path()
    check_s4()
    for parameter in range(101):
        check_modular(parameter)
    print("Modular matrices: all n=1..100 pass, with even composite moduli 4 through 10102")
    print("Boundary n=0: modulo 2 the square products coincide, so the obstruction vanishes")
