#!/usr/bin/env python3
"""Check the marked-group certificates for MS(n, y^-1 x y x^-1).

Run with Python 3.9+ and no extra packages. Each conjugation may use an
arbitrary word. S3 permutations and 2x2 matrices act rightmost first.
"""

from itertools import permutations, product


def compose(p, q):
    return tuple(p[i] for i in q)


def inverse(p):
    return tuple(p.index(i) for i in range(len(p)))


def evaluate(n, x, y, multiply, inv, identity):
    r = identity
    for a in [inv(x)] + [y] * n + [x] + [inv(y)] * (n + 1):
        r = multiply(r, a)
    s = multiply(multiply(multiply(multiply(x, x), inv(y)), inv(x)), y)
    return r, s


def three_signs():
    # An invertible exponent matrix over F2 has distinct nonzero rows.
    for v, w in permutations((1, 2, 3), 2):
        def odd(row, character):
            return bin(row & character).count('1') % 2
        assert sum(odd(v, chi) and odd(w, chi) for chi in (1, 2, 3)) == 1


class PairActions:
    """Nielsen and conjugation transitions modulo simultaneous inner conjugacy."""

    def __init__(self, group):
        conjugates = {
            a: {g: compose(compose(g, a), inverse(g)) for g in group}
            for a in group
        }
        self.labels = {}
        representatives = []
        for p, q in product(group, repeat=2):
            if (p, q) in self.labels:
                continue
            for g in group:
                self.labels[conjugates[p][g], conjugates[q][g]] = len(representatives)
            representatives.append((p, q))
        self.nielsen, self.conjugations = [], []
        for p, q in representatives:
            self.nielsen.append(tuple(self.labels[pair] for pair in (
                (inverse(p), q), (p, inverse(q)), (compose(p, q), q),
                (p, compose(q, p)))))
            self.conjugations.append((
                {self.labels[r, q] for r in conjugates[p].values()},
                {self.labels[p, r] for r in conjugates[q].values()}))


def nielsen_closure(actions, seeds):
    seen = set(seeds)
    queue = list(seen)
    for state in queue:
        for operation in range(4):
            nxt = tuple(mark.nielsen[idx][operation] for mark, idx in zip(actions, state))
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def conjugation_step(actions, states):
    # Keep the affected row synchronized. Choosing conjugators separately in
    # all marks includes the image of every actual single free-word conjugator.
    successors = set()
    for state in states:
        for row in (0, 1):
            choices = (mark.conjugations[idx][row] for mark, idx in zip(actions, state))
            successors.update(product(*choices))
    return successors


def marked_endpoints(n, actions, marks):
    def images(x, y):
        return evaluate(n, x, y, compose, inverse, tuple(range(len(x))))
    source = tuple(a.labels[images(x, y)] for a, (x, y) in zip(actions, marks))
    goal = tuple(a.labels[pair] for a, pair in zip(actions, marks))
    return source, goal


def s3_layers():
    """Independent complete finite calculation for n=1."""
    actions = (PairActions(list(permutations(range(3)))),) * 3
    transposition, other, rotation = (0, 2, 1), (1, 0, 2), (1, 2, 0)
    marks = ((transposition, other), (transposition, rotation),
             (rotation, transposition))
    assert len(actions[0].nielsen) == 11
    initial, goal = marked_endpoints(1, actions, marks)
    layer = nielsen_closure(actions, [initial])
    seen = set(layer)
    sizes = [len(layer)]
    while goal not in layer:
        assert layer
        layer = nielsen_closure(actions, conjugation_step(actions, layer)) - seen
        seen.update(layer)
        sizes.append(len(layer))
    assert sizes == [6, 18, 18, 6]
    return sizes


def four_mark_exclusion():
    """For n=2, a single C from either endpoint gives disjoint closures.

    Each free-word conjugation projects to a permitted edge; the quotient may
    choose these conjugators independently even if no common free word exists.
    In each cyclic Nielsen orbit the operation permutations have finite order,
    so forward zero closures are also backward zero closures.
    """
    dihedral = [tuple((offset + sign*j) % 5 for j in range(5))
                for offset in range(5) for sign in (-1, 1)]
    actions5 = PairActions(list(permutations(range(5))))
    actions = (PairActions(dihedral), PairActions(list(permutations(range(3)))),
               actions5, actions5)
    marks = (((0, 4, 3, 2, 1), (1, 2, 3, 4, 0)),
             ((1, 2, 0), (0, 2, 1)),
             ((0, 1, 2, 4, 3), (1, 2, 3, 4, 0)),
             ((0, 2, 1, 4, 3), (1, 3, 4, 0, 2)))
    initial, goal = marked_endpoints(2, actions, marks)
    left, right = (nielsen_closure(actions, [point]) for point in (initial, goal))
    assert (len(left), len(right)) == (6, 216)
    left = nielsen_closure(actions, conjugation_step(actions, left))
    right = nielsen_closure(actions, conjugation_step(actions, right))
    assert (len(left), len(right)) == (540, 18372) and left.isdisjoint(right)
    return len(left), len(right)


def dihedral_marks(n):
    # (a,s) is the affine map t -> (-1)^s t + a modulo m.
    def check(m, x, y, target_row):
        def mul(p, q):
            return ((p[0] + (-1) ** p[1] * q[0]) % m, p[1] ^ q[1])
        def inv(p):
            return ((-(-1) ** p[1] * p[0]) % m, p[1])
        rows = evaluate(n, x, y, mul, inv, (0, 0))
        assert rows[target_row] == (0, 0) and rows[1 - target_row][1] == 1
        assert mul(x, y) != mul(y, x)
    check(2 * n + 1, (0, 1), (1, 0), 0)
    check(3, (1, 0), (0, 1), 1)
    if n % 2:
        x, y = (0, 2, 1), (1, 0, 2)
        r, s = evaluate(n, x, y, compose, inverse, (0, 1, 2))
        assert r == s and r != (0, 1, 2) and compose(r, r) == (0, 1, 2)
        assert compose(x, y) != compose(y, x)


def gaussian_mark(n):
    # Entries are residues u+vi, i^2=-1. The argument works for composite
    # m as well. All odd n>=1 use S3 instead; this marking covers even n>=4.
    m = n - 1
    assert n >= 4 and n % 2 == 0
    def scalar(real, imaginary=0):
        return (real % m, imaginary % m)
    def add(p, q):
        return scalar(p[0] + q[0], p[1] + q[1])
    def neg(p):
        return scalar(-p[0], -p[1])
    def product_scalar(p, q):
        return scalar(p[0]*q[0] - p[1]*q[1], p[0]*q[1] + p[1]*q[0])
    def mul(p, q):
        return tuple(add(product_scalar(p[2*r], q[c]),
                         product_scalar(p[2*r+1], q[c+2]))
                     for r in (0, 1) for c in (0, 1))
    def inv(p):
        a, b, c, d = p
        return d, neg(b), neg(c), a

    h = (m + 1) // 2
    zero, one, imaginary = scalar(0), scalar(1), scalar(0, 1)
    a, b = scalar(-h, h), scalar(-h, 1)
    ident = one, zero, zero, one
    x, y = (a, b, imaginary, a), (one, one, zero, one)
    expected = neg(a), scalar(-1, h), one, a
    assert mul(x, inv(x)) == mul(y, inv(y)) == ident
    r, s = evaluate(n, x, y, mul, inv, ident)
    assert r == s == expected
    assert mul(r, r) == tuple(neg(e) for e in ident)
    assert r[2] == one and one != zero
    assert mul(x, y) not in (mul(y, x), tuple(neg(e) for e in mul(y, x)))
    # Append a C2 factor in which both x and y have odd sign. Both relators
    # are odd there, so (r,odd) generates the common two-element subgroup.


if __name__ == '__main__':
    if not __debug__:
        raise SystemExit('Run without -O to enable the assertions.')
    three_signs()
    print('All six mod-2 bases: exactly one character is odd on both rows.')
    print('MS(1) three S3 markings: complete conjugation layers', s3_layers())
    print('MS(2) four-mark one-conjugation closures: disjoint, sizes', four_mark_exclusion())
    for parameter in range(1, 101):
        dihedral_marks(parameter)
        if parameter >= 4 and parameter % 2 == 0:
            gaussian_mark(parameter)
    print('n=1..100: both dihedral marks verified; the third mark is '
          'verified for n=1 and 3..100.')
