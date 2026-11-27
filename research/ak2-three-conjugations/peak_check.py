#!/usr/bin/env python3
"""Verify the AK(2) tradeoff between conjugations and peak total relator length.

Run with Python 3.9+ (standard library only), without -O. The search considers
ordered pairs of freely reduced words. No swap, symmetry quotient, or cap on
conjugator length is used. The independent --cross-check implementation expands
single-letter conjugations in forward layers with a signed-pair symmetry.

From this directory run: python3 peak_check.py [--cross-check].
Typical runtime for the primary search is a few seconds on a laptop.
"""

import argparse
from collections import defaultdict, deque
from functools import cache


INITIAL = ("xxYYY", "xyxYXY")
STANDARD = ("x", "y")
THREE_CONJUGATIONS = (
    ("I", 0), ("M", 1), ("C", 1, "xYX"), ("M", 0), ("I", 1),
    ("C", 1, "xyXX"), ("M", 1), ("C", 0, "xY"), ("I", 1),
    ("M", 0), ("M", 1), ("M", 0), ("M", 0), ("I", 1), ("M", 1),
)

# Independent witness found by Open Math OS Ultramath member 3.
KIMI_THREE_CONJUGATIONS = (
    ("I", 1), ("M", 0), ("I", 0), ("M", 1), ("C", 0, "xYX"),
    ("M", 1), ("I", 0), ("C", 0, "yyXyX"), ("M", 0), ("I", 0),
    ("C", 0, "yX"), ("M", 1), ("M", 0), ("M", 1), ("M", 0),
)

FOUR_CONJUGATIONS = (
    ("I", 0), ("M", 1), ("C", 0, "X"), ("C", 1, "YX"), ("M", 0),
    ("I", 0), ("C", 0, "yXy"), ("M", 1), ("C", 0, "xY"), ("I", 1),
    ("M", 0), ("M", 1), ("M", 1), ("I", 1), ("M", 0), ("M", 0),
)
FIVE_CONJUGATIONS = (
    ("I", 1), ("C", 1, "xYX"), ("M", 1), ("I", 0), ("C", 0, "Y"),
    ("M", 1), ("C", 0, "Xy"), ("M", 0), ("I", 0), ("C", 0, "Yx"),
    ("M", 1), ("C", 0, "xY"), ("I", 0), ("M", 0), ("M", 1),
    ("I", 1), ("I", 0), ("M", 1), ("M", 0),
)


@cache
def inverse(word):
    return word[::-1].swapcase()


def product(left, right):
    cancelled = 0
    while (cancelled < min(len(left), len(right))
           and left[-cancelled-1] == right[cancelled].swapcase()):
        cancelled += 1
    return left[:len(left)-cancelled] + right[cancelled:]


def replace(pair, row, word):
    return (word, pair[1]) if row == 0 else (pair[0], word)


def peak_size(pair):
    return len(pair[0]) + len(pair[1])


@cache
def cyclic_key(word):
    while len(word) >= 2 and word[0] == word[-1].swapcase():
        word = word[1:-1]
    return min((word[i:] + word[:i] for i in range(len(word))), default="")


@cache
def conjugate_words(key, limit):
    """All freely reduced words conjugate to key and of length at most limit.

    Their cyclically reduced cores are exactly the rotations of key. A longer
    word is formed by wrapping a shorter one in one inverse pair of letters.
    The two tests ensure that the wrapping is freely reduced.
    """
    if len(key) > limit:
        return ()
    if not key:
        return ("",)
    layer = {key[i:] + key[:i] for i in range(len(key))}
    result = list(layer)
    for _ in range((limit - len(key)) // 2):
        layer = {c + w + c.swapcase() for w in layer for c in "xXyY"
                 if c.swapcase() != w[0] and c != w[-1]}
        result.extend(layer)
    return tuple(result)


def nielsen_closure(seeds, limit, *, reverse=False, exclude=None):
    """Closure under inversion and positive right multiplication, or its reverse."""
    if exclude is None:
        exclude = set()
    known = set(seeds)
    queue = deque(known)
    while queue:
        pair = queue.popleft()
        for i in (0, 1):
            w, other = pair[i], pair[1-i]
            factor = inverse(other) if reverse else other
            for changed in (inverse(w), product(w, factor)):
                if len(changed) + len(other) > limit:
                    continue
                candidate = replace(pair, i, changed)
                if candidate not in known and candidate not in exclude:
                    known.add(candidate)
                    queue.append(candidate)
    return known


def conjugacy_signature(pair, i):
    """A single i-th conjugation joins exactly the pairs of equal signature."""
    return (i, pair[1-i], cyclic_key(pair[i]))


def minimum_cost(limit):
    """Return the minimum number of conjugations under the peak bound.

    Split a nonempty conjugation sequence immediately before the last one. The
    preceding state is in a forward layer; the state after the conjugation is
    in the reverse Nielsen closure. They agree on the untouched row and have
    the same cyclic key on the changed row. Conversely, either matching
    signature immediately joins the two pieces by one permissible move, with
    no intermediate state. Test zero conjugations separately. Expanding only
    new states is sufficient because a cheaper visit allows every continuation
    available to a more expensive one. Exhaustion certifies nonreachability.
    """
    if limit < max(peak_size(INITIAL), peak_size(STANDARD)):
        return None
    tail = nielsen_closure({STANDARD}, limit, reverse=True)
    signatures = {conjugacy_signature(pair, i) for pair in tail for i in (0, 1)}
    seen = set()
    seeds = {INITIAL}
    layer_sizes, hit_counts = [], []
    if INITIAL in tail:
        return 0
    while seeds:
        layer = nielsen_closure(seeds, limit, exclude=seen)
        layer_sizes.append(len(layer))
        hits = sum(any(conjugacy_signature(pair, i) in signatures for i in (0, 1))
                   for pair in layer)
        hit_counts.append(hits)
        seen.update(layer)
        if hits:
            break
        seeds = set()
        for pair in layer:
            for i in (0, 1):
                bound = limit - len(pair[1-i])
                for changed in conjugate_words(cyclic_key(pair[i]), bound):
                    candidate = replace(pair, i, changed)
                    if candidate not in seen:
                        seeds.add(candidate)
    print(f"cap {limit}: tail states={len(tail)}, tail signatures={len(signatures)}, "
          f"forward layers={layer_sizes}, matching states={hit_counts}")
    return len(layer_sizes) if hit_counts[-1] else None


def replay(moves, expected):
    state = INITIAL
    peak = peak_size(state)
    for move in moves:
        kind, row = move[:2]
        word = state[row]
        if kind == "I":
            changed = inverse(word)
        elif kind == "M":
            changed = product(word, state[1-row])
        else:
            conjugator = move[2]
            changed = product(product(conjugator, word), inverse(conjugator))
        state = replace(state, row, changed)
        peak = max(peak, peak_size(state))
    assert state == STANDARD
    count = sum(move[0] == "C" for move in moves)
    assert (len(moves), count, peak) == expected
    print(f"Witness: {len(moves)} moves, {count} conjugations, peak {peak}, "
          "ordered endpoint (x,y).")


def cross_check(limit):
    """Independent forward expansion with integer letters and signed unordered rows.

    Inversion and exchanging positions can be included for free. Inversions
    are legal moves and do not change length. Any exchanges can be pushed to
    the end of a path by exchanging subsequent move indices. A witnessed path
    for each positive claim is checked separately in the actual ordered graph.

    Instead of testing a cyclic key, take the connected component under
    conjugation by individual letters in the selected row; charge that whole
    excursion one conjugation. Every such excursion is a single arbitrary-word
    conjugation. Conversely, any two bounded conjugate words connect this way
    within the bound: peel their outer inverse pairs down to cyclic cores,
    rotate a core by letters, then restore the other word's outer pairs.
    """
    alphabet = (-2, -1, 1, 2)

    def reduce_word(word):
        stack = []
        for letter in word:
            if stack and stack[-1] == -letter:
                stack.pop()
            else:
                stack.append(letter)
        return tuple(stack)

    @cache
    def opposite(word):
        return tuple(-c for c in reversed(word))

    def unsigned(word):
        return min(word, opposite(word))

    def order(first, second):
        return tuple(sorted((unsigned(first), unsigned(second))))

    start = order((1, 1, -2, -2, -2), (1, 2, 1, -2, -1, -2))
    goal = order((1,), (2,))
    if limit < sum(map(len, start)):
        return None
    seeds = {start}
    seen = set()
    cost = 0
    while seeds:
        layer = set(seeds)
        queue = deque(seeds)
        while queue:
            pair = queue.popleft()
            if pair == goal:
                return cost
            for active, other in (pair, pair[::-1]):
                for a in (active, opposite(active)):
                    for b in (other, opposite(other)):
                        changed = reduce_word(a + b)
                        if len(changed) + len(other) > limit:
                            continue
                        candidate = order(changed, other)
                        if candidate not in seen and candidate not in layer:
                            layer.add(candidate)
                            queue.append(candidate)
        seen.update(layer)
        seeds = set()
        by_untouched = defaultdict(set)
        for a, b in layer:
            by_untouched[a].add(b)
            by_untouched[b].add(a)
        for other, words in by_untouched.items():
            reachable = set(words)
            queue = deque(words)
            while queue:
                word = queue.popleft()
                for c in alphabet:
                    candidate = unsigned(reduce_word((c,) + word + (-c,)))
                    if len(candidate) + len(other) <= limit and candidate not in reachable:
                        reachable.add(candidate)
                        queue.append(candidate)
            seeds.update(order(other, w) for w in reachable)
        seeds.difference_update(seen)
        cost += 1
    return None


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cross-check", action="store_true",
                        help="repeat with the independent single-letter search")
    args = parser.parse_args()
    replay(THREE_CONJUGATIONS, (15, 3, 17))
    print("Open Math OS independent ledger:")
    replay(KIMI_THREE_CONJUGATIONS, (15, 3, 17))
    replay(FOUR_CONJUGATIONS, (16, 4, 15))
    replay(FIVE_CONJUGATIONS, (19, 5, 13))
    expected = {12: None, 13: 5, 14: 5, 15: 4, 16: 4, 17: 3}
    for cap, cost in expected.items():
        assert minimum_cost(cap) == cost
        if args.cross_check:
            assert cross_check(cap) == cost
            print(f"  Independent forward letter search agrees at cap {cap}.")
