"""Minimum conjugation count for MS(2,w*) at its smallest possible peak 12."""

from collections import deque
from functools import lru_cache

from witness_check import inverse, reduce_word, replay, source, uniform_moves


@lru_cache(None)
def cyclic_key(word):
    while len(word) >= 2 and word[0] == inverse(word[-1]):
        word = word[1:-1]
    return min((word[i:] + word[:i] for i in range(len(word))), default="")


@lru_cache(None)
def all_conjugates(key, limit):
    # Every reduced conjugate wraps an inverse pair of words around a rotation.
    # Starting at those rotations, grow one freely reduced outer pair at a time.
    if not key:
        return ("",)
    words = set(key[i:] + key[:i] for i in range(len(key)))
    pending = list(words)
    for w in pending:
        for a in "xXyY":
            if len(w) + 2 <= limit and w[0] != inverse(a) and w[-1] != a:
                v = a + w + inverse(a)
                if v not in words:
                    words.add(v)
                    pending.append(v)
    return tuple(words)


def min_conjugations(start, peak):
    if sum(map(len, start)) > peak:
        raise ValueError("The initial pair already exceeds the peak")
    best = {start: 0}
    queue = deque([(start, 0)])
    expanded = set()
    while queue:
        pair, d = queue.popleft()
        if d != best[pair]:
            continue
        if pair == ("x", "y"):
            return d
        for i in range(2):
            a, b = pair[i], pair[1-i]
            for v in (inverse(a), reduce_word(a + b)):
                dest = (v, b) if i == 0 else (b, v)
                if len(v) + len(b) <= peak and (dest not in best or d < best[dest]):
                    best[dest] = d
                    queue.appendleft((dest, d))
            # The first popped member has least cost within this conjugacy class.
            # All its members have the same cost-one neighbors.
            signature = (i, b, cyclic_key(a))
            if signature in expanded:
                continue
            expanded.add(signature)
            for v in all_conjugates(signature[2], peak - len(b)):
                dest = (v, b) if i == 0 else (b, v)
                if dest not in best or d+1 < best[dest]:
                    best[dest] = d + 1
                    queue.append((dest, d+1))
    return None


if __name__ == "__main__":
    start = source(2)
    peak = sum(map(len, start))
    cost = min_conjugations(start, peak)
    if (peak, cost) != (12, 5) or replay(2, uniform_moves(2), 5) != (16, 5, 12):
        raise RuntimeError("Peak certificate failed")
    print("At n=2 and the minimum peak 12, the minimum is 5 conjugations.")
