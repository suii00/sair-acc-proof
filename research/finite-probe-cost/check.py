"""Finite examples for stable multiplication-cost bounds on P_L and Q_L.

Run with Python 3.9+. The infinite-family proof uses the seam and Fibonacci
inequalities; bounded enumeration here independently checks the conventions.
"""
from itertools import permutations, product
from math import lcm


def inverse(word):
    return word[::-1].swapcase()


def reduce_word(word):
    stack = []
    for char in word:
        if stack and stack[-1] == char.swapcase():
            stack.pop()
        else:
            stack.append(char)
    return "".join(stack)


def cyclic_core(word):
    word = reduce_word(word)
    while len(word) > 1 and word[0].swapcase() == word[-1]:
        word = word[1:-1]
    return word


def score(word):
    return word.count("xy") - word.count("YX")


def cyclic_score(word):
    core = cyclic_core(word)
    return score(core + core[:1])


def relator(exponent):
    return "y" + "xyXY" * exponent


def strip_one(rows):
    # Conjugate row 0 by y, multiply row 1, conjugate back; subtract row 0.
    a, b = rows
    a = reduce_word("y" + a + "Y")
    b = reduce_word(b + a)
    a = reduce_word("Y" + a + "y")
    a = inverse(a)
    b = reduce_word(b + a)
    a = inverse(a)
    return a, b


def strip_derived_block(rows):
    """Append w^-1 = b^-1 a^2 b^-1 a^-1 b^2 a^-1; a=x, b=yxY."""
    a, r = rows
    height, sign = 0, 1
    counts = [0, 0, 0]  # right multiplications, conjugations, inversions
    for target_height, target_sign in ((1, -1), (0, 1), (0, 1), (1, -1),
                                      (0, -1), (1, 1), (1, 1), (0, -1)):
        if target_height != height:
            by = "y" if target_height else "Y"
            a = reduce_word(by + a + inverse(by))
            counts[1] += 1
        if target_sign != sign:
            a = inverse(a)
            counts[2] += 1
        r = reduce_word(r + a)
        counts[0] += 1
        height, sign = target_height, target_sign
    a = inverse(a)
    counts[2] += 1
    assert counts == [8, 6, 6]
    return a, r


def strip_derived_block_four(rows, d):
    """Append (d a D)(d b^-1 D)b a^-1 with four right multiplications."""
    helper, rel = rows
    previous_frame, previous_sign = "", 1
    for frame, sign in ((d, 1), (d + "y", -1), ("y", 1), ("", -1)):
        by = reduce_word(frame + inverse(previous_frame))
        helper = reduce_word(by + helper + inverse(by))
        if sign != previous_sign:
            helper = inverse(helper)
        rel = reduce_word(rel + helper)
        previous_frame, previous_sign = frame, sign
    return inverse(helper), rel


def strip_first_exponent(rows):
    """Ordinary descent on Q_1 with exactly two positive right multiplications."""
    helper, rel = rows
    p, q = "yx", "yXYx"
    def conjugate(by, word):
        return reduce_word(by + word + inverse(by))
    helper = conjugate(q, helper)
    rel = reduce_word(rel + helper)
    helper = conjugate(reduce_word(q + "y" + inverse(q)), inverse(helper))
    rel = reduce_word(rel + helper)
    helper = inverse(conjugate(inverse(q + "y"), helper))
    return helper, conjugate(inverse(p), rel)


def batch_deletion_certificate(exponent):
    """Dots delete signed a or b letters from (aBBabAAb)^L; the rest cancels."""
    block = "aBBabAAb"
    anchor = "..Bab..b"
    cycle = (".BBab.A.", "aBBa.AAb", "a..a.AAb", "a.B.bAAb", ".BBab..b")
    tails = {
        2: (".BBa.AAb",),
        3: (".BBab.A.", "aBB.bAAb"),
        4: (".BBab.A.", "aBBa.AAb", "..BabAAb"),
        5: (".BBab.A.", "aBBa.AAb", "a..a.AAb", ".BBabAAb"),
        6: (".BBab.A.", "aBBa.AAb", "a..a.AAb", "a.B.bAA.", block),
        7: (".BBab.A.", "aBBa.AAb", "a..a.AAb", "a.B.bAAb", ".BBa..Ab", block),
    }
    if exponent == 1:
        masks = ("..Ba..Ab",)
    else:
        repeats, residue = divmod(exponent - 2, 6)
        masks = (anchor,) + cycle * repeats + tails[residue + 2] + (block,) * repeats
    assert len(masks) == exponent
    for mask in masks:
        assert len(mask) == len(block)
        assert all(ch == "." or ch == letter for ch, letter in zip(mask, block))
    pattern = "".join(masks)
    assert pattern.count(".") == 2 * exponent + 2
    assert reduce_word(pattern.replace(".", "")) == ""
    # Inserting the five edited blocks after the anchor and one intact block
    # at the end preserves triviality of the kept word, for every exponent.
    h = anchor.replace(".", "")
    g = "".join(cycle).replace(".", "")
    assert sum(mask.count(".") for mask in cycle) == 12
    assert reduce_word(h + g + inverse(h)) == inverse(block)
    return masks


def replay_deletion_path(masks, law):
    """Turn the deletion certificate into a chronological ordinary AC path."""
    images = {"a": "x", "b": "yxY", "A": "X", "B": "yXY"}
    prefix = ""
    factors = []
    for mask in masks:
        for letter, kept in zip("aBBabAAb", mask):
            if kept == ".":
                # A deleted b is a conjugate of x with one extra y in the frame.
                frame = reduce_word(prefix + ("y" if letter.lower() == "b" else ""))
                factors.append((frame, letter.isupper()))
            else:
                prefix = reduce_word(prefix + images[letter])
    assert prefix == ""
    helper = "x"
    relator_row = "y" + law * len(masks)
    for frame, originally_negative in reversed(factors):
        # Append the inverse of this factor, then restore the helper row to x.
        helper = reduce_word(frame + helper + inverse(frame))
        if not originally_negative:
            helper = inverse(helper)
        relator_row = reduce_word(relator_row + helper)
        if not originally_negative:
            helper = inverse(helper)
        helper = reduce_word(inverse(frame) + helper + frame)
    assert (helper, relator_row) == ("x", "y")
    assert len(factors) == 2 * len(masks) + 2


def marked_score(word, generators):
    """Maximum of the absolute cyclic score over maps to 1,x,y."""
    best = 0
    for marking in product(("", "x", "y"), repeat=len(generators)):
        image = dict(zip(generators, marking))
        projected = "".join(image[c] if c.islower() else inverse(image[c.lower()])
                            for c in word)
        best = max(best, abs(cyclic_score(projected)))
    return best


def words_through(length):
    row = [""]
    words = row.copy()
    for _ in range(length):
        row = [w + c for w in row for c in "xyXY"
               if not w or w[-1] != c.swapcase()]
        words.extend(row)
    return words


def first_fibonacci_bound(weight):
    """Smallest m with F_(m+2) >= weight, using F_1=F_2=1."""
    smaller = larger = 1
    moves = 0
    while weight > larger:
        smaller, larger = larger, smaller + larger
        moves += 1
    return moves


def mul(a, b):
    return tuple(a[i] for i in b)


def evaluate(word, x, y):
    identity = tuple(range(len(x)))
    letters = {"x": x, "y": y, "X": tuple(x.index(i) for i in identity),
               "Y": tuple(y.index(i) for i in identity)}
    result = identity
    for c in word:
        result = mul(result, letters[c])
    return result


def check_law(group, word):
    identity = tuple(range(len(group[0])))

    for x, y in product(group, repeat=2):
        if evaluate(word, x, y) != identity:
            raise ValueError("The marked pair differs from the standard pair")
    return len(group) ** 2


def check():
    for exponent in range(1, 129):
        start = ("x", relator(exponent))
        assert strip_one(start) == ("x", relator(exponent - 1))
        assert cyclic_core(start[1]) == "y" + "XYxy" * (exponent - 1)
        assert cyclic_score(start[1]) == exponent - 1
    rows = ("x", relator(128))
    for _ in range(128):
        rows = strip_one(rows)
    assert rows == ("x", "y")
    print("Six-step descent and cyclic formula hold for 1 <= L <= 128.")

    # A fixed law in every metabelian group using the same cyclic score.
    c = "xyXY"
    d = reduce_word("X" + c + "x")
    derived_law = reduce_word(c + d + inverse(c) + inverse(d))
    assert derived_law == "xyXXYxyxYXXyxY"
    assert strip_first_exponent(("x", "y" + derived_law)) == ("x", "y")
    print("Q_1 reaches (x,y) with exactly two positive right multiplications.")
    a, b = "x", "yxY"
    assert reduce_word(a + inverse(b)*2 + a + b + inverse(a)*2 + b) == derived_law
    for exponent in range(1, 129):
        word = "y" + derived_law * exponent
        assert cyclic_score(word) == exponent
        assert strip_derived_block(("x", word)) == ("x", "y" + derived_law*(exponent-1))
        assert strip_derived_block_four(("x", word), d) == ("x", "y" + derived_law*(exponent-1))
        masks = batch_deletion_certificate(exponent)
        if exponent <= 19:
            replay_deletion_path(masks, derived_law)
    print("Second-derived law: 20-step descent and score L through L=128.")
    print("Four right multiplications remove each second-derived block for L=1..128.")
    print("Batched deletion uses 2L+2 signed conjugates of x; all six base cases and L=1..128 pass.")
    print("The paths reconstructed from the masks reach the ordered basis for L=1..19.")

    square = tuple(range(4))
    dihedral = [tuple((k + s*i) % 4 for i in square) for k in square for s in (-1, 1)]
    for name, group in (("S3", list(permutations(range(3)))), ("D8", dihedral)):
        tested = check_law(group, derived_law)
        print(f"Second-derived law holds on all {tested} ordered markings of {name}.")
    assert evaluate(derived_law, (0, 2, 3, 1), (1, 0, 2, 3)) == (3, 2, 1, 0)

    # In the three-seam formula all present directions are distinct.
    for a, b, c in permutations("xyXY", 3):
        seams = (score(inverse(a) + c), score(inverse(a) + b),
                 score(inverse(b) + c))
        assert sum(value != 0 for value in seams) <= 1

    words = words_through(3)
    scores = {a: cyclic_score(a) for a in words}
    max_raw, max_cyclic = 0, 0
    for a, b in product(words, repeat=2):
        ab = reduce_word(a + b)
        raw = abs(score(ab) - score(a) - score(b))
        cyclic = abs(cyclic_score(ab) - scores[a] - scores[b])
        assert raw <= 1 and cyclic <= 2
        assert cyclic_score(b + a + inverse(b)) == scores[a]
        assert cyclic_score(inverse(a)) == -scores[a]
        max_raw = max(max_raw, raw)
        max_cyclic = max(max_cyclic, cyclic)
    print(f"Raw/cyclic defect maxima on {len(words)**2} word pairs: "
          f"{max_raw}/{max_cyclic}.")

    # Relabel old generators x,y as z,x and stabilize at fresh index y.
    rename = str.maketrans("xyXY", "zxZX")
    assert marked_score("y", "xzy") == 0
    samples = ("", "x", relator(5), "y" + derived_law*3)
    for word in samples:
        extended = word.translate(rename)
        old_value = marked_score(word, "xy")
        assert marked_score(extended, "xzy") == old_value
        assert marked_score("y" + extended + "Y", "xzy") == old_value
        for other in samples:
            helper = other.translate(rename)
            assert marked_score(extended + helper, "xzy") <= (
                old_value + marked_score(helper, "xzy") + 2)
    print("Stabilization, conjugation by a fresh generator, and rank-3 norm checks pass.")

    for degree in (3, 4):
        exponent = lcm(*range(1, degree+1))
        tested = check_law(list(permutations(range(degree))), "xyXY" * exponent)
        print(f"S{degree}: distance zero on all {tested} markings at L={exponent}.")

    for bound, expected in ((6, 9), (10, 16), (20, 40)):
        exponent = lcm(*range(1, bound+1))
        # For P_L the elementary pair-counting proof gives F >= ceil((L+1)/2).
        elementary = first_fibonacci_bound((exponent + 2) // 2)
        # Heuer's defect-one theorem gives F >= L for both P_L and Q_L.
        strengthened = first_fibonacci_bound(exponent)
        assert strengthened == expected
        print(f"All permutation degrees <= {bound}: L={exponent}, "
              f"elementary lower bound on P_L {elementary}, "
              f"defect-one lower bound on both families {strengthened}.")


if __name__ == "__main__":
    if not __debug__:
        raise SystemExit("Run without -O to enable the checks.")
    check()
