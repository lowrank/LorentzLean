#!/usr/bin/env python3
"""Independently check the finite data used by the paper, using exact fractions.

Run from any directory with Python 3.9+. Reads the checked-in Lean coefficient
tables; no Lean, symbolic algebra package, floating-point decisions, or external
certificate file is needed. This is a reproducibility check, not a replacement
for the Lean kernel or the paper's whole-interval analytic argument.
"""

import ast
from fractions import Fraction as F
from itertools import permutations
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
DATA = (ROOT / "lean/Lorentz/CertificateData.lean").read_text()
GRID = (ROOT / "lean/Lorentz/CertificateGrid.lean").read_text()
MODULUS = list(map(F, [1, 0, -36, 0, 105, 0, -112, 0, 54, 0, -12, 0, 1]))
CHECKS = 0


def check(condition, message):
    global CHECKS
    if not condition:
        raise AssertionError(message)
    CHECKS += 1


def parse_literal(text):
    def visit(node):
        if isinstance(node, ast.List):
            return [visit(x) for x in node.elts]
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return F(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            return visit(node.left) / visit(node.right)
        raise ValueError(f"Unsupported coefficient syntax: {ast.dump(node)}")
    return visit(ast.parse(text, mode="eval").body)


def table(name):
    start = DATA.index("[", DATA.index(":=", DATA.index("def " + name + " ")))
    depth = 0
    for i in range(start, len(DATA)):
        depth += (DATA[i] == "[") - (DATA[i] == "]")
        if not depth:
            return parse_literal(DATA[start:i + 1])
    raise ValueError(name)


def grid_table(name):
    block = GRID.split("def " + name + " ", 1)[1].split("\ndef ", 1)[0]
    return {int(j): parse_literal(p) for j, p in
            re.findall(r"\| (\d+) => (\[[^\n]*\])", block)}


def trim(p):
    p = list(p)
    while p and p[-1] == 0:
        p.pop()
    return p


def reduce(p):
    p = trim(p)
    while len(p) > 12:
        c, offset = p[-1], len(p) - 13
        for i, m in enumerate(MODULUS):
            p[offset + i] -= c * m
        p = trim(p)
    return p


def const(c):
    return trim([F(c)])


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def scale(c, p):
    return trim([F(c) * x for x in p])


def sub(p, q):
    return add(p, scale(-1, q))


def mul(p, q):
    if not p or not q:
        return []
    out = [F(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i + j] += a * b
    return reduce(out)


def power(p, n):
    result = const(1)
    for _ in range(n):
        result = mul(result, p)
    return result


def cheb(p, n):
    a, b = const(1), p
    for _ in range(n):
        a, b = b, sub(scale(2, mul(p, b)), a)
    return a


def evaluate(p, x):
    y = F(0)
    for a in reversed(p):
        y = a + x * y
    return y


def enclosure(p, lo, hi):
    left = right = F(0)
    for a in reversed(p):
        products = [lo * left, lo * right, hi * left, hi * right]
        left, right = a + min(products), a + max(products)
    return left, right


def determinant(matrix):
    result = []
    for perm in permutations(range(len(matrix))):
        inversions = sum(perm[i] > perm[j] for i in range(len(perm))
                         for j in range(i + 1, len(perm)))
        term = const((-1) ** inversions)
        for i, j in enumerate(perm):
            term = mul(term, matrix[i][j])
        result = add(result, term)
    return result


lo, hi = F(199238939, 100000000), F(199238940, 100000000)
check(evaluate(MODULUS, lo) < 0 < evaluate(MODULUS, hi), "root endpoint signs")
# The paper proves m is strictly increasing here. Bisection preserves this root.
for _ in range(100):
    mid = (lo + hi) / 2
    if evaluate(MODULUS, mid) < 0:
        lo = mid
    else:
        hi = mid

BETA = table("betaCoeffs")
expected_beta = scale(F(1, 107), list(map(F,
    [-60, 82, 1086, 1576, -2932, -3433, 2002, 2243, -510, -587, 44, 54])))
check(BETA == expected_beta, "explicit beta formula")
check(F(419, 1000) < enclosure(BETA, lo, hi)[0] and
      enclosure(BETA, lo, hi)[1] < F(420, 1000), "beta interval")
NODES, H0, H1 = (grid_table(s) for s in ["nodeCoeffs", "h0Coeffs", "h1Coeffs"])
SLACKS, CHEB, ACTIVE = (table(s) for s in ["slackRows", "chebyshevRows", "activeRows"])
V = {s: table(s + "Coeffs") for s in
     ["v1", "v31", "v32", "v33", "v41", "v43", "v51", "v53", "v55"]}
SLOPES = [table("t" + str(n) + "Coeffs") for n in [0, 1, 1, 3, 4, 5, 5]]


def correction(n, x):
    if n == 0:
        return []
    if n <= 2:
        return mul(V["v1"], x)
    if n == 3:
        return add(add(mul(V["v31"], x), mul(V["v32"], power(x, 2))),
                   mul(V["v33"], power(x, 3)))
    prefix = "v4" if n == 4 else "v5"
    result = add(sub(cheb(x, 4), const(1)),
                 add(mul(V[prefix + "1"], x), mul(V[prefix + "3"], cheb(x, 3))))
    return result if n == 4 else add(result, mul(V["v55"], cheb(x, 5)))


def grid_h(j):
    return add(H0[j], mul(BETA, H1[j]))


def seed(x):
    return add(sub(sub(cheb(x, 4), const(1)), scale(2, cheb(x, 5))),
               mul(BETA, cheb(x, 7)))


def sign(j):
    return 1 if j % 4 in (0, 3) else -1


two_beta = add(const(2), BETA)
check(sub(V["v1"], scale(-1, two_beta)) == [], "v1 formula")
a = NODES[13]
check(sub(power(a, 2), const(F(1, 2))) == [] and enclosure(a, lo, hi)[0] > 0,
      "positive quarter-period node")
c6 = cheb([F(0), F(1, 2)], 6)
check(sub(SLOPES[0], mul(mul(a, c6), two_beta)) == [], "lambda0 formula")
check(sub(SLOPES[1], scale(F(1, 2), mul(a, two_beta))) == [], "lambda1 formula")
cubic_indices = [1, 4, 7, 10, 13, 16, 16, 13, 10, 7, 4, 1, 1, 4, 7, 10, 13, 16]
for j in range(18):
    x = NODES[j]
    check(sub(x, scale(-1, cheb([F(0), F(1, 2)], 2 * j + 1))) == [], f"node {j+1}")
    check(cheb(x, 18) == [], f"T18 zero {j+1}")
    check(sub(cheb(x, 9), scale(-sign(j), a)) == [], f"baseline contact sign {j+1}")
    check(sub(cheb(x, 3), NODES[cubic_indices[j]]) == [], f"cubic image {j+1}")
    r = sub(sub(cheb(x, 4), scale(F(1, 3), cheb(x, 12))), const(F(5, 6)))
    r = add(sub(r, scale(2, cheb(x, 5))), mul(BETA, cheb(x, 7)))
    r = add(r, mul(two_beta, add(scale(F(1, 3), cheb(x, 15)),
                                scale(F(1, 6), cheb(x, 9)))))
    check(sub(r, grid_h(j)) == [], f"grid forcing value {j+1}")
    check(sub(grid_h(j), sub(seed(x), scale(F(1, 3), grid_h(cubic_indices[j])))) == [],
          f"grid recurrence {j+1}")
    left, right = enclosure(x, lo, hi)
    check(-1 < left <= right < 1, f"interior node {j+1}")
    if j:
        check(enclosure(NODES[j-1], lo, hi)[1] < left, f"ordered node {j+1}")

ZEROS = [[3, 4], [1, 3, 4, 6], [1, 3, 4, 6], [1, 3, 8, 10, 16],
         [1, 3, 8, 9, 10, 16, 18], [3, 4, 6, 9, 10, 13, 15, 16],
         [3, 4, 6, 9, 10, 13, 15, 16]]
LOWER = list(map(F, ["127/50", "363/100", "363/100", "9/100", "7/10", "1/5", "1/5"]))
NORM_UPPER = [F(0), F(5, 2), F(5, 2), F(9, 4), F(13, 4), F(11, 2), F(11, 2)]
for n in range(7):
    check(0 < enclosure(SLOPES[n], lo, hi)[0] and enclosure(SLOPES[n], lo, hi)[1] < 2,
          f"positive slope {n}")
    check(correction(n, []) == [], f"origin value {n}")
    # Degree <= 6 makes equality at seven distinct rational points decisive.
    for t in range(-3, 4):
        x, value = const(F(t, 3)), []
        for k, coefficient in enumerate(CHEB[n]):
            value = add(value, mul(coefficient, cheb(x, k)))
        check(sub(value, correction(n, x)) == [], f"Chebyshev coefficients {n}, {t}")
    norms = [max(map(abs, enclosure(p, lo, hi))) for p in CHEB[n]]
    check(sum(norms) < NORM_UPPER[n] if n else sum(norms) == 0, f"coefficient norm {n}")
    check(sum(k*k*v for k, v in enumerate(norms)) < 216, f"derivative mass {n}")
    zeros = []
    for j in range(6 if n < 3 else 18):
        index, sigma = (3*j+1, -sign(j)) if n < 3 else (j, sign(j))
        slack = sub(SLOPES[n], scale(sigma, sub(grid_h(index), correction(n, NODES[index]))))
        check(sub(slack, SLACKS[n][j]) == [], f"slack polynomial {n}, {j+1}")
        if not slack:
            zeros.append(j+1)
        else:
            check(enclosure(slack, lo, hi)[0] > LOWER[n], f"strict slack {n}, {j+1}")
    check(zeros == ZEROS[n], f"complete zero set {n}")
    active = [int(x) for x in ACTIVE[n]]
    check(len(active) == n+2 and all(x < y for x, y in zip(active, active[1:])),
          f"ordered active indices {n}")
    check(all(j+1 in zeros for j in active), f"active equalities {n}")
    check(all(sign(x) == -sign(y) for x, y in zip(active, active[1:])), f"alternation {n}")

for n, indices, powers in [(3, [1, 3, 8, 10], [1, 2, 3]),
                            (4, [10, 16, 18], [1, 3]),
                            (5, [10, 13, 15, 16], [1, 3, 5])]:
    matrix = []
    for j in indices:
        x = NODES[j-1]
        row = [(power(x, k) if n == 3 else cheb(x, k)) for k in powers]
        matrix.append(row + [const(sign(j-1))])
    low, high = enclosure(determinant(matrix), lo, hi)
    check(high < 0 or low > 0, f"nonsingular defining system {n}")

print(f"PASS: {CHECKS} exact finite-certificate checks.")
print("All equality decisions use rational polynomial arithmetic modulo m.")
print("All strict inequalities use rational interval bounds; no floating-point decisions.")
