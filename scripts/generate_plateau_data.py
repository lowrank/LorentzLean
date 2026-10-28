#!/usr/bin/env python3
"""Translate supplied plateau certificates to exact Lean coefficient data.

The generated files contain data and kernel-checked root brackets. This
translation is not itself a proof of the final counterexamples. The incoming
JSON files are read only. Run from any directory; no third-party packages.
"""
from fractions import Fraction as Q
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "lean/Lorentz/Plateau/Certificates"


def trim(p):
    p = list(p)
    while p and not p[-1]:
        p.pop()
    return p


def rational(x):
    x = Q(x)
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator} / {x.denominator})"


def lean_list(items, level=0):
    if not items:
        return "[]"
    if not isinstance(items[0], list):
        tokens = [rational(x) for x in items]
        result, line = [], "["
        for i, token in enumerate(tokens):
            end = ", " if i + 1 < len(tokens) else "]"
            if len(line) + len(token) + len(end) > 96 and line != "[":
                result.append(line.rstrip())
                line = "  " * (level + 1)
            line += token + end
        result.append(line)
        return "\n".join(result)
    pad = "  " * (level + 1)
    return "[\n" + ",\n".join(pad + lean_list(x, level + 1) for x in items) + "\n" + "  " * level + "]"


def generate(kind):
    source = ROOT / f"certificates/plateau/{kind}_certificate.json"
    data = json.loads(source.read_text())
    modulus = list(map(Q, data["minimal_polynomial"]))
    degree = len(modulus) - 1

    def reduce(p):
        p = list(p)
        while len(p) > degree:
            c = p.pop()
            off = len(p) - degree
            for j in range(degree):
                p[off + j] -= c * modulus[j]
        return trim(p)

    def add(p, q):
        return trim([(p[i] if i < len(p) else Q(0)) +
                     (q[i] if i < len(q) else Q(0)) for i in range(max(len(p), len(q)))])

    def scale(p, c):
        return trim([x * c for x in p])

    def mul(p, q):
        out = [Q(0)] * max(0, len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return reduce(out)

    def evaluate(cs, x):
        out = []
        for c in reversed(cs):
            out = add(c, mul(x, out))
        return out

    def power_basis(cs):
        # Chebyshev polynomials represented as integer power coefficients.
        ts = [[Q(1)], [Q(0), Q(1)]]
        for n in range(2, len(cs)):
            ts.append(add([Q(0)] + scale(ts[-1], 2), scale(ts[-2], -1)))
        out = [[] for _ in cs]
        for c, t in zip(cs, ts):
            for k, coefficient in enumerate(t):
                out[k] = add(out[k], scale(c, coefficient))
        while out and not out[-1]:
            out.pop()
        return out

    def read(cs):
        return [reduce(list(map(Q, c))) for c in cs]

    if kind == "odd":
        forcing = power_basis(read(data["h"]))
        corrections = [power_basis(read(cs)) for cs in data["polynomials"]]
        slopes = read(data["lambdas"])
        slacks = [read(cs) for cs in data["slacks"]]
        active = data["active"]
        degrees = data["degrees"]
        ngrid = 18
    else:
        degrees = [1, 3, 5, 7]
        forcing = power_basis(read(data["forcing_chebyshev"]))
        corrections = [power_basis(read(data["correction_chebyshev"][str(n)])) for n in degrees]
        slopes = read([data["error_corrections"][str(n)] for n in degrees])
        slacks = [read(data["slacks"][str(n)]) for n in degrees]
        active = [data["chosen_alternations"][str(n)] for n in degrees]
        ngrid = 36

    cosines = [[Q(2)], [Q(0), Q(1)]]
    for _ in range(2, 2 * ngrid):
        cosines.append(add(mul([Q(0), Q(1)], cosines[-1]), scale(cosines[-2], -1)))
    nodes = [scale(cosines[2 * j + 1], Q(-1, 2)) for j in range(ngrid)]
    node_indices = {tuple(x): i for i, x in enumerate(nodes)}
    mapping = [node_indices[tuple(add(scale(mul(mul(x, x), x), 4), scale(x, -3)))] for x in nodes]
    rho = Q(-3, 5)
    values = []
    seeds = [evaluate(forcing, x) for x in nodes]
    for i in range(ngrid):
        seen, orbit = {}, []
        j = i
        while j not in seen:
            seen[j] = len(orbit)
            orbit.append(j)
            j = mapping[j]
        start = seen[j]
        period = len(orbit) - start
        head, tail = [], []
        for k, j in enumerate(orbit[:start]):
            head = add(head, scale(seeds[j], rho ** k))
        for k, j in enumerate(orbit[start:]):
            tail = add(tail, scale(seeds[j], rho ** k))
        values.append(add(head, scale(tail, rho ** start / (1 - rho ** period))))
    if kind == "odd":
        assert mapping == data["cubic_map"]
        assert values == read(data["grid_H"])
    for i in range(ngrid):
        assert values[i] == add(seeds[i], scale(values[mapping[i]], rho))

    # A shorter exact bracket makes the kernel arithmetic much cheaper.
    old_l, old_u = map(Q, data["root_interval"])
    denominator = 10 ** 30
    lower = Q((old_l * denominator).__floor__(), denominator)
    upper = Q((old_u * denominator).__ceil__(), denominator)

    def rat_eval(p, x):
        result = Q(0)
        for c in reversed(p):
            result = c + x * result
        return result

    assert lower <= old_l < old_u <= upper
    assert rat_eval(modulus, lower) < 0 < rat_eval(modulus, upper)
    namespace = "Odd" if kind == "odd" else "Even"
    lines = ["module", "", "public import Lorentz.Plateau.FiniteTools", "",
             "@[expose] public section", "", "set_option maxRecDepth 100000", "",
             f"/-! Exact {kind} plateau data, generated by `scripts/generate_plateau_data.py`.",
             f"Input SHA256: {hashlib.sha256(source.read_bytes()).hexdigest()}.",
             "Data alone do not assert a counterexample theorem. -/", "",
             f"namespace Lorentz.Plateau.Certificates.{namespace}", "",
             f"def modulusCoeffs : List ℚ := {lean_list(modulus)}", "",
             f"def rootLower : ℚ := {rational(lower)}",
             f"def rootUpper : ℚ := {rational(upper)}", "",
             "theorem root_order : rootLower ≤ rootUpper := by decide +kernel",
             "theorem root_lower_negative :",
             "    FiniteTools.evalRational modulusCoeffs rootLower < 0 := by decide +kernel",
             "theorem root_upper_positive :",
             "    0 < FiniteTools.evalRational modulusCoeffs rootUpper := by decide +kernel", "",
             "theorem exists_root : ∃ z : ℝ, (rootLower : ℝ) ≤ z ∧ z ≤ (rootUpper : ℝ) ∧",
             "    Certificate.eval modulusCoeffs z = 0 :=",
             "  FiniteTools.exists_root modulusCoeffs rootLower rootUpper root_order",
             "    root_lower_negative.le root_upper_positive.le", ""]
    def emit_table(name, value, depth, base):
        # Separate coefficient vectors avoid a large pending metavariable
        # problem when elaborating hundreds of rational divisions at once.
        typename = base
        for _ in range(depth):
            typename = f"List ({typename})"
        if depth == 1 or not value:
            body = lean_list(value, 1)
        else:
            children = []
            for i, row in enumerate(value):
                child = f"{name}_{i}"
                emit_table(child, row, depth - 1, base)
                children.append(child)
            body = "[\n    " + ",\n    ".join(children) + "\n  ]"
        lines.extend([f"def {name} : {typename} :=", "  " + body, ""])

    for name, depth, base, value in [
        ("forcingCoeffs", 2, "ℚ", forcing),
        ("correctionRows", 3, "ℚ", corrections),
        ("slopeRows", 2, "ℚ", slopes),
        ("nodeRows", 2, "ℚ", nodes),
        ("gridValues", 2, "ℚ", values),
        ("slackRows", 3, "ℚ", slacks),
        ("cubicMap", 1, "ℕ", mapping),
        ("degrees", 1, "ℕ", degrees),
        ("activeRows", 2, "ℕ", active),
    ]:
        emit_table(name, value, depth, base)
    lines.extend([f"end Lorentz.Plateau.Certificates.{namespace}", ""])
    text = "\n".join(lines)
    if len(text.splitlines()) > 10000:
        raise ValueError(f"{namespace}Data exceeds Palomar's source-file limit")
    OUTPUT.mkdir(parents=True, exist_ok=True)
    destination = OUTPUT / f"{namespace}Data.lean"
    destination.write_text(text)
    print(f"Generated {destination.relative_to(ROOT)} ({len(text.splitlines())} lines)")


if __name__ == "__main__":
    for kind in ("odd", "even"):
        generate(kind)
