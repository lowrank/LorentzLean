#!/usr/bin/env python3
"""Translate supplied plateau certificates to kernel-checked Lean proofs.

The generated files prove root brackets, recurrences, signs, slacks, and
initial plateaus using the shared analytic persistence theorem. Python is
only a generator: Lean checks every emitted identity and inequality. The
incoming JSON files are read only. Run anywhere; no third-party packages.
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
    lines.extend([
        "noncomputable def forcing (z : ℝ) : Polynomial ℝ :=",
        "  FiniteTools.fieldPolynomial forcingCoeffs z", "",
        "noncomputable def correction (i : ℕ) (z : ℝ) : Polynomial ℝ :=",
        "  FiniteTools.fieldPolynomial (correctionRows.getD i []) z", "",
        "def node (z : ℝ) (j : ℕ) : ℝ := Certificate.eval (nodeRows.getD j []) z",
        "def value (z : ℝ) (j : ℕ) : ℝ := Certificate.eval (gridValues.getD j []) z",
        "def slope (z : ℝ) (i : ℕ) : ℝ := Certificate.eval (slopeRows.getD i []) z", "",
        "def gridIndex (i j : ℕ) : ℕ := " + ("if i = 0 then 3 * j + 1 else j" if kind == "odd"
                                                    else "if i < 3 then 3 * j + 1 else j"),
        "def gridSign (i j : ℕ) : ℚ :=",
        "  let s : ℚ := if j % 4 = 0 ∨ j % 4 = 3 then 1 else -1",
        "  " + ("if i = 0 then -s else s" if kind == "odd" else "if i < 3 then s else -s"), "",
        f"theorem forcing_degree (z : ℝ) : (forcing z).natDegree ≤ {len(forcing)-1} :=",
        "  (FiniteTools.fieldPolynomial_degree forcingCoeffs z).trans (by decide +kernel)", "",
    ])
    lines.extend([f"end Lorentz.Plateau.Certificates.{namespace}", ""])
    text = "\n".join(lines)
    if len(text.splitlines()) > 10000:
        raise ValueError(f"{namespace}Data exceeds Palomar's source-file limit")
    OUTPUT.mkdir(parents=True, exist_ok=True)
    destination = OUTPUT / f"{namespace}Data.lean"
    if not destination.exists() or destination.read_text() != text:
        destination.write_text(text)
    print(f"Generated {destination.relative_to(ROOT)} ({len(text.splitlines())} lines)")

    def raw_mul(p, q):
        out = [Q(0)] * max(0, len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return trim(out)

    def raw_evaluate(cs, x):
        out = []
        for c in reversed(cs):
            out = add(c, raw_mul(x, out))
        return out

    def quotient(p):
        p = trim(p)
        quot = [Q(0)] * max(0, len(p) - degree)
        while len(p) > degree:
            c = p.pop()
            off = len(p) - degree
            quot[off] = c
            for j in range(degree):
                p[off + j] -= c * modulus[j]
        assert not trim(p), "An asserted certificate identity has nonzero remainder"
        return trim(quot)

    def header():
        return ["module", "", f"public import Lorentz.Plateau.Certificates.{namespace}Data",
                "public import Lorentz.Plateau.Certificates.Checker", "",
                "@[expose] public section", "", "set_option maxRecDepth 100000",
                "set_option maxHeartbeats 4000000", "set_option Elab.async false", "",
                "/-! Generated exact identities. Each certificate is checked by Lean's kernel. -/", "",
                f"namespace Lorentz.Plateau.Certificates.{namespace}", ""]

    def save(name, result):
        result.extend([f"end Lorentz.Plateau.Certificates.{namespace}", ""])
        content = "\n".join(result)
        if len(content.splitlines()) > 10000:
            raise ValueError(f"{name} exceeds the source-file limit")
        target = OUTPUT / (namespace + name + ".lean")
        if not target.exists() or target.read_text() != content:
            target.write_text(content)
        print(f"Generated {target.relative_to(ROOT)} ({len(content.splitlines())} lines)")

    result = header()
    for j, k in enumerate(mapping):
        q = quotient(add(add(values[j], scale(raw_evaluate(forcing, nodes[j]), -1)),
                         scale(values[k], -rho)))
        result.extend([
            f"def recurrenceQuotient{j} : List ℚ :=", "  " + lean_list(q, 1), "",
            f"theorem recurrence_{j} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :",
            f"    value z {j} = (forcing z).eval (node z {j}) + (-3 / 5 : ℝ) * value z {k} := by",
            "  simpa only [value, forcing, node, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat] using",
            f"    Checker.recurrence forcingCoeffs (nodeRows.getD {j} []) (gridValues.getD {j} [])",
            f"      (gridValues.getD {k} []) recurrenceQuotient{j} modulusCoeffs (-3 / 5) z hm",
            "      (by decide +kernel)", "",
        ])
    result.extend([
        "theorem all_recurrences (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
        f"    (j : Fin {ngrid}) : value z j = (forcing z).eval (node z j) +",
        "      (-3 / 5 : ℝ) * value z (cubicMap.getD j 0) := by", "  fin_cases j",
    ])
    for j in range(ngrid):
        result.append(f"  · exact recurrence_{j} z hm")
    save("Recurrences", result)

    for i, row in enumerate(slacks):
        result = header()
        for j, slack in enumerate(row):
            k = 3 * j + 1 if (i == 0 if kind == "odd" else i < 3) else j
            s = Q(1 if j % 4 in (0, 3) else -1)
            if i == 0 if kind == "odd" else i == 3:
                s = -s
            difference = add(slopes[i], scale(add(values[k], scale(raw_evaluate(corrections[i], nodes[k]), -1)), -s))
            q = quotient(add(difference, scale(slack, -1)))
            result.extend([
                f"def slackQuotient{i}_{j} : List ℚ :=", "  " + lean_list(q, 1), "",
                f"theorem slack_{i}_{j} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :",
                f"    slope z {i} - ({rational(s)} : ℝ) * (value z {k} -",
                f"      (correction {i} z).eval (node z {k})) =",
                f"      Certificate.eval ((slackRows.getD {i} []).getD {j} []) z := by",
                "  simpa only [slope, value, correction, node, Rat.cast_neg, Rat.cast_one] using",
                f"    Checker.slack (correctionRows.getD {i} []) (nodeRows.getD {k} [])",
                f"      (gridValues.getD {k} []) (slopeRows.getD {i} [])",
                f"      ((slackRows.getD {i} []).getD {j} []) slackQuotient{i}_{j} modulusCoeffs",
                f"      ({rational(s)}) z hm (by decide +kernel)", "",
            ])
        result.extend([
            f"theorem all_slacks_{i} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
            f"    (j : Fin {len(row)}) : slope z {i} - (gridSign {i} j : ℝ) *",
            f"      (value z (gridIndex {i} j) - (correction {i} z).eval (node z (gridIndex {i} j))) =",
            f"      Certificate.eval ((slackRows.getD {i} []).getD j []) z := by", "  fin_cases j",
        ])
        for j in range(len(row)):
            result.append(f"  · simpa [gridSign, gridIndex] using slack_{i}_{j} z hm")
        save(f"Slacks{i}", result)

    # Interval bounds use exact rational Horner arithmetic at the same root.
    result = header()
    result.extend([
        "lemma root_nonneg (z : ℝ) (hl : (rootLower : ℝ) ≤ z) : 0 ≤ z :=",
        "  le_trans (by exact_mod_cast (show (0 : ℚ) ≤ rootLower by decide +kernel)) hl", "",
        f"theorem rational_node_bounds : ∀ j : Fin {ngrid},",
        "    (-1 : ℚ) < Certificate.lower (nodeRows.getD j []) rootLower rootUpper ∧",
        "    Certificate.upper (nodeRows.getD j []) rootLower rootUpper < 1 := by decide +kernel", "",
        f"theorem rational_node_order : ∀ j : Fin {ngrid-1},",
        "    Certificate.upper (nodeRows.getD j []) rootLower rootUpper <",
        "    Certificate.lower (nodeRows.getD (j.val + 1) []) rootLower rootUpper := by decide +kernel", "",
        "theorem node_bounds (z : ℝ) (hl : (rootLower : ℝ) ≤ z)",
        f"    (hu : z ≤ (rootUpper : ℝ)) (j : Fin {ngrid}) : -1 < node z j ∧ node z j < 1 := by",
        "  have h := Certificate.eval_bounds (nodeRows.getD j []) z rootLower rootUpper hl hu (root_nonneg z hl)",
        "  have hr := rational_node_bounds j",
        "  exact ⟨lt_of_lt_of_le (by exact_mod_cast hr.1) h.1,",
        "    lt_of_le_of_lt h.2 (by exact_mod_cast hr.2)⟩", "",
        "theorem nodes_strictMono (z : ℝ) (hl : (rootLower : ℝ) ≤ z)",
        f"    (hu : z ≤ (rootUpper : ℝ)) : StrictMono (fun j : Fin {ngrid} ↦ node z j) := by",
        "  apply Fin.strictMono_iff_lt_succ.mpr",
        "  intro j",
        "  have hleft := (Certificate.eval_bounds (nodeRows.getD j []) z rootLower rootUpper hl hu (root_nonneg z hl)).2",
        "  have hright := (Certificate.eval_bounds (nodeRows.getD (j.val + 1) []) z rootLower rootUpper hl hu (root_nonneg z hl)).1",
        "  have hr := rational_node_order j",
        "  exact lt_of_le_of_lt hleft (lt_of_lt_of_le (by exact_mod_cast hr) hright)", "",
    ])
    for i, row in enumerate(slacks):
        result.extend([
            f"theorem rational_slacks_{i} : ∀ j : Fin {len(row)}, 0 ≤",
            f"    Certificate.lower ((slackRows.getD {i} []).getD j []) rootLower rootUpper := by decide +kernel", "",
            f"theorem slacks_nonneg_{i} (z : ℝ) (hl : (rootLower : ℝ) ≤ z)",
            f"    (hu : z ≤ (rootUpper : ℝ)) (j : Fin {len(row)}) :",
            f"    0 ≤ Certificate.eval ((slackRows.getD {i} []).getD j []) z :=",
            "  Certificate.eval_nonneg _ z rootLower rootUpper hl hu (root_nonneg z hl)",
            f"    (rational_slacks_{i} j)", "",
        ])
    save("Bounds", result)

    # An invariant cubic grid plus one elementary field element identifies
    # every signed pullback contact without expanding high-degree compositions.
    result = header()
    for j, k in enumerate(mapping):
        q = quotient(add(add(scale(raw_mul(raw_mul(nodes[j], nodes[j]), nodes[j]), 4),
                             scale(nodes[j], -3)), scale(nodes[k], -1)))
        result.extend([
            f"def cubicQuotient{j} : List ℚ :=", "  " + lean_list(q, 1), "",
            f"theorem cubic_at_{j} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :",
            f"    cubic (node z {j}) = node z {k} :=",
            f"  Checker.cubic_map (nodeRows.getD {j} []) (nodeRows.getD {k} []) cubicQuotient{j}",
            "    modulusCoeffs z hm (by decide +kernel)", "",
        ])
    result.extend([
        "theorem cubic_at_node (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
        f"    (j : Fin {ngrid}) : cubic (node z j) = node z (cubicMap.getD j 0) := by",
        "  fin_cases j",
    ])
    result.extend(f"  · exact cubic_at_{j} z hm" for j in range(ngrid))
    save("CubicGrid", result)

    a = nodes[13] if kind == "odd" else add(scale(mul(nodes[mapping[1]], nodes[mapping[1]]), 2), [Q(-1)])
    a_square_quotient = quotient(add(raw_mul(a, a), [Q(-1, 2)]))
    result = header()
    result[4:4] = [f"public import Lorentz.Plateau.Certificates.{namespace}Bounds",
                   f"public import Lorentz.Plateau.Certificates.{namespace}CubicGrid",
                   "public import Lorentz.Plateau.Families"]
    result.extend([
        "open Certificate.PolynomialCertificate", "",
        "def aCoeffs : List ℚ := " + lean_list(a), "",
        "def aSquareQuotient : List ℚ := " + lean_list(a_square_quotient), "",
        "theorem algebraic_a (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
        "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :",
        "    Certificate.eval aCoeffs z = PolynomialBounds.a := by",
        "  have hs := FiniteTools.eq_of_modulus_certificate (power aCoeffs 2) [1 / 2]",
        "    aSquareQuotient modulusCoeffs z hm (by decide +kernel)",
        "  have hp := Certificate.eval_pos aCoeffs z rootLower rootUpper hl hu (root_nonneg z hl)",
        "    (by decide +kernel)",
        "  have ha := PolynomialBounds.a_pos",
        "  have ha2 := PolynomialBounds.a_sq",
        "  norm_num only [eval_power, Certificate.eval, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, mul_zero, add_zero] at hs",
        "  nlinarith", "",
    ])
    for i, row in enumerate(slacks):
        high = not (i == 0 if kind == "odd" else i < 3)
        even = kind == "even"
        bs = lambda b: "true" if b else "false"
        for j in range(len(row)):
            k = 3*j+1 if not high else j
            t = mapping[mapping[k]] if high else mapping[k]
            s = Q(1 if j % 4 in (0, 3) else -1)
            if (i == 0 if kind == "odd" else i == 3):
                s = -s
            expression = add(scale(raw_mul(nodes[t], nodes[t]), 2), [Q(-1)]) if even else nodes[t]
            ecode = f"(sub (scale 2 (power (nodeRows.getD {t} []) 2)) [1])" if even else f"(nodeRows.getD {t} [])"
            if high:
                expression = scale(expression, -1)
                ecode = f"(scale (-1) {ecode})"
            quot = quotient(add(expression, scale(a, -s)))
            result.extend([
                f"def contactQuotient{i}_{j} : List ℚ := " + lean_list(quot), "",
                f"theorem contact_{i}_{j} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
                "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :",
                f"    (pullback {bs(even)} {bs(high)}).eval (node z {k}) = ({rational(s)} : ℝ) * PolynomialBounds.a := by",
                f"  have h := FiniteTools.eq_of_modulus_certificate {ecode} (scale ({rational(s)}) aCoeffs)",
                f"    contactQuotient{i}_{j} modulusCoeffs z hm (by decide +kernel)",
                "  have hone : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]",
                "  simp only [eval_scale, eval_sub, eval_power, hone, algebraic_a z hm hl hu,",
                "    Rat.cast_neg, Rat.cast_one, Rat.cast_ofNat] at h",
                "  simp only [pullback_eval, Bool.false_eq_true, ↓reduceIte, seedMap_eval_false, seedMap_eval_true]",
                f"  rw [cubic_at_{k} z hm]" + (f"\n  rw [cubic_at_{mapping[k]} z hm]" if high else ""),
                "  simpa only [node, neg_one_mul, one_mul] using h", "",
            ])
        result.extend([
            f"theorem contacts_{i} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
            "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))",
            f"    (j : Fin {len(row)}) : (pullback {bs(even)} {bs(high)}).eval (node z (gridIndex {i} j)) =",
            f"      (gridSign {i} j : ℝ) * PolynomialBounds.a := by", "  fin_cases j",
        ])
        result.extend(f"  · simpa [gridIndex, gridSign] using contact_{i}_{j} z hm hl hu" for j in range(len(row)))
        result.append("")
    save("Contacts", result)

    result = header()
    result[4:4] = [f"public import Lorentz.Plateau.Certificates.{namespace}Bounds",
                   f"public import Lorentz.Plateau.Certificates.{namespace}CubicGrid",
                   f"public import Lorentz.Plateau.Certificates.{namespace}Recurrences"]
    result.extend([
        f"def nextNode (j : Fin {ngrid}) : Fin {ngrid} :=",
        f"  ⟨cubicMap.getD j 0, (show ∀ k : Fin {ngrid}, cubicMap.getD k 0 < {ngrid} by decide +kernel) j⟩", "",
        "theorem series_at_node (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
        "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ))",
        f"    (j : Fin {ngrid}) : orbitSeries (forcing z).eval (-3 / 5) (node z j) = value z j := by",
        "  exact FiniteTools.finite_orbit_values (forcing z) (by norm_num)",
        f"    (fun k : Fin {ngrid} ↦ node z k) (fun k ↦ value z k) nextNode",
        "    (fun k ↦ Set.Ioo_subset_Icc_self (node_bounds z hl hu k))",
        "    (cubic_at_node z hm) (all_recurrences z hm) j", "",
    ])
    save("Values", result)

    for i, row in enumerate(slacks):
        n = degrees[i]
        count = len(row)
        even = kind == "even"
        high = not (i == 0 if kind == "odd" else i < 3)
        bs = lambda b: "true" if b else "false"
        initial = 1 if active[i][0] % 4 in (0, 3) else -1
        if (i == 0 if kind == "odd" else i == 3):
            initial = -initial
        result = header()
        result[4:4] = [f"public import Lorentz.Plateau.Certificates.{namespace}Contacts",
                       f"public import Lorentz.Plateau.Certificates.{namespace}Values",
                       f"public import Lorentz.Plateau.Certificates.{namespace}Slacks{i}",
                       "public import Lorentz.Plateau.SeedCertificate"]
        result.extend([
            f"def contactIndex{i} (j : Fin {count}) : Fin {ngrid} :=",
            f"  ⟨gridIndex {i} j, (show ∀ k : Fin {count}, gridIndex {i} k < {ngrid} by decide +kernel) j⟩", "",
            f"def chosen{i} (j : Fin {n+2}) : Fin {count} :=",
            f"  ⟨(activeRows.getD {i} []).getD j 0,",
            f"    (show ∀ k : Fin {n+2}, (activeRows.getD {i} []).getD k 0 < {count} by decide +kernel) j⟩", "",
            f"theorem seed_{i} (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
            "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :",
            "    ∃ ε₀ > 0, ∀ ε, 0 ≤ ε → ε ≤ ε₀ →",
            f"      HasPlateauCertificate (familyFunction {bs(even)} (forcing z) ε) {n} := by",
            f"  have hsg (j : Fin {count}) : (gridSign {i} j : ℝ) = 1 ∨ (gridSign {i} j : ℝ) = -1 := by",
            f"    exact_mod_cast (show ∀ k : Fin {count}, gridSign {i} k = 1 ∨ gridSign {i} k = -1 by decide +kernel) j",
            f"  have hs (j : Fin {count}) := all_slacks_{i} z hm j",
            f"  have hv (j : Fin {count}) : orbitSeries (forcing z).eval (-3 / 5)",
            f"      (node z (gridIndex {i} j)) = value z (gridIndex {i} j) :=",
            f"    series_at_node z hm hl hu (contactIndex{i} j)",
            f"  apply finite_seed_certificate {bs(even)} {bs(high)} (forcing z) (correction {i} z) (slope z {i})",
            f"    (fun j : Fin {count} ↦ node z (gridIndex {i} j)) (fun j ↦ (gridSign {i} j : ℝ))",
            f"    ((nodes_strictMono z hl hu).comp (show StrictMono contactIndex{i} by decide +kernel))",
            f"    (fun j ↦ node_bounds z hl hu (contactIndex{i} j)) hsg (contacts_{i} z hm hl hu)",
            f"    ?_ ?_ ?_ chosen{i} (by decide +kernel) ({initial}) (by norm_num) ?_ ?_ ?_ ?_",
            "  · intro hp",
            "    have he := congrArg (fun p : Polynomial ℝ ↦ p.eval 1) hp",
            "    norm_num [contactPolynomial_eval, pullback_eval, seedMap_eval_false, seedMap_eval_true, cubic] at he",
            "  · unfold contactPolynomial pullback seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly",
            "    simp only [Bool.false_eq_true, ↓reduceIte, Polynomial.sub_comp, Polynomial.mul_comp,",
            "      Polynomial.pow_comp, Polynomial.natCast_comp, Polynomial.X_comp]",
            "    compute_degree <;> norm_num",
            "  · intro j",
            f"    have hh := slacks_nonneg_{i} z hl hu j",
            "    have hid := hs j",
            f"    change orbitSeries (forcing z).eval (-3 / 5) (node z (gridIndex {i} j)) = _ at hv",
            "    rw [hv j]",
            "    linarith",
            "  · intro j",
            f"    exact_mod_cast (show ∀ k : Fin {n+2}, gridSign {i} (chosen{i} k) =",
            f"      ({initial} : ℚ) * (-1 : ℚ) ^ (k : ℕ) by decide +kernel) j",
            "  · intro j",
            f"    have hid := hs (chosen{i} j)",
            f"    have hz : ((slackRows.getD {i} []).getD (chosen{i} j) []) = [] :=",
            f"      (show ∀ k : Fin {n+2}, ((slackRows.getD {i} []).getD (chosen{i} k) []) = [] by decide +kernel) j",
            "    rw [hz] at hid",
            f"    rw [hv (chosen{i} j)]",
            "    change _ = 0 at hid",
            "    linarith",
            f"  · exact lt_of_le_of_lt (FiniteTools.fieldPolynomial_degree (correctionRows.getD {i} []) z) (by decide +kernel)",
            "  · unfold basePolynomial seedMap Certificate.sixthPoly Certificate.cubicPoly Lorentz.cubicPoly",
            "    norm_num only [Bool.false_eq_true, ↓reduceIte]",
            "    compute_degree <;> norm_num", "",
        ])
        # The local value equality is a function; retain its argument when rewriting.
        result = [line for line in result if "at hv" not in line]
        save(f"Seed{i}", result)

    result = header()
    result[4:4] = [f"public import Lorentz.Plateau.Certificates.{namespace}Bounds"]
    factor = Q(1 if kind == "odd" else -1)
    raw_asymmetry = add(raw_evaluate(forcing, [Q(1)]), scale(raw_evaluate(forcing, [Q(-1)]), factor))
    asymmetry = reduce(raw_asymmetry)
    result.extend([
        "open Certificate.PolynomialCertificate", "",
        "def asymmetryCoeffs : List ℚ := " + lean_list(asymmetry), "",
        "def asymmetryQuotient : List ℚ := " + lean_list(quotient(add(raw_asymmetry, scale(asymmetry, -1)))), "",
        "theorem forcing_asymmetry (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0) :",
        f"    (forcing z).eval 1 {'+' if kind == 'odd' else '-'} (forcing z).eval (-1) =",
        "      Certificate.eval asymmetryCoeffs z := by",
        "  have h := FiniteTools.eq_of_modulus_certificate",
        f"    (add (FiniteTools.substitute forcingCoeffs [1]) (scale ({rational(factor)}) (FiniteTools.substitute forcingCoeffs [-1])))",
        "    asymmetryCoeffs asymmetryQuotient modulusCoeffs z hm (by decide +kernel)",
        "  have hp : Certificate.eval [1] z = (1 : ℝ) := by simp [Certificate.eval]",
        "  have hn : Certificate.eval [-1] z = (-1 : ℝ) := by simp [Certificate.eval]",
        "  simpa only [eval_add, eval_scale, FiniteTools.eval_substitute, hp, hn, forcing,",
        "    Rat.cast_one, Rat.cast_neg, one_mul, neg_one_mul, sub_eq_add_neg] using h", "",
        "theorem forcing_asymmetry_ne (z : ℝ) (hm : Certificate.eval modulusCoeffs z = 0)",
        "    (hl : (rootLower : ℝ) ≤ z) (hu : z ≤ (rootUpper : ℝ)) :",
        f"    (forcing z).eval 1 {'+' if kind == 'odd' else '-'} (forcing z).eval (-1) ≠ 0 := by",
        "  rw [forcing_asymmetry z hm]",
    ])
    if kind == "odd":
        result.extend([
            "  simpa only [Rat.cast_zero] using (Certificate.eval_lt asymmetryCoeffs z rootLower rootUpper 0 hl hu",
            "    (root_nonneg z hl) (by decide +kernel)).ne", "",
            "theorem forcing_zero (z : ℝ) : (forcing z).eval 0 = 0 := by",
            "  change (Polynomial.C (Certificate.eval [] z) + Polynomial.X * _).eval 0 = 0",
            "  simp [Certificate.eval]", "",
        ])
    else:
        result.extend([
            "  exact (Certificate.eval_pos asymmetryCoeffs z rootLower rootUpper hl hu",
            "    (root_nonneg z hl) (by decide +kernel)).ne'", "",
        ])
    save("Asymmetry", result)


if __name__ == "__main__":
    for kind in ("odd", "even"):
        generate(kind)
