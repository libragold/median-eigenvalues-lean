#!/usr/bin/env python3
"""Print the systematic Lean definitions for all supplied tail reducers.

The compact source table is expanded into readable blocks. Each numeric edge
is accompanied by its original letter name, and the script validates the
transformation before printing Lean code.
"""

from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import sys


POSITIVE_REDDISH = {
    "l": [0], "m": [0], "o": [0], "p": [0], "q": [0],
    "r": [0], "s": [0], "t": [0], "u": [0], "x": [3], "mMinus": [0],
}
NEGATIVE_REDDISH = {
    "e": [1], "h": [1], "i": [1], "j": [1], "k": [2],
    "n": [2], "o": [0], "p": [0], "q": [0], "r": [2],
    "s": [2], "t": [2], "u": [0, 1], "v": [0, 1],
    "w": [1], "x": [2], "y": [1], "z": [0],
    "e0Minus": [1], "s0Minus": [2], "s0Minus2": [2],
}

SPECIAL_LABELS = {
    ("+", "mMinus"): "m-minus+",
    ("-", "e0Minus"): "e0-minus-",
    ("-", "e1Minus"): "e1-minus-",
    ("-", "s0Minus"): "s0-minus-",
    ("-", "s1Minus"): "s1-minus-",
    ("-", "s0Minus2"): "s0-minus2-",
    ("-", "s1Minus2"): "s1-minus2-",
}


def letter(index):
    return chr(ord("a") + index)


def row_colors(row):
    """Compute the exact graph color assigned to every encoded vertex."""
    n = row["vertex_count"]
    k = row["side_count"]
    reddish = set(row["reddish"])
    has_same_side_neighbor = [False] * n
    for u, v in row["edges"]:
        if (u < k) == (v < k):
            has_same_side_neighbor[u] = True
            has_same_side_neighbor[v] = True
    return [
        ("reddish" if i in reddish else "red") if i < k else
        ("blue" if has_same_side_neighbor[i] else "bluish")
        for i in range(n)
    ]


def all_nonedges_automatic(row):
    """Whether degree saturation/matching sides force every missing edge."""
    n = row["vertex_count"]
    k = row["side_count"]
    edges = {tuple(sorted(edge)) for edge in row["edges"]}
    colors = row_colors(row)
    degrees = [0] * n
    same_side_neighbor = [False] * n
    for u, v in edges:
        degrees[u] += 1
        degrees[v] += 1
        if (u < k) == (v < k):
            same_side_neighbor[u] = True
            same_side_neighbor[v] = True
    for x in range(n):
        for y in range(n):
            if x == y or tuple(sorted((x, y))) in edges:
                continue
            saturated_x = colors[x] in {"red", "blue"} and degrees[x] == 3
            saturated_y = colors[y] in {"red", "blue"} and degrees[y] == 3
            same_side = (x < k) == (y < k)
            matching_forces = same_side and (
                colors[x] in {"reddish", "bluish"} or
                same_side_neighbor[x]
            )
            if not (saturated_x or saturated_y or matching_forces):
                return False
    return True


def boundary_nonedges(row):
    """Missing unordered pairs not forced by saturation/matching alone."""
    n = row["vertex_count"]
    k = row["side_count"]
    edges = {tuple(sorted(edge)) for edge in row["edges"]}
    colors = row_colors(row)
    degrees = [0] * n
    same_side_neighbor = [False] * n
    for u, v in edges:
        degrees[u] += 1
        degrees[v] += 1
        if (u < k) == (v < k):
            same_side_neighbor[u] = True
            same_side_neighbor[v] = True
    result = []
    def automatic(x, y):
        saturated_x = colors[x] in {"red", "blue"} and degrees[x] == 3
        saturated_y = colors[y] in {"red", "blue"} and degrees[y] == 3
        same_side = (x < k) == (y < k)
        matching_forces = same_side and (
            colors[x] in {"reddish", "bluish"} or
            same_side_neighbor[x]
        )
        return saturated_x or saturated_y or matching_forces
    for x in range(n):
        for y in range(x + 1, n):
            if (x, y) in edges:
                continue
            if not automatic(x, y) or not automatic(y, x):
                result.append((x, y))
    return result


def parse_rows():
    rows = {"+": [], "-": []}
    source = Path("data/tail_reducers.txt")
    for line_number, line in enumerate(source.read_text().splitlines(), 1):
        head, code = line.split()
        sign = "+" if "+" in head else "-"
        name, side_count = head.split(sign)
        assert len(code) % 2 == 0, (line_number, "odd edge encoding")
        edges = [
            (ord(code[i]) - ord("a"), ord(code[i + 1]) - ord("a"))
            for i in range(0, len(code), 2)
        ]
        assert all(0 <= u < 26 and 0 <= v < 26 and u != v for u, v in edges)
        unordered = [tuple(sorted(edge)) for edge in edges]
        assert len(unordered) == len(set(unordered)), (head, "duplicate edge")
        vertex_count = 1 + max(max(edge) for edge in edges)
        degrees = [0] * vertex_count
        for u, v in edges:
            degrees[u] += 1
            degrees[v] += 1
        assert max(degrees) <= 3, (head, "not subcubic", degrees)
        assert int(side_count) <= vertex_count
        side = set(range(int(side_count)))
        side_degrees = [0] * vertex_count
        for u, v in edges:
            if (u in side) == (v in side):
                side_degrees[u] += 1
                side_degrees[v] += 1
        assert max(side_degrees) <= 1, (head, "not a matching cut", side_degrees)
        display_label = SPECIAL_LABELS.get((sign, name), f"{name}{sign}")
        rows[sign].append({
            "name": name,
            "label": display_label,
            "side_count": int(side_count),
            "vertex_count": vertex_count,
            "edges": edges,
        })
    assert len(rows["+"]) == 26
    assert len(rows["-"]) == 46
    return rows


def exact_rows():
    rows = parse_rows()
    positive = []
    for row in rows["+"]:
        positive.append({**row, "reddish": POSITIVE_REDDISH.get(row["name"], [])})

    negative = []
    for row in rows["-"]:
        name = row["name"]
        if name == "a":
            # User convention: suffix 0 is the reddish-a version; suffix 1 is red.
            negative.append({**row, "name": "a0", "label": "a0-", "reddish": [0]})
            negative.append({**row, "name": "a1", "label": "a1-", "reddish": []})
        elif name == "w":
            # b is always reddish; suffix 0/1 selects reddish/red for a.
            negative.append({**row, "name": "w0", "label": "w0-", "reddish": [0, 1]})
            negative.append({**row, "name": "w1", "label": "w1-", "reddish": [1]})
        else:
            negative.append({**row, "reddish": NEGATIVE_REDDISH.get(name, [])})

    assert len(positive) == 26
    assert len(negative) == 48
    for row in positive + negative:
        assert all(i < row["side_count"] for i in row["reddish"])
    return positive, negative


def emit_catalog(title, prefix, sign, rows):
    print(f"/-- Names of the {title.lower()} tail reducers in the supplied catalog. -/")
    print(f"inductive {title}TailReducerName")
    for row in rows:
        print(f"  | {row['name']}")
    print("  deriving DecidableEq, Repr\n")

    print(f"/-- Exact graph and color data for every {title.lower()} tail reducer. -/")
    print(f"def {prefix}TailReducerData : {title}TailReducerName → PatternData")
    for row in rows:
        name = row["name"]
        n = row["vertex_count"]
        k = row["side_count"]
        red_letters = ", ".join(letter(i) for i in range(k))
        blue_letters = ", ".join(letter(i) for i in range(k, n))
        print(f"  | .{name} => {{")
        print(f"      label := \"{row['label']}\"")
        print(f"      vertexCount := {n}")
        print(f"      sideCount := {k}")
        print(f"      -- Red side: {red_letters}. Blue side: {blue_letters}.")
        print("      edges := [")
        for index, (u, v) in enumerate(row["edges"]):
            comma = "," if index + 1 < len(row["edges"]) else ""
            print(f"        ({u}, {v}){comma} -- {letter(u)}{letter(v)}")
        print("      ]")
        if row["reddish"]:
            values = ", ".join(map(str, row["reddish"]))
            names = ", ".join(letter(i) for i in row["reddish"])
            print(f"      reddish := [{values}] -- {names}")
        print("    }")
    print()

    print(f"/-- The exact colored induced pattern associated with a {title.lower()} reducer name. -/")
    print(f"def {prefix}TailReducer (name : {title}TailReducerName) : ColoredPattern :=")
    print(f"  ({prefix}TailReducerData name).toPattern\n")

    print(f"instance (name : {title}TailReducerName) :")
    print(f"    DecidableRel ({prefix}TailReducer name).graph.Adj := by")
    print(f"  unfold {prefix}TailReducer PatternData.toPattern")
    print("  infer_instance\n")

    print(f"/-- Every listed {title.lower()} reducer graph is subcubic. -/")
    print(f"theorem {prefix}TailReducer_subcubic (name : {title}TailReducerName) :")
    print(f"    IsSubcubic ({prefix}TailReducer name).graph := by")
    print("  cases name <;>")
    print("    change IsSubcubic (graphOfEdges _) <;>")
    print("    intro v <;>")
    print("    unfold vertexDegree <;>")
    print("    rw [Set.ncard_eq_toFinset_card'] <;>")
    print("    native_decide +revert\n")

    automatic = [row for row in rows if all_nonedges_automatic(row)]
    print(f"/-! Generated induced-occurrence certificates for {title.lower()} reducers")
    print("whose every nonedge follows from saturation or the matching cut. -/\n")
    for row in automatic:
        theorem_name = f"{prefix}{row['name'][0].upper()}{row['name'][1:]}_automaticNonedges"
        print(f"theorem {theorem_name} (x y : Fin ({prefix}TailReducer .{row['name']}).vertexCount)")
        print(f"    (hne : x ≠ y) (hxy : ¬ ({prefix}TailReducer .{row['name']}).graph.Adj x y) :")
        print(f"    ({prefix}TailReducer .{row['name']}).AutomaticallyForcesNonedge x y := by")
        print("  revert x y")
        print("  native_decide\n")

    print(f"/-! Generated lists of the remaining boundary nonedges. -/\n")
    for row in rows:
        pairs = boundary_nonedges(row)
        if not pairs:
            continue
        theorem_name = f"{prefix}{row['name'][0].upper()}{row['name'][1:]}_boundaryNonedges"
        pattern = f"{prefix}TailReducer .{row['name']}"
        pair_text = ", ".join(
            f"(⟨{u}, by native_decide⟩, ⟨{v}, by native_decide⟩)"
            for u, v in pairs
        )
        print(f"theorem {theorem_name} (x y : Fin ({pattern}).vertexCount)")
        print(f"    (hne : x ≠ y) (hxy : ¬ ({pattern}).graph.Adj x y)")
        print(f"    (hauto : ¬ ({pattern}).AutomaticallyForcesNonedge x y) :")
        print(f"    (x, y) ∈ [{pair_text}] ∨ (y, x) ∈ [{pair_text}] := by")
        print("  revert x y")
        print("  native_decide\n")


def main():
    positive, negative = exact_rows()
    print("import Subcubic.Pattern\n")
    print("open Set\n")
    print("namespace Subcubic\n")
    emit_catalog("Positive", "positive", "+", positive)
    emit_catalog("Negative", "negative", "-", negative)

    print("/-- Membership in the complete supplied catalog of positive tail reducers. -/")
    print("def IsPositiveTailReducer (P : ColoredPattern) : Prop :=")
    print("  ∃ name, P = positiveTailReducer name\n")
    print("/-- Membership in the complete supplied catalog of negative tail reducers. -/")
    print("def IsNegativeTailReducer (P : ColoredPattern) : Prop :=")
    print("  ∃ name, P = negativeTailReducer name\n")
    print("theorem IsPositiveTailReducer.subcubic {P : ColoredPattern}")
    print("    (hP : IsPositiveTailReducer P) : IsSubcubic P.graph := by")
    print("  obtain ⟨name, rfl⟩ := hP")
    print("  exact positiveTailReducer_subcubic name\n")
    print("theorem IsNegativeTailReducer.subcubic {P : ColoredPattern}")
    print("    (hP : IsNegativeTailReducer P) : IsSubcubic P.graph := by")
    print("  obtain ⟨name, rfl⟩ := hP")
    print("  exact negativeTailReducer_subcubic name\n")

    for title, prefix in [("Positive", "positive"), ("Negative", "negative")]:
        print(f"/-- An induced {title.lower()} reducer in the catalog's displayed orientation. -/")
        print(f"def ContainsOriented{title}TailReducer {{V : Type*}} [Fintype V]")
        print("    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=")
        print(f"  ∃ P, Is{title}TailReducer P ∧ P.OccursInduced C\n")
        print(f"/-- An induced {title.lower()} reducer, allowing all colors to be exchanged. -/")
        print(f"def Contains{title}TailReducer {{V : Type*}} [Fintype V]")
        print("    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=")
        print(f"  ContainsInducedUpToSwap Is{title}TailReducer C\n")

    print("/-! Named color checks for exceptional entries. -/\n")
    checks = [
        ("negativeA0_color_a", "a0", 0, "reddish"),
        ("negativeA1_color_a", "a1", 0, "red"),
        ("negativeW0_color_a", "w0", 0, "reddish"),
        ("negativeW0_color_b", "w0", 1, "reddish"),
        ("negativeW1_color_a", "w1", 0, "red"),
        ("negativeW1_color_b", "w1", 1, "reddish"),
    ]
    for theorem, name, vertex, color in checks:
        print(f"@[simp] theorem {theorem} :")
        print(f"    (negativeTailReducer .{name}).color ⟨{vertex}, by native_decide⟩ = .{color} := by")
        print("  native_decide\n")
    print("end Subcubic")


if __name__ == "__main__":
    if sys.argv[1:] == ["--write"]:
        output = StringIO()
        with redirect_stdout(output):
            main()
        Path("Subcubic/TailReducers.lean").write_text(output.getvalue())
    else:
        assert not sys.argv[1:], "usage: generate_tail_reducers.py [--write]"
        main()
