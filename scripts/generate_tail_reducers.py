#!/usr/bin/env python3
"""Generate the Lean tail-reducer catalogue from tail_reducers.cvs."""

import csv
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import re
import sys

SOURCE = Path("tail_reducers.cvs")
FIELDNAMES = [
    "name",
    "edges",
    "reddish",
    "red",
    "bluish",
    "blue",
    "degree_constraint",
]
LABEL = re.compile(r"^(ptr|ntr)-(.+)$")
DEGREE_CONSTRAINT = re.compile(r"^deg\(([a-z])\)=([0-9]+)$")


def letter(index):
    return chr(ord("a") + index)


def lean_name(name):
    """Translate a detailed label such as dc-a to the Lean constructor dcA."""
    first, *rest = name.split("-")
    return first + "".join(part[0].upper() + part[1:] for part in rest)


def indices(text):
    text = text.strip()
    return [] if text in {"", "-"} else [ord(c) - ord("a") for c in text]


def parse_name(text):
    match = LABEL.fullmatch(text.strip())
    assert match is not None, ("invalid name", text)
    kind, detailed_name = match.groups()
    return kind, detailed_name


def parse_degree_constraint(text):
    text = text.strip()
    if not text:
        return None
    match = DEGREE_CONSTRAINT.fullmatch(text)
    assert match is not None, ("invalid degree constraint", text)
    vertex, degree = match.groups()
    return ord(vertex) - ord("a"), int(degree)


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
    with SOURCE.open(newline="") as source:
        reader = csv.DictReader(source)
        assert reader.fieldnames == FIELDNAMES, (
            "unexpected CSV header",
            reader.fieldnames,
            FIELDNAMES,
        )
        records = list(reader)
    for line_number, record in enumerate(records, 2):
        kind, detailed_name = parse_name(record["name"])
        sign = "+" if kind == "ptr" else "-"
        code = record["edges"].strip()
        assert len(code) % 2 == 0, (line_number, "odd edge encoding")
        edges = [
            (ord(code[i]) - ord("a"), ord(code[i + 1]) - ord("a"))
            for i in range(0, len(code), 2)
        ]
        assert all(0 <= u < 26 and 0 <= v < 26 and u != v for u, v in edges)
        unordered = [tuple(sorted(edge)) for edge in edges]
        assert len(unordered) == len(set(unordered)), (
            line_number, "duplicate edge")
        color_groups = {
            "reddish": indices(record["reddish"]),
            "red": indices(record["red"]),
            "bluish": indices(record["bluish"]),
            "blue": indices(record["blue"]),
        }
        colored_vertices = [v for group in color_groups.values() for v in group]
        assert len(colored_vertices) == len(set(colored_vertices)), (
            line_number, "vertex assigned two colors")
        vertex_count = 1 + max(colored_vertices)
        assert set(colored_vertices) == set(range(vertex_count)), (
            line_number, "colors do not partition the vertices")
        side = sorted(color_groups["reddish"] + color_groups["red"])
        side_count = len(side)
        assert side == list(range(side_count)), (line_number, "red side is not initial")
        assert all(max(edge) < vertex_count for edge in edges), (
            line_number, "edge endpoint lacks a color")
        degrees = [0] * vertex_count
        for u, v in edges:
            degrees[u] += 1
            degrees[v] += 1
        assert max(degrees) <= 3, (detailed_name, "not subcubic", degrees)
        side_set = set(side)
        side_degrees = [0] * vertex_count
        for u, v in edges:
            if (u in side_set) == (v in side_set):
                side_degrees[u] += 1
                side_degrees[v] += 1
        assert max(side_degrees) <= 1, (
            detailed_name, "not a matching cut", side_degrees)
        ambient_degree = []
        degree_constraint = parse_degree_constraint(record["degree_constraint"])
        if degree_constraint is not None:
            vertex, degree = degree_constraint
            assert degrees[vertex] <= degree <= 3, (
                detailed_name, "invalid ambient-degree guard")
            ambient_degree = [(vertex, degree)]
        row = {
            "name": lean_name(detailed_name),
            "label": f"{kind}-{detailed_name}",
            "side_count": side_count,
            "vertex_count": vertex_count,
            "edges": edges,
            "reddish": color_groups["reddish"],
            "ambient_degree": ambient_degree,
        }
        declared_colors = [
            next(color for color, vertices in color_groups.items() if v in vertices)
            for v in range(vertex_count)
        ]
        assert row_colors(row) == declared_colors, (
            line_number, "declared colors disagree with graph/cut", detailed_name)
        rows[sign].append(row)
    assert len(rows["+"]) == 27
    assert len(rows["-"]) == 56
    return rows


def exact_rows():
    rows = parse_rows()
    positive = rows["+"]
    negative = rows["-"]
    assert len(positive) == 27
    assert len(negative) == 56
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
        if row["ambient_degree"]:
            vertex, degree = row["ambient_degree"][0]
            print(f"      ambientDegree := [({vertex}, {degree})]")
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
        ("negativeDcA_color_a", "dcA", 0, "reddish"),
        ("negativeA_color_a", "a", 0, "red"),
        ("negativeDcG_color_a", "dcG", 0, "reddish"),
        ("negativeDcG_color_b", "dcG", 1, "reddish"),
        ("negativeX_color_a", "x", 0, "red"),
        ("negativeX_color_b", "x", 1, "reddish"),
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
