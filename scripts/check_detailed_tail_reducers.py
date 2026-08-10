#!/usr/bin/env python3
"""Check detailed-input.txt against the generated Lean tail-reducer catalog.

Names are intentionally ignored.  Reducers are compared by sign, graph,
complete vertex coloring, and ambient-degree requirements.  This is the
precondition for safely adopting the names from detailed-input.txt.
"""

from collections import defaultdict
from pathlib import Path
import re

from generate_tail_reducers import exact_rows, row_colors


LINE = re.compile(
    r"^(ptr|ntr)-([^ ]+) ([a-z]+)"
    r"(?: deg\(([a-z])\)=([0-9]+))?"
    r" reddish ([a-z]+|-); red ([a-z]+|-);"
    r" bluish ([a-z]+|-); blue ([a-z]+|-)$"
)


def indices(text):
    return [] if text == "-" else [ord(c) - ord("a") for c in text]


def parse_detailed():
    result = []
    for line_number, text in enumerate(
        Path("detailed-input.txt").read_text().splitlines(), 1
    ):
        match = LINE.fullmatch(text)
        assert match is not None, (line_number, "cannot parse", text)
        kind, name, edge_code, degree_vertex, degree, reddish, red, bluish, blue = (
            match.groups()
        )
        assert len(edge_code) % 2 == 0, (line_number, "odd edge encoding")
        edges = [
            (ord(edge_code[i]) - ord("a"), ord(edge_code[i + 1]) - ord("a"))
            for i in range(0, len(edge_code), 2)
        ]
        unordered = [tuple(sorted(edge)) for edge in edges]
        assert len(unordered) == len(set(unordered)), (line_number, "duplicate edge")

        color_groups = {
            "reddish": indices(reddish),
            "red": indices(red),
            "bluish": indices(bluish),
            "blue": indices(blue),
        }
        colored_vertices = [v for group in color_groups.values() for v in group]
        assert len(colored_vertices) == len(set(colored_vertices)), (
            line_number,
            "vertex assigned two colors",
        )
        vertex_count = 1 + max(colored_vertices)
        assert set(colored_vertices) == set(range(vertex_count)), (
            line_number,
            "colors do not partition the vertices",
        )
        side = sorted(color_groups["reddish"] + color_groups["red"])
        side_count = len(side)
        assert side == list(range(side_count)), (line_number, "red side is not initial")
        assert all(max(edge) < vertex_count for edge in edges), (
            line_number,
            "edge endpoint lacks a color",
        )

        guard = []
        if degree_vertex is not None:
            guard = [(ord(degree_vertex) - ord("a"), int(degree))]
        row = {
            "sign": "+" if kind == "ptr" else "-",
            "name": name,
            "label": f"{kind}-{name}",
            "vertex_count": vertex_count,
            "side_count": side_count,
            "edges": edges,
            "reddish": color_groups["reddish"],
            "ambient_degree": guard,
        }
        assert row_colors(row) == [
            next(color for color, vertices in color_groups.items() if v in vertices)
            for v in range(vertex_count)
        ], (line_number, "declared colors disagree with graph/cut", name)
        result.append(row)
    return result


def signature(row):
    guard = row.get("ambient_degree")
    if guard is None:
        from generate_tail_reducers import AMBIENT_DEGREE_GUARDS

        entry = AMBIENT_DEGREE_GUARDS.get((row["sign"], row["name"]))
        guard = [] if entry is None else [entry]
    return (
        row["sign"],
        row["vertex_count"],
        row["side_count"],
        tuple(sorted(tuple(sorted(edge)) for edge in row["edges"])),
        tuple(row_colors(row)),
        tuple(guard),
    )


def grouped(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[signature(row)].append(row["name"])
    return groups


def main():
    positive, negative = exact_rows()
    current = [
        {**row, "sign": sign}
        for sign, rows in [("+", positive), ("-", negative)]
        for row in rows
    ]
    detailed = parse_detailed()
    current_groups = grouped(current)
    detailed_groups = grouped(detailed)

    assert all(len(names) == 1 for names in detailed_groups.values()), (
        "detailed-input contains duplicate mathematical reducers",
        [names for names in detailed_groups.values() if len(names) != 1],
    )
    assert set(current_groups) == set(detailed_groups), {
        "current_unique": len(current_groups),
        "detailed_unique": len(detailed_groups),
        "current_duplicates": [
            names for names in current_groups.values() if len(names) > 1
        ],
        "only_current": [current_groups[s] for s in set(current_groups) - set(detailed_groups)],
        "only_detailed": [detailed_groups[s] for s in set(detailed_groups) - set(current_groups)],
    }

    print(f"verified {len(detailed_groups)} detailed reducers")
    print(f"  positive: {sum(s[0] == '+' for s in detailed_groups)}")
    print(f"  negative: {sum(s[0] == '-' for s in detailed_groups)}")
    print("bijection with the generated mathematical patterns established")


if __name__ == "__main__":
    main()
