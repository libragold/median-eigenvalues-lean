#!/usr/bin/env python3
"""Validate tail_reducers.cvs before regenerating the Lean reducer catalog.

This catches duplicate mathematical reducers: entries with the same sign,
graph, complete vertex coloring, and ambient-degree requirements.
"""

from collections import defaultdict

from generate_tail_reducers import parse_rows, row_colors


def signature(row):
    return (
        row["sign"],
        row["vertex_count"],
        row["side_count"],
        tuple(sorted(tuple(sorted(edge)) for edge in row["edges"])),
        tuple(row_colors(row)),
        tuple(row["ambient_degree"]),
    )


def grouped(rows):
    groups = defaultdict(list)
    for row in rows:
        groups[signature(row)].append(row["name"])
    return groups


def main():
    positive, negative = parse_rows().values()
    rows = [
        {**row, "sign": sign}
        for sign, rows in [("+", positive), ("-", negative)]
        for row in rows
    ]
    groups = grouped(rows)

    assert len(positive) == 27
    assert len(negative) == 56
    assert all(len(names) == 1 for names in groups.values()), (
        "tail_reducers.cvs contains duplicate mathematical reducers",
        [names for names in groups.values() if len(names) != 1],
    )

    print(f"validated {len(groups)} detailed reducers")
    print(f"  positive: {len(positive)}")
    print(f"  negative: {len(negative)}")
    print("no duplicate mathematical reducers")


if __name__ == "__main__":
    main()
