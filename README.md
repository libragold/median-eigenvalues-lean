# Subcubic graph lemmas in Lean

This repository contains a Lean formalization of local reductions in subcubic
graphs with matching cuts.

## Basic Definitions

A graph `G` is **subcubic** if every vertex has degree at most `3`.

A **matching cut** of `G` is a cut `(A, B)` of the vertices such that
each side induces a graph of maximum degree at most `1`.  Equivalently, the
edges of `G[A] ∪ G[B]` form a matching. In Lean this is represented by
`MatchingCut G`, which stores one side `A`; the other side is its complement.

The four colors used throughout the formalization are derived from a matching
cut:

- `red`: a vertex in `A` with a neighbor in `G[A]`;
- `reddish`: a vertex in `A` with no neighbor in `G[A]`;
- `blue`: a vertex in `B` with a neighbor in `G[B]`;
- `bluish`: a vertex in `B` with no neighbor in `G[B]`.

The Lean type `MatchingCutColoring G` is the color-based presentation of this
data.  It stores the four-coloring directly, together with proofs that `G` is
subcubic, that the two color-sides form a matching cut, and that every color
has exactly the graph-theoretic meaning above.  A `MatchingCut G` can be
converted to its recomputed four-coloring by `MatchingCut.toColoring`, and a
`MatchingCutColoring G` can recover its cut by
`MatchingCutColoring.toMatchingCut`.

A **cut-preserver flip** is performed at a red-blue edge `ab`: both endpoints
are toggled across the cut, so the new cut is
`(A ∆ {a, b}, B ∆ {a, b})`.  In Lean a flip is valid only when the resulting
cut is again a matching cut; reachability means zero or more such valid flips,
with colors recomputed after each flip.

## Main Formalized Results

The top-level results are `lemma2_7` and `lemma2_8`.  They are stated in Lean
for a `MatchingCutColoring` and a specified red edge.  Equivalently, in cut
language:

Let `(A, B)` be a matching cut of a finite subcubic graph `G`.  If `G[A]`
contains an edge, then there are matching cuts
`(A_0, B_0), (A_1, B_1), ..., (A_k, B_k)` and edges
`a_0 b_0, a_1 b_1, ..., a_{k-1} b_{k-1}` of `G`, with
`(A_0, B_0) = (A, B)`, such that for each `i < k`, the vertex `a_i` is red and
`b_i` is blue with respect to `(A_i, B_i)`, and
`A_{i+1} = A_i ∆ {a_i, b_i}` and `B_{i+1} = B_i ∆ {a_i, b_i}`.

With colors recomputed from either `(A_k, B_k)` or `(B_k, A_k)`, the graph `G`
then contains an induced catalogued obstruction satisfying its listed
ambient-degree constraints when present:

- `lemma2_7`: a cut enhancer, degree cut enhancer, absolute tail reducer,
  positive tail reducer, or degree-constrained positive tail reducer;
- `lemma2_8`: a cut enhancer, degree cut enhancer, absolute tail reducer,
  negative tail reducer, or degree-constrained negative tail reducer.

## Repository Layout

- `Subcubic/Basic.lean`: subcubic graphs, colors, `MatchingCutColoring`, color
  reversal, and color-side facts.
- `Subcubic/MatchingCut.lean`: matching cuts, color recomputation from a cut,
  cut-preserver flips, and flip reachability.
- `Subcubic/Pattern.lean`: finite colored patterns, induced occurrence, side
  swapping, and reusable induced-occurrence constructors.
- `Subcubic/TailReducers.lean`: the generated catalog of `27` positive and
  `56` negative tail reducers.
- `Subcubic/CutEnhancers.lean`: the catalog of cut enhancers, including the
  low-degree enhancers used by Lemma 3.6.
- `Subcubic/PositiveTailReducerWitnesses.lean` and
  `Subcubic/NegativeTailReducerWitnesses.lean`: reusable embeddings of named
  tail reducers into ambient configurations.
- `Subcubic/PositiveReduction.lean` and `Subcubic/NegativeReduction.lean`:
  reachability predicates for the positive and negative conclusions.
- `Subcubic/Lemma2_7.lean` and `Subcubic/Lemma2_8.lean`: the main positive and
  negative reducer theorems.
- `Subcubic/Lemma3_*.lean`, `Subcubic/Lemma4_*.lean`, and
  `Subcubic/Lemma5_*.lean`: supporting local lemmas and case analyses used by
  the two main theorems.
- `Subcubic.lean`: aggregate import of the formalization.

The numbered lemma and case labels are internal navigation labels for the
formal proof files.

## Reducer Data and Scripts

The source data for tail reducers is `tail_reducers.cvs`.  Its columns are
`name`, `edges`, `reddish`, `red`, `bluish`, `blue`, and
`degree_constraint`.  The `edges` column uses a compact two-letter edge
encoding, and `degree_constraint` records optional ambient degree requirements.

Run:

```bash
python3 scripts/validate_tail_reducers.py
```

to check that the source file contains `27` positive and `56` negative
reducers and has no duplicate mathematical reducer entries.

Run:

```bash
python3 scripts/generate_tail_reducers.py --write
```

to regenerate `Subcubic/TailReducers.lean` from `tail_reducers.cvs`.

## Checking the Formalization

This project uses Lean through Lake.  To check the full formalization, run:

```bash
lake build
```
