# Subcubic graph lemmas in Lean

This project formalizes local arguments about subcubic graphs equipped with a
good four-coloring. The coloring determines the cut: red/reddish vertices form
one side and blue/bluish vertices form the other.

The initial organization is:

- `Subcubic/Basic.lean`: subcubic graphs, good colorings, their derived cut
  sides, color reversal, and cut preservers;
- `Subcubic/ColoringLemmas.lean`: reusable consequences of the matching and
  degree-three assumptions, independent of the pattern catalogs;
- `Subcubic/MatchingCut.lean`: matching cuts as first-class objects, color
  recomputation, valid cut-preserver flips, and the explicitly documented
  Lemma 3.4 axiom for degree-three red/blue vertices;
- `Subcubic/Pattern.lean`: finite colored patterns and induced occurrence (for
  both tail reducers and cut enhancers), including reversal under the symmetry
  `A ↔ B`, red ↔ blue, and reddish ↔ bluish;
- `Subcubic/TailReducers.lean`: 24 positive and 42 exact-color negative
  reducers, generated in a readable format from the compact source table;
- `Subcubic/CutEnhancers.lean`: the seven explicitly colored induced
  cut-enhancer patterns;
- `Subcubic/Lemma3_3.lean`: Lemma 3.3, including the explicit induced copy of
  cut enhancer `a`;
- `Subcubic/Lemma4_2.lean`: the complete proof of Lemma 4.2, including all
  four-, three-, and two-crossing-edge cases.
- `Subcubic/Lemma4_3.lean`: Lemma 4.3, concluding that there is a positive
  tail reducer or a cut enhancer.
- `Subcubic/Lemma4_4.lean`: Lemma 4.4, using the three possible overlap sizes
  of the bluish neighbor pairs to obtain reducers `b+`, `h+`, or `k+`.

The two formerly flexible negative reducers are split as follows: `a0` and
`w0` have reddish `a`, while `a1` and `w1` have red `a`. Run
`python3 scripts/generate_tail_reducers.py` to print a regenerated
`Subcubic/TailReducers.lean` after changing the source data.

Build with `lake build`.
