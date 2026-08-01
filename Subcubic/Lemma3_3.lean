import Subcubic.CutEnhancers
import Subcubic.ColoringLemmas
import Mathlib.Tactic.FinCases

/-!
# Lemma 3.3

The conclusion is stated as a disjunction.  Thus the lemma does not need a
global hypothesis saying that cut enhancers are absent: if `d` is blue, the
three displayed vertices themselves witness cut enhancer `a`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 3.3.** Let `a` be red.  Suppose `b` and `d` are distinct
blue-side neighbors of `a`, while `b` belongs to the blue edge `bc`, with
`c ≠ d`.  Then `d` is bluish, unless the graph already contains cut enhancer
`a`.

The hypothesis that `d` is blue or bluish is the color-only formulation of
"`d` lies on the blue side". -/
theorem lemma3_3
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red)
    (hb : C.color b = .blue) (hc : C.color c = .blue)
    (hdside : C.color d = .blue ∨ C.color d = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (hbc : G.Adj b c)
    (hbd_vertices : b ≠ d) (hcd_vertices : c ≠ d) :
    C.color d = .bluish ∨ ContainsCutEnhancer C := by
  rcases hdside with hd | hd
  · right
    apply containsCutEnhancerA_of C ha hb hd hab had hbd_vertices
    have hbside : b ∉ C.redSide := by simp [hb]
    have hcside : c ∉ C.redSide := by simp [hc]
    have hdside : d ∉ C.redSide := by simp [hd]
    exact C.blueSide_not_adj_second_neighbor hbside hcside hdside hbc hcd_vertices
  · exact Or.inl hd

/-- Lemma 3.3 with red and blue, and reddish and bluish, exchanged. -/
theorem lemma3_3_reversed
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .blue)
    (hb : C.color b = .red) (hc : C.color c = .red)
    (hdside : C.color d = .red ∨ C.color d = .reddish)
    (hab : G.Adj a b) (had : G.Adj a d) (hbc : G.Adj b c)
    (hbd_vertices : b ≠ d) (hcd_vertices : c ≠ d) :
    C.color d = .reddish ∨ ContainsCutEnhancer C := by
  have ha' : C.swapSides.color a = .red := by simp [ha]
  have hb' : C.swapSides.color b = .blue := by simp [hb]
  have hc' : C.swapSides.color c = .blue := by simp [hc]
  have hdside' : C.swapSides.color d = .blue ∨
      C.swapSides.color d = .bluish := by
    rcases hdside with hd | hd
    · exact Or.inl (by simp [hd])
    · exact Or.inr (by simp [hd])
  rcases lemma3_3 C.swapSides ha' hb' hc' hdside' hab had hbc
      hbd_vertices hcd_vertices with hd | henhancer
  · left
    change (C.color d).swap = .bluish at hd
    exact (Color.swap_eq_bluish _).1 hd
  · right
    exact (containsInducedUpToSwap_swapSides IsCutEnhancer C).1 henhancer

end Subcubic
