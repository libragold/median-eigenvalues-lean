import Subcubic.Lemma4_2

/-!
# Lemma 4.3

The conclusion records both outcomes in the proof: a positive tail reducer or
a cut enhancer.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- If one endpoint of a red edge has two distinct blue neighbors, those
neighbors either induce cut enhancer `a`, or their blue edge lets Lemma 4.2
produce the desired positive tail reducer. -/
private theorem redEdge_twoBlueNeighbors
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hcd_vertices : c ≠ d) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  by_cases hcd : G.Adj c d
  · apply redEdge_blueEdge_multipleEdges C a b c d hab ha hb hcd hc hd
    classical
    simp [fourVertexCrossEdgeCount, hac, had]
    omega
  · exact Or.inr (containsCutEnhancerA_of C ha hc hd hac had hcd_vertices hcd)

/-- **Lemma 4.3.** If a red edge sends at least three edges
into a set consisting entirely of blue vertices, then the graph contains a
positive tail reducer or a cut enhancer. -/
theorem lemma4_3
    (C : GoodColoring G) {a b : V} (B : Set V)
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (hB : ∀ v ∈ B, C.color v = .blue)
    (hthree : 3 ≤ edgeCountFromPairToSet G a b B) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  have hsplit :
      2 ≤ (G.neighborSet a ∩ B).ncard ∨
      2 ≤ (G.neighborSet b ∩ B).ncard := by
    unfold edgeCountFromPairToSet at hthree
    omega
  rcases hsplit with ha_two | hb_two
  · have ha_one : 1 < (G.neighborSet a ∩ B).ncard := by omega
    rcases (Set.one_lt_ncard (s := G.neighborSet a ∩ B)).mp ha_one with
      ⟨c, hc, d, hd, hcd_vertices⟩
    exact redEdge_twoBlueNeighbors C ha hb (hB c hc.2) (hB d hd.2)
      hab hc.1 hd.1 hcd_vertices
  · have hb_one : 1 < (G.neighborSet b ∩ B).ncard := by omega
    rcases (Set.one_lt_ncard (s := G.neighborSet b ∩ B)).mp hb_one with
      ⟨c, hc, d, hd, hcd_vertices⟩
    exact redEdge_twoBlueNeighbors C hb ha (hB c hc.2) (hB d hd.2)
      hab.symm hc.1 hd.1 hcd_vertices

end Subcubic
