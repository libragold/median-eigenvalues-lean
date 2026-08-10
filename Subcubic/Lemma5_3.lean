import Subcubic.Lemma5_2

/-!
# Lemma 5.3

The negative-tail analogue of Lemma 4.3.  The proof is the same pigeonhole
argument, with Lemma 5.2 replacing Lemma 4.2.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- If one endpoint of a red edge has two distinct blue neighbors, those
neighbors either induce cut enhancer `a`, or their blue edge lets Lemma 5.2
produce a negative tail reducer. -/
private theorem redEdge_twoBlueNeighbors_negative
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hcdV : c ≠ d) :
    HasReachableNegativeReduction C := by
  by_cases hcd : G.Adj c d
  · apply lemma5_2 C a b c d hab ha hb hcd hc hd
    classical
    simp [fourVertexCrossEdgeCount, hac, had]
    omega
  · exact .of_current_ce C
      (containsCutEnhancerA_of C ha hc hd hac had hcdV hcd)

/-- **Lemma 5.3.** If a red edge sends at least three edges into a set of
blue vertices, then the current coloring contains an induced negative tail
reducer or an induced cut enhancer.  The paper's distance bound is omitted. -/
theorem lemma5_3
    (C : GoodColoring G) {a b : V} (B : Set V)
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (hB : ∀ v ∈ B, C.color v = .blue)
    (hthree : 3 ≤ edgeCountFromPairToSet G a b B) :
    HasReachableNegativeReduction C := by
  have hsplit :
      2 ≤ (G.neighborSet a ∩ B).ncard ∨
      2 ≤ (G.neighborSet b ∩ B).ncard := by
    unfold edgeCountFromPairToSet at hthree
    omega
  rcases hsplit with haTwo | hbTwo
  · have haOne : 1 < (G.neighborSet a ∩ B).ncard := by omega
    rcases (Set.one_lt_ncard (s := G.neighborSet a ∩ B)).mp haOne with
      ⟨c, hc, d, hd, hcdV⟩
    exact redEdge_twoBlueNeighbors_negative C ha hb (hB c hc.2) (hB d hd.2)
      hab hc.1 hd.1 hcdV
  · have hbOne : 1 < (G.neighborSet b ∩ B).ncard := by omega
    rcases (Set.one_lt_ncard (s := G.neighborSet b ∩ B)).mp hbOne with
      ⟨c, hc, d, hd, hcdV⟩
    exact redEdge_twoBlueNeighbors_negative C hb ha (hB c hc.2) (hB d hd.2)
      hab.symm hc.1 hd.1 hcdV

/-- Finite form of Lemma 5.3: three distinct blue vertices, each adjacent to
at least one endpoint of the red edge, supply the required edge count. -/
theorem lemma5_3_of_three_neighbors
    (C : GoodColoring G) {a b x y z : V}
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (hx : C.color x = .blue) (hy : C.color y = .blue)
    (hz : C.color z = .blue)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hax : G.Adj a x ∨ G.Adj b x)
    (hay : G.Adj a y ∨ G.Adj b y)
    (haz : G.Adj a z ∨ G.Adj b z) :
    HasReachableNegativeReduction C := by
  classical
  let B : Set V := {x, y, z}
  apply lemma5_3 C B ha hb hab
  · intro v hv
    simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  · have hcard : B.ncard = 3 := by simp [B, hxy, hxz, hyz]
    have hcover : B ⊆
        (G.neighborSet a ∩ B) ∪ (G.neighborSet b ∩ B) := by
      intro v hv
      simp only [Set.mem_union, Set.mem_inter_iff]
      simp only [B, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl
      · rcases hax with h | h
        · exact Or.inl ⟨h, by simp [B]⟩
        · exact Or.inr ⟨h, by simp [B]⟩
      · rcases hay with h | h
        · exact Or.inl ⟨h, by simp [B]⟩
        · exact Or.inr ⟨h, by simp [B]⟩
      · rcases haz with h | h
        · exact Or.inl ⟨h, by simp [B]⟩
        · exact Or.inr ⟨h, by simp [B]⟩
    have hlower := Set.ncard_le_ncard hcover
    have hunion := Set.ncard_union_le
      (G.neighborSet a ∩ B) (G.neighborSet b ∩ B)
    unfold edgeCountFromPairToSet
    omega

end Subcubic
