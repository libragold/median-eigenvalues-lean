import Subcubic.Lemma5_13.Case3

/-!
# Lemma 5.13, Case (4): the local setup

We have oriented the path so that the bluish third neighbor `e` of `b`
is adjacent to `a`.  The vertex `g` is the remaining neighbor of `a`.
The paper's reduction to Case (2) lets us assume that every neighbor of `e`
other than `a,b` is reddish.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_13Case4Configuration (C : GoodColoring G)
    (a b c d : V) extends Lemma5_13ThirdNeighborConfiguration C a b c d where
  heaEdge : G.Adj e a
  hef : ¬ G.Adj e f
  g : V
  hg : C.color g = .bluish
  hag : G.Adj a g
  hgb : g ≠ b
  hge : g ≠ e
  /-- The third neighbor of `e`; it is reddish after excluding Case (2). -/
  r : V
  hr : C.color r = .reddish
  her : G.Adj e r
  hra : r ≠ a
  hrb : r ≠ b

/-- Construct the fixed vertices in Case (4).  A red third neighbor of `e`
is exactly the path-extension Case (2), so it is returned separately. -/
theorem lemma5_13_case4_setup
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_13ThirdNeighborConfiguration C a b c d)
    (hea : G.Adj Q.e a) (hef : ¬ G.Adj Q.e Q.f) :
    HasReachableNegativeReduction C ∨
      ∃ R : Lemma5_13Case4Configuration C a b c d,
        R.toLemma4_12ThirdNeighborConfiguration = Q := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact Or.inl hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  obtain ⟨g, hag, hgb, hge⟩ :=
    exists_third_neighbor_of_degree_three
      (degreeC (Or.inl ha))
      Q.hbe.ne
  have hgSide := C.other_neighbor_of_red_is_blueSide ha hb hab hag hgb
  have hg : C.color g = .bluish := by
    rcases hgSide with hg | hg
    · exact (hNoBlueAtA g hag hg).elim
    · exact hg
  obtain ⟨r, her, hra, hrb⟩ :=
    exists_third_neighbor_of_degree_three Q.hedeg hab.ne
  cases hr : C.color r with
  | red =>
      obtain ⟨R, hRQ⟩ := lemma5_13_case2_setup C Q hr her hra hrb
      subst Q
      rcases lemma5_13_case2_flip_path C ⟨hinj, hedge⟩ ha hb hc hd R with
          hresult | hpath3
      · exact Or.inl hresult
      · obtain ⟨P⟩ := hpath3
        exact Or.inl P.reduces
  | reddish =>
      exact Or.inr ⟨⟨Q, hea, hef, g, hg, hag, hgb, hge,
        r, hr, her, hra, hrb⟩, rfl⟩
  | blue =>
      exact (C.bluish_not_adj_blueSide Q.he (Or.inl hr) her).elim
  | bluish =>
      exact (C.bluish_not_adj_blueSide Q.he (Or.inr hr) her).elim

end Subcubic
