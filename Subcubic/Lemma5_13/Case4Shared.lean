import Subcubic.Lemma5_13.Case4Setup

/-! Lemma 5.13, Case (4.1): `d` and `e` share a reddish neighbor. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_shared_de
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {s : V} (hs : C.color s = .reddish)
    (hes : G.Adj Q.e s) (hds : G.Adj d s) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : ¬ G.Adj d Q.e :=
    C.bluish_not_adj_blueSide Q.he (Or.inl hd) ∘ SimpleGraph.Adj.symm
  have hda : ¬ G.Adj d a := by
    intro h; exact hNoRedAtD a h ha
  have hdb : ¬ G.Adj d b := by
    intro h; exact hNoRedAtD b h hb
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h; subst y; simp_all
  have emit (t : V) (ht : C.color t = .reddish) (hdt : G.Adj d t)
      (hts : t ≠ s) (het : ¬ G.Adj Q.e t) :
      ContainsNegativeTailReducer C := by
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegativeH C.swapSides
      (a := d) (b := Q.e) (c := t) (d := s) (e := a) (f := b)
      (by simp [hd]) (by simp [Q.he]) (by simp [ht]) (by simp [hs])
      (by simp [ha]) (by simp [hb])
      hdt hds hes Q.heaEdge Q.hbe.symm hab
      hde hda hdb het
    simp [color_ne hd Q.he (by decide), color_ne hd ht (by decide),
      color_ne hd hs (by decide), color_ne hd ha (by decide),
      color_ne hd hb (by decide), color_ne Q.he ht (by decide),
      color_ne Q.he hs (by decide), color_ne Q.he ha (by decide),
      color_ne Q.he hb (by decide), hts, color_ne ht ha (by decide),
      color_ne ht hb (by decide), color_ne hs ha (by decide),
      color_ne hs hb (by decide), hab.ne]
  by_cases hfd : G.Adj Q.f d
  · exact HasReachableNegativeReduction.of_current_ntr C
      (emit Q.f Q.hf hfd.symm (by
        intro h; subst s; exact Q.hef hes) Q.hef)
  · obtain ⟨t, hdt, htc, hts⟩ :=
      exists_third_neighbor_of_degree_three
        (degreeC (Or.inr hd))
        (color_ne hc hs (by decide))
    have htSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdt htc
    have ht : C.color t = .reddish := by
      rcases htSide with ht | ht
      · exact (hNoRedAtD t hdt ht).elim
      · exact ht
    have htb : t ≠ b := color_ne ht hb (by decide)
    have hta : t ≠ a := color_ne ht ha (by decide)
    have het : ¬ G.Adj Q.e t := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hedeg
        Q.hbe.symm Q.heaEdge hes
      · exact hab.ne.symm
      · exact color_ne hb hs (by decide)
      · exact color_ne ha hs (by decide)
      · exact htb
      · exact hta
      · exact hts
    exact HasReachableNegativeReduction.of_current_ntr C
      (emit t ht hdt hts het)

end Subcubic
