import Subcubic.Lemma5_13.Case4GMeetsF

/-! Lemma 5.13, Case (4.2): `g` has another red neighbor. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Case (4.2.1).  After flipping `hi`, the three monochromatic edges are
`cd`, `ab`, and `gh`.  We apply the color-swapped inline Lemma 5.12 to the
path `d-c-b-a-g-h`. -/
theorem lemma5_13_case4_red_neighbor_blue
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {h i : V} (hh : C.color h = .red) (hi : C.color i = .blue)
    (hgh : G.Adj Q.g h) (hhi : G.Adj h i) (hha : h ≠ a) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
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
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro e; subst y; simp_all
  have hhb : h ≠ b := by
    intro e
    subst h
    have hnot := C.not_adj_fourth_neighbor (Or.inl hb)
      hab.symm hbc Q.hbe
      (hv (x := (0 : Fin 4)) (y := 2) (by decide)) Q.hea.symm Q.hec.symm
      Q.hag.ne.symm (color_ne Q.hg hc (by decide)) Q.hge
    exact hnot hgh.symm
  have hci : c ≠ i := by
    intro e
    subst i
    have hnot := not_adj_fourth_neighbor_of_degree_three
      (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
      (hv (x := (1 : Fin 4)) (y := 3) (by decide))
      (color_ne hb Q.hf (by decide)) (color_ne hd Q.hf (by decide))
      hhb (color_ne hh hd (by decide)) (color_ne hh Q.hf (by decide))
    exact hnot hhi.symm
  have hdi : d ≠ i := by
    intro e
    subst i
    exact hNoRedAtD h hhi.symm hh
  have hhCorrect := C.color_correct h
  rw [hh] at hhCorrect
  obtain ⟨_, t, htSide, hht⟩ := hhCorrect
  have htSide' := (C.mem_redSide_iff t).1 htSide
  have ht : C.color t = .red := by
    rcases htSide' with ht | ht
    · exact ht
    · exact (C.reddish_not_adj_redSide ht (Or.inl hh) hht.symm).elim
  obtain ⟨j, hj, hij⟩ := C.exists_blue_mate hi
  rcases exists_flipAt_or_cutEnhancer C hh hi ht hj
      (degreeC (Or.inl hh)) (degreeC (Or.inr hi)) hht hhi hij with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toColoring
    have hai : a ≠ i := color_ne ha hi (by decide)
    have hbi : b ≠ i := color_ne hb hi (by decide)
    have hch : c ≠ h := color_ne hc hh (by decide)
    have hdh : d ≠ h := color_ne hd hh (by decide)
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb])
        hab hha.symm hai hhb.symm hbi
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha])
        hab.symm hhb.symm hbi hha.symm hai
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd])
        hcd hch hci hdh hdi
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc])
        hcd.symm hdh hdi hch hci
    have hgD : D.color Q.g = .blue := by
      apply blue_of_bluish_gains_flipped_red C hflip Q.hg hgh
      · exact hgh.ne
      · exact color_ne Q.hg hi (by decide)
    have hhD : D.color h = .blue :=
      blue_of_flipped_red_endpoint C hflip ht hht
        (degreeC (Or.inl hh))
        (color_ne ht hi (by decide))
    have hnodup : [d, c, b, a, Q.g, h].Nodup := by
      simp [hcd.ne.symm, hbc.ne.symm, hab.ne.symm, Q.hag.ne,
        hgh.ne, hha.symm, hhb.symm,
        color_ne hd hb (by decide), color_ne hd ha (by decide),
        color_ne hd Q.hg (by decide), color_ne hd hh (by decide),
        color_ne hc ha (by decide), color_ne hc Q.hg (by decide),
        color_ne hc hh (by decide), color_ne hb Q.hg (by decide)]
    have hsub : FormsNegativePath6Subgraph G d c b a Q.g h := by
      refine ⟨?_, ?_⟩
      · have hvec : (![d, c, b, a, Q.g, h] : Fin 6 → V) =
            [d, c, b, a, Q.g, h].get := by funext x; fin_cases x <;> rfl
        rw [hvec]
        exact hnodup.injective_get
      · intro x y hxy
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, G.adj_comm, hcd, hbc, hab, Q.hag,
            hgh.symm] at hxy ⊢
    have hDswap := lemma5_12_inline D.swapSides hsub
      (by simp [hdD]) (by simp [hcD]) (by simp [hbD]) (by simp [haD])
      (by simp [hgD]) (by simp [hhD])
    exact HasReachableNegativeReduction.after_flip C hflip
      (HasReachableNegativeReduction.of_swapSides D hDswap)
  · exact HasReachableNegativeReduction.of_current_ce C hce

/-- Complete Case (4.2).  If the new red vertex has a blue neighbor we use
the preceding flip lemma; otherwise two small negative reducers apply according
to whether it meets `e`. -/
theorem lemma5_13_case4_red_neighbor
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {h : V} (hh : C.color h = .red) (hgh : G.Adj Q.g h)
    (hha : h ≠ a) : HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  by_cases hBlue : ∃ i, G.Adj h i ∧ C.color i = .blue
  · obtain ⟨i, hhi, hi⟩ := hBlue
    exact lemma5_13_case4_red_neighbor_blue C hpath ha hb hc hd hNoRedAtD
      Q hh hi hgh hhi hha
  · have hNoBlue : ∀ i, G.Adj h i → C.color i ≠ .blue := by
      intro i hhi hi
      exact hBlue ⟨i, hhi, hi⟩
    dsimp [FormsInducedPath4] at hpath
    rcases hpath with ⟨hinj, hedge⟩
    have hv {x y : Fin 4} (hxy : x ≠ y) :
        (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
    have edge (x y : Fin 4)
        (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
        G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
    have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
    have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
    have color_ne {x y : V} {cx cy : Color}
        (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
      intro e; subst y; simp_all
    have hhb : h ≠ b := by
      intro e
      subst h
      have hnot := C.not_adj_fourth_neighbor (Or.inl hb)
        hab.symm hbc Q.hbe
        (hv (x := (0 : Fin 4)) (y := 2) (by decide)) Q.hea.symm Q.hec.symm
        Q.hag.ne.symm (color_ne Q.hg hc (by decide)) Q.hge
      exact hnot hgh.symm
    have hah : ¬ G.Adj a h := by
      apply not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
      · exact color_ne hb Q.he (by decide)
      · exact Q.hgb.symm
      · exact Q.hge.symm
      · exact hhb
      · exact color_ne hh Q.he (by decide)
      · exact hgh.ne.symm
    by_cases hhe : G.Adj h Q.e
    · apply HasReachableNegativeReduction.of_current_ntr C
      apply containsNegativeB C (a := a) (b := h) (c := Q.e) (d := Q.g)
        ha hh Q.he Q.hg Q.heaEdge.symm Q.hag hhe hgh.symm hah
      simp [hha.symm, Q.hge.symm,
        color_ne ha Q.he (by decide), color_ne ha Q.hg (by decide),
        color_ne hh Q.he (by decide), color_ne hh Q.hg (by decide)]
    · have hhCorrect := C.color_correct h
      rw [hh] at hhCorrect
      obtain ⟨_, t, htSide, hht⟩ := hhCorrect
      have htSide' := (C.mem_redSide_iff t).1 htSide
      have ht : C.color t = .red := by
        rcases htSide' with ht | ht
        · exact ht
        · exact (C.reddish_not_adj_redSide ht (Or.inl hh) hht.symm).elim
      obtain ⟨u, hhu, hug, hut⟩ :=
        exists_third_neighbor_of_degree_three
          (degreeC (Or.inl hh))
          (color_ne Q.hg ht (by decide))
      have huSide := C.other_neighbor_of_red_is_blueSide hh ht hht hhu hut
      have hu : C.color u = .bluish := by
        rcases huSide with hu | hu
        · exact (hNoBlue u hhu hu).elim
        · exact hu
      have hue : u ≠ Q.e := by
        intro e; subst u; exact hhe hhu
      have hau : ¬ G.Adj a u := by
        apply not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
        · exact color_ne hb Q.he (by decide)
        · exact Q.hgb.symm
        · exact Q.hge.symm
        · exact color_ne hu hb (by decide)
        · exact hue
        · exact hug
      apply HasReachableNegativeReduction.of_current_ntr C
      apply containsNegativeD C
        (a := a) (b := h) (c := Q.e) (d := Q.g) (e := u)
        ha hh Q.he Q.hg hu Q.heaEdge.symm Q.hag hgh.symm hhu
        hah hau hhe
      simp [hha.symm, Q.hge.symm, hue.symm, hug.symm,
        color_ne ha Q.he (by decide), color_ne ha Q.hg (by decide),
        color_ne ha hu (by decide), color_ne hh Q.he (by decide),
        color_ne hh Q.hg (by decide), color_ne hh hu (by decide)]

end Subcubic
