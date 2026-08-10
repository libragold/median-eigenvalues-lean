import Subcubic.Lemma4_12.InlinePath3Cases

/-! The final flip subcase of the shared-neighbor branch in Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Case (3.1.2.3): `h` has no red neighbor, while its blue mate `i` has
a red neighbor `j`.  After flipping `ij`, the six vertices
`g,b,h,e,d,c` induce `m+` in the recomputed coloring. -/
theorem lemma4_12_shared_i_red_flip
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (R : Lemma4_12SharedBlueConfiguration C a b c d)
    (hOnlyRedB : ∀ z, G.Adj R.e z → C.color z = .red → z = b)
    (hNoRedH : ∀ z, G.Adj R.h z → C.color z ≠ .red)
    {j : V} (hj : C.color j = .red) (hij : G.Adj R.i j) :
    HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have nonedge (x y : Fin 4)
      (hxy : ¬ (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d] x) (![a, b, c, d] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hbd : ¬ G.Adj b d := by
    simpa using nonedge 1 3 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) :
      x ≠ y := by
    intro h
    subst y
    simp_all
  have hhc : R.h ≠ c := by
    intro h
    exact hNoRedH b (by simpa [h] using hbc.symm) hb
  have hic : R.i ≠ c := by
    intro h
    have hnot := C.blueSide_not_adj_second_neighbor
      (by simp [hc]) (by simp [hd]) (by simp [R.hh])
      hcd R.hhd.symm
    exact hnot (by simpa [h] using R.hhi.symm)
  have hid : R.i ≠ d := by
    intro h
    have hnot := C.blueSide_not_adj_second_neighbor
      (by simp [hd]) (by simp [hc]) (by simp [R.hh])
      hcd.symm hhc.symm
    exact hnot (by simpa [h] using R.hhi.symm)
  have hbi : ¬ G.Adj b R.i := by
    apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc R.hbe
    · exact hv (x := (0 : Fin 4)) (y := 2) (by decide)
    · exact R.hea.symm
    · exact R.hec.symm
    · exact color_ne R.hi ha (by decide)
    · exact hic
    · exact color_ne R.hi R.he (by decide)
  have hjb : j ≠ b := by
    intro h
    subst j
    exact hbi hij.symm
  have hja : j ≠ a := by
    intro h
    subst j
    exact hNoBlueAtA R.i hij.symm R.hi
  have hej : ¬ G.Adj R.e j := by
    intro hej
    exact hjb (hOnlyRedB j hej hj)
  have hjCorrect := C.color_correct j
  rw [hj] at hjCorrect
  obtain ⟨_, k, hkSide, hjk⟩ := hjCorrect
  have hkSide' := (C.mem_redSide_iff k).1 hkSide
  have hk : C.color k = .red := by
    rcases hkSide' with hk | hk
    · exact hk
    · exact (C.reddish_not_adj_redSide hk (Or.inl hj) hjk.symm).elim
  rcases exists_flipAt_or_cutEnhancer C hj R.hi hk R.hh
      (degreeC (Or.inl hj)) (degreeC (Or.inr R.hi))
      hjk hij.symm R.hhi.symm with hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hja.symm (color_ne ha R.hi (by decide))
        hjb.symm (color_ne hb R.hi (by decide))
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hjb.symm (color_ne hb R.hi (by decide))
        hja.symm (color_ne ha R.hi (by decide))
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (color_ne hc hj (by decide)) hic.symm
        (color_ne hd hj (by decide)) hid.symm
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (color_ne hd hj (by decide)) hid.symm
        (color_ne hc hj (by decide)) hic.symm
    have heD : D.color R.e = .bluish := by
      apply bluish_of_untouched_bluish C hflip R.he hej
      · exact color_ne R.he hj (by decide)
      · exact color_ne R.he R.hi (by decide)
    have hhj : ¬ G.Adj R.h j := fun h => hNoRedH j h hj
    have hhD : D.color R.h = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip R.hh R.hhi hhj
      · exact color_ne R.hh hj (by decide)
      · exact R.hhi.ne
    have hge : R.g ≠ R.e := R.heg.ne.symm
    have hgd : R.g ≠ d := R.hdg.ne.symm
    have hgh : R.g ≠ R.h := R.hgh.ne
    have hei : R.e ≠ R.i := color_ne R.he R.hi (by decide)
    have hdi : d ≠ R.i := hid.symm
    have hhi : R.h ≠ R.i := R.hhi.ne
    have hgi : ¬ G.Adj R.g R.i := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        R.heg.symm R.hdg.symm R.hgh
      · exact color_ne R.he hd (by decide)
      · exact color_ne R.he R.hh (by decide)
      · exact R.hhd.symm
      · exact hei.symm
      · exact hid
      · exact hhi.symm
    have hgD : D.color R.g = .reddish := by
      apply reddish_of_untouched_reddish C hflip R.hg hgi
      · exact color_ne R.hg hj (by decide)
      · exact color_ne R.hg R.hi (by decide)
    have hgb : ¬ G.Adj R.g b :=
      C.reddish_not_adj_redSide R.hg (Or.inl hb)
    have hgc : ¬ G.Adj R.g c := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        R.heg.symm R.hdg.symm R.hgh
      · exact color_ne R.he hd (by decide)
      · exact color_ne R.he R.hh (by decide)
      · exact R.hhd.symm
      · exact color_ne hc R.he (by decide)
      · exact hcd.ne
      · exact hhc.symm
    have hbh : ¬ G.Adj b R.h := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc R.hbe
      · exact hv (x := (0 : Fin 4)) (y := 2) (by decide)
      · exact R.hea.symm
      · exact R.hec.symm
      · exact color_ne R.hh ha (by decide)
      · exact hhc
      · exact color_ne R.hh R.he (by decide)
    apply HasReachableReduction.after_flip C hflip
    apply HasReachableReduction.of_current_ptr D
    apply containsPositiveM D (a := R.g) (b := b) (c := R.h)
      (d := R.e) (e := d) (f := c) hgD hbD hhD heD hdD hcD
      R.hgh R.heg.symm R.hdg.symm R.hbe hbc hcd.symm
      hgb hgc hbh hbd
    simp [List.nodup_cons, hgh, hge, hgd, R.hhd, hcd.ne.symm,
      color_ne R.hg hb (by decide),
      color_ne R.hg hc (by decide), color_ne hb R.hh (by decide),
      color_ne hb R.he (by decide), color_ne hb hd (by decide),
      color_ne hb hc (by decide), color_ne R.hh R.he (by decide),
      hhc, color_ne R.he hd (by decide), R.hec]
  · exact HasReachableReduction.of_current_ce C hce

end Subcubic
