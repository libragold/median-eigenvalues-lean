import Subcubic.Lemma4_10.Basic

/-!
# The isolated-edge flip used in Lemma 4.10

This is case (2) of the prose proof.  Keeping it separate also makes the
color recomputation after flipping `bc` explicit.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_10_flip_bc_isolates_ef
    (C : MatchingCutColoring G) {a b c d e f g : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .bluish) (hbg : G.Adj b g)
    (hge : ¬ G.Adj g e) (hgf : ¬ G.Adj g f)
    (hNoBlueAtF : ∀ v, G.Adj f v → C.color v ≠ .blue) :
    HasReachableReduction C := by
  classical
  by_contra hresult
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath6 G a b c d e f := ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) :=
    hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    (hedge x y).mp hxy
  have nonedge (x y : Fin 6) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
  have heb : ¬ G.Adj e b := by simpa using nonedge 4 1 (by native_decide)
  have hec : ¬ G.Adj e c := by simpa using nonedge 4 2 (by native_decide)
  have hfb : ¬ G.Adj f b := by simpa using nonedge 5 1 (by native_decide)
  have hfc : ¬ G.Adj f c := by simpa using nonedge 5 2 (by native_decide)
  have noCurrentCE (hce : ContainsCutEnhancer C) : False :=
    hresult (HasReachableReduction.of_current_ce C hce)
  have degreeC {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hresult (.of_current_ptr C hptr)).elim
    · exact (noCurrentCE hce).elim
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
      (degreeC (Or.inl hb)) (degreeC (Or.inr hc)) hab.symm hbc hcd with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toColoring
    have heD : D.color e = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
      · exact hv (x := (4 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 2) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 2) (by decide)
    have hfD : D.color f = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
      · exact hv (x := (5 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 2) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 2) (by decide)
    have hdD : D.color d = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip hd hcd.symm
      · simpa using nonedge 3 1 (by native_decide)
      · exact hv (x := (3 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (3 : Fin 6)) (y := 2) (by decide)
    have b_saturated {z : V}
        (hza : z ≠ a) (hzc : z ≠ c) (hzg : z ≠ g) : ¬ G.Adj b z :=
      C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc hbg
        (hv (x := (0 : Fin 6)) (y := 2) (by decide))
        (by intro h; subst g; simp_all) (by intro h; subst g; simp_all)
        hza hzc hzg
    have e_other : ∀ z, G.Adj e z → z ≠ f → D.color z = .bluish := by
      intro z hez hzf
      by_cases hzd : z = d
      · simpa [hzd] using hdD
      have hzSide := C.other_neighbor_of_red_is_blueSide he hf hef hez hzf
      have hzc : z ≠ c := by intro h; subst z; exact hec hez
      rcases lemma3_3 C he hd hc hzSide hde.symm hez hcd.symm
          (Ne.symm hzd) (Ne.symm hzc) with hz | hce
      · have hza : z ≠ a := by intro h; subst z; simp_all
        have hzg : z ≠ g := by intro h; subst z; exact hge hez.symm
        have hzb := b_saturated hza hzc hzg
        apply bluish_of_untouched_bluish C hflip hz (fun h => hzb h.symm)
        · intro h; subst z; simp_all
        · exact hzc
      · exact (noCurrentCE hce).elim
    have f_other : ∀ z, G.Adj f z → z ≠ e → D.color z = .bluish := by
      intro z hfz hze
      have hzSide := C.other_neighbor_of_red_is_blueSide hf he hef.symm hfz hze
      have hz : C.color z = .bluish := by
        rcases hzSide with hz | hz
        · exact (hNoBlueAtF z hfz hz).elim
        · exact hz
      have hza : z ≠ a := by intro h; subst z; simp_all
      have hzc : z ≠ c := by intro h; subst z; exact hfc hfz
      have hzg : z ≠ g := by intro h; subst z; exact hgf hfz.symm
      have hzb := b_saturated hza hzc hzg
      apply bluish_of_untouched_bluish C hflip hz (fun h => hzb h.symm)
      · intro h; subst z; simp_all
      · exact hzc
    have degreeD {v : V}
        (hv : D.color v = .red ∨ D.color v = .blue) :
        vertexDegree G v = 3 := by
      rcases lemma3_6_positive D hv with hdegree | hptr | hceD
      · exact hdegree
      · exact (hresult (HasReachableReduction.after_flip C hflip
          (.of_current_ptr D hptr))).elim
      · exact (hresult (HasReachableReduction.after_flip C hflip
          (.of_current_ce D hceD))).elim
    have hptr := lemma4_4 D heD hfD hef
      (degreeD (Or.inl heD)) (degreeD (Or.inl hfD)) e_other f_other
    exact hresult (HasReachableReduction.after_flip C hflip
      (HasReachableReduction.of_current_ptr D hptr))
  · exact (noCurrentCE hce).elim

end Subcubic
