import Subcubic.Lemma4_8.CaseIAdjG

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The second top-level case.  The endpoint hypothesis at `h` is what makes
the blue edge `gh` isolated after flipping `de`. -/
theorem lemma4_8_case_i_not_adj_g_h
    (C : MatchingCutColoring G) {a b c d e f g h i j : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .reddish) (hj : C.color j = .bluish)
    (hdi : G.Adj d i) (hej : G.Adj e j)
    (hig : ¬ G.Adj i g) (hih : ¬ G.Adj i h)
    (hNoRedAtH : ∀ v, G.Adj h v → C.color v ≠ .red) :
    HasReachableReduction C := by
  classical
  by_contra hresult
  have noCurrentCE (hce : ContainsCutEnhancer C) : False :=
    hresult (HasReachableReduction.of_current_ce C hce)
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 8} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h] x) ≠
        (![a, b, c, d, e, f, g, h] y) := hinj.ne hxy
  have hcd : G.Adj c d := (hedge 2 3).mp (by native_decide)
  have hde : G.Adj d e := (hedge 3 4).mp (by native_decide)
  have hef : G.Adj e f := (hedge 4 5).mp (by native_decide)
  have hfg : G.Adj f g := (hedge 5 6).mp (by native_decide)
  have hgh : G.Adj g h := (hedge 6 7).mp (by native_decide)
  have path_nonedge (x y : Fin 8)
      (hxy : ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) :=
    fun hxyG => hxy ((hedge x y).mpr hxyG)
  obtain ⟨M, hflip⟩ := exists_flipAt_of_local C
    he hd hf hc (Or.inl hj) (Or.inl hi) hef hde.symm hej hcd.symm hdi
  let D := M.toColoring
  have hgD : D.color g = .blue := by
    apply blue_of_untouched_blue_edge C hflip
      (by simp [hg]) (by simp [hh]) hgh
    · exact hv (x := (6 : Fin 8)) (y := 4) (by decide)
    · exact hv (x := (6 : Fin 8)) (y := 3) (by decide)
    · exact hv (x := (7 : Fin 8)) (y := 4) (by decide)
    · exact hv (x := (7 : Fin 8)) (y := 3) (by decide)
  have hhD : D.color h = .blue := by
    apply blue_of_untouched_blue_edge C hflip
      (by simp [hh]) (by simp [hg]) hgh.symm
    · exact hv (x := (7 : Fin 8)) (y := 4) (by decide)
    · exact hv (x := (7 : Fin 8)) (y := 3) (by decide)
    · exact hv (x := (6 : Fin 8)) (y := 4) (by decide)
    · exact hv (x := (6 : Fin 8)) (y := 3) (by decide)
  have hfD : D.color f = .reddish := by
    apply reddish_of_red_loses_flipped_mate C hflip hf hef.symm
    · simpa using path_nonedge 5 3 (by native_decide)
    · exact (hv (x := (5 : Fin 8)) (y := 4) (by decide))
    · exact (hv (x := (5 : Fin 8)) (y := 3) (by decide))
  have d_has_no_fourth {z : V}
      (hzc : z ≠ c) (hze : z ≠ e) (hzi : z ≠ i) :
      ¬ G.Adj d z :=
    C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
      (hv (x := (2 : Fin 8)) (y := 4) (by decide))
      (by intro h; subst i; simp_all)
      (by intro h; subst i; simp_all) hzc hze hzi
  have g_other : ∀ z, G.Adj g z → z ≠ h → D.color z = .reddish := by
    intro z hgz hzh
    by_cases hzf : z = f
    · simpa [hzf] using hfD
    have hzSide := C.other_neighbor_of_blue_is_redSide
      hg hh hgh hgz hzh
    have hze : z ≠ e := by
      intro h; subst z
      exact (path_nonedge 6 4 (by native_decide)) hgz
    rcases lemma3_3_reversed C hg hf he hzSide hfg.symm hgz
        hef.symm (Ne.symm hzf) hze.symm with hz | hce
    · apply reddish_of_untouched_reddish C hflip hz
      · intro hzd
        apply d_has_no_fourth _ hze _ hzd.symm
        · intro h; subst z; simp_all
        · intro h; subst z; exact hig hgz.symm
      · exact hze
      · intro h; subst z; simp_all
    · exact (noCurrentCE hce).elim
  have h_other : ∀ z, G.Adj h z → z ≠ g → D.color z = .reddish := by
    intro z hhz hzg
    have hzSide := C.other_neighbor_of_blue_is_redSide
      hh hg hgh.symm hhz hzg
    have hz : C.color z = .reddish := by
      rcases hzSide with hz | hz
      · exact (hNoRedAtH z hhz hz).elim
      · exact hz
    have hze : z ≠ e := by intro h; subst z; simp_all
    apply reddish_of_untouched_reddish C hflip hz
    · intro hzd
      apply d_has_no_fourth _ hze _ hzd.symm
      · intro h; subst z; simp_all
      · intro h; subst z; exact hih hhz.symm
    · exact hze
    · intro h; subst z; simp_all
  have degreeD {z : V}
      (hz : D.color z = .red ∨ D.color z = .blue) :
      vertexDegree G z = 3 := by
    rcases lemma3_6_positive D hz with hdegree | hptr | hce
    · exact hdegree
    · exact (hresult (HasReachableReduction.after_flip C hflip
        (HasReachableReduction.of_current_ptr D hptr))).elim
    · exact (hresult (HasReachableReduction.after_flip C hflip
        (HasReachableReduction.of_current_ce D hce))).elim
  have hptrSwap : ContainsPositiveTailReducer D.swapSides :=
    lemma4_4 D.swapSides
      (by simp [hgD]) (by simp [hhD]) hgh
      (degreeD (Or.inr hgD)) (degreeD (Or.inr hhD))
      (by
        intro z hgz hzh
        have := g_other z hgz hzh
        simp [this])
      (by
        intro z hhz hzg
        have := h_other z hhz hzg
        simp [this])
  have hptr : ContainsPositiveTailReducer D :=
    (containsInducedUpToSwap_swapSides IsPositiveTailReducer D).1 hptrSwap
  exact hresult (HasReachableReduction.after_flip C hflip
    (HasReachableReduction.of_current_ptr D hptr))

end Subcubic
