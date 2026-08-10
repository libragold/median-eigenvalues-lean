import Subcubic.Lemma4_12.ThirdNeighborSetup

/-! Case (1) of Lemma 4.12: the two exposed third neighbors are adjacent. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_12_case_ef
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma4_12ThirdNeighborConfiguration C a b c d)
    (hef : G.Adj Q.e Q.f) : HasReachableReduction C := by
  classical
  by_contra hresult
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have noCurrentCE (hce : ContainsCutEnhancer C) : False :=
    hresult (HasReachableReduction.of_current_ce C hce)
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hresult (.of_current_ptr C hptr)).elim
    · exact (hresult (.of_current_ce C hce)).elim
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
      (degreeC (Or.inl hb)) (degreeC (Or.inr hc)) hab.symm hbc hcd with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hbD : D.color b = .blue :=
      blue_of_flipped_red_endpoint C hflip ha hab.symm
        (degreeC (Or.inl hb))
        (hv (x := (0 : Fin 4)) (y := 2) (by decide))
    have hcD : D.color c = .red :=
      red_of_flipped_blue_endpoint C hflip hd hcd
        (degreeC (Or.inr hc))
        (hv (x := (3 : Fin 4)) (y := 1) (by decide))
    have heD : D.color Q.e = .blue := by
      apply blue_of_bluish_gains_flipped_red C hflip Q.he Q.hbe.symm
      · exact Q.hbe.ne.symm
      · exact Q.hec
    have hfD : D.color Q.f = .red := by
      apply red_of_reddish_gains_flipped_blue C hflip Q.hf Q.hcf.symm
      · exact Q.hfb
      · exact Q.hcf.ne.symm
    have hfe : G.Adj Q.f Q.e := hef.symm
    have hout := lemma4_2 D c Q.f b Q.e Q.hcf hcD hfD Q.hbe hbD heD (by
      simp [fourVertexCrossEdgeCount, hbc.symm, hfe]
      omega)
    have hD := hout.elim (HasReachableReduction.of_current_ptr D)
      (HasReachableReduction.of_current_ce D)
    exact hresult (HasReachableReduction.after_flip C hflip hD)
  · exact (noCurrentCE hce).elim

end Subcubic
