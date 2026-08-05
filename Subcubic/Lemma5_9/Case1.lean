import Subcubic.Lemma5_9.Basic

/-! Lemma 5.9, Case (1): `i ~ g`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_i_adj_g
    (C : GoodColoring G) {c d e f g h i : V}
    (hpath : FormsInducedPath6 G c d e f g h)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hdi : G.Adj d i) (hig : G.Adj i g) :
    HasReachableNegativeReduction C := by
  have hout := lemma5_6 C.swapSides hpath.reverse
    (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
    (by simp [hd]) (by simp [hc])
  rcases hout with hnone | hntr | hce
  · exact (hnone ⟨i, hig.symm, hdi⟩).elim
  · exact HasReachableNegativeReduction.of_swapSides C
      (HasReachableNegativeReduction.of_current_ntr C.swapSides hntr)
  · exact HasReachableNegativeReduction.of_swapSides C
      (HasReachableNegativeReduction.of_current_ce C.swapSides hce)

end Subcubic
