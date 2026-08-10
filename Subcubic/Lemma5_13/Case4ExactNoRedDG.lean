import Subcubic.Lemma5_13.Case4ExactNoOverlap

/-! Lemma 5.13, Case (4.4.3.3.2.1). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(e): the bluish vertex `i` and the blue vertex `d` have the
reddish neighbors `h,z` in common. -/
theorem lemma5_13_case4_exact_no_red_shared_d
    (C : GoodColoring G) {d h i z u : V}
    (hd : C.color d = .blue) (hi : C.color i = .bluish)
    (hh : C.color h = .reddish) (hz : C.color z = .reddish)
    (hu : C.color u = .reddish)
    (hdh : G.Adj d h) (hdz : G.Adj d z)
    (hih : G.Adj i h) (hiz : G.Adj i z) (hiu : G.Adj i u)
    (hdi : ¬ G.Adj d i) (hdu : ¬ G.Adj d u)
    (hn : [d, i, h, z, u].Nodup) :
    HasReachableNegativeReduction C := by
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegativeE C.swapSides
    (by simp [hd]) (by simp [hi]) (by simp [hh]) (by simp [hz])
    (by simp [hu]) hdh hdz hih hiz hiu hdi hdu hn

end Subcubic
