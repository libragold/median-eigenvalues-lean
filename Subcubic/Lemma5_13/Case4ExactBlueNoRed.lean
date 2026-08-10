import Subcubic.Lemma5_13.Case4ExactNoRed

/-! Lemma 5.13, the blue/no-red-neighbor part of Case (4.4.3.3.2). -/

namespace Subcubic

set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- If `i` is blue but has no red neighbor, its third neighbor `q` is
reddish.  According as `q` is also the remaining reddish neighbor of `d`,
Figures 5(b) or 5(d) apply. -/
theorem lemma5_13_case4_exact_blue_no_red
    (C : GoodColoring G) {c d h s i : V}
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hh : C.color h = .reddish) (hs : C.color s = .reddish)
    (hi : C.color i = .blue)
    (hcd : G.Adj c d) (hdh : G.Adj d h) (hds : G.Adj d s)
    (hsh : s ≠ h) (hih : G.Adj i h)
    (hci : c ≠ i) (hdi : d ≠ i)
    (hNoRedI : ∀ z, G.Adj i z → C.color z ≠ .red) :
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
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hne : cx ≠ cy) : x ≠ y := by
    intro e; subst y; simp_all
  obtain ⟨m, hm, him⟩ := C.exists_blue_mate hi
  have hhm : h ≠ m := vertex_ne_of_color_eq hh hm (by decide)
  obtain ⟨q, hiq, hqh, hqm⟩ :=
    exists_third_neighbor_of_degree_three
      (degreeC (Or.inr hi)) hhm
  have hq : C.color q = .reddish := by
    cases hcq : C.color q with
    | red => exact (hNoRedI q hiq hcq).elim
    | reddish => rfl
    | blue =>
        exact ((C.blueSide_not_adj_second_neighbor
          (by simp [hi]) (by simp [hm]) (by simp [hcq]) him hqm.symm) hiq).elim
    | bluish =>
        exact ((C.blueSide_not_adj_second_neighbor
          (by simp [hi]) (by simp [hm]) (by simp [hcq]) him hqm.symm) hiq).elim
  have hdiAdj : ¬ G.Adj d i :=
    C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
      (by simp [hi]) hcd.symm hci
  by_cases hqs : q = s
  · subst q
    apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegativeB C.swapSides
      (by simp [hd]) (by simp [hi]) (by simp [hh]) (by simp [hs])
      hdh hds hih hiq hdiAdj
    simp [hdh.ne, hds.ne, hih.ne, hiq.ne, hsh, hsh.symm, hci, hdi,
      color_ne hd hh (by decide),
      color_ne hd hs (by decide), color_ne hi hh (by decide),
      color_ne hi hs (by decide)]
  · have hdq : ¬ G.Adj d q := by
      exact C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hdh hds
        (vertex_ne_of_color_eq hc hh (by decide))
        (vertex_ne_of_color_eq hc hs (by decide)) hsh.symm
        (vertex_ne_of_color_eq hq hc (by decide)) hqh hqs
    have his : ¬ G.Adj i s := by
      exact C.not_adj_fourth_neighbor (Or.inr hi) him hih hiq
        (vertex_ne_of_color_eq hm hh (by decide))
        (vertex_ne_of_color_eq hm hq (by decide)) hqh.symm
        (vertex_ne_of_color_eq hs hm (by decide)) hsh (Ne.symm hqs)
    apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegativeD C.swapSides
      (by simp [hd]) (by simp [hi]) (by simp [hs]) (by simp [hh])
      (by simp [hq]) hds hdh hih hiq hdiAdj hdq his
    simp [hdh.ne, hds.ne, hih.ne, hiq.ne, hsh, hsh.symm, hqs,
      Ne.symm hqs, hci, hdi, hqh, hqh.symm,
      color_ne hd hs (by decide),
      color_ne hd hh (by decide), color_ne hd hq (by decide),
      color_ne hi hs (by decide), color_ne hi hh (by decide),
      color_ne hi hq (by decide)]

end Subcubic
