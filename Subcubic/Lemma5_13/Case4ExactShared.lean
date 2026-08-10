import Subcubic.Lemma5_13.Case4SharedDG

/-! Lemma 5.13, the first branch of Case (4.4.3.3). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Case (4.4.3.3.1): the third neighbor `i` of the unique shared reddish
neighbor is blue and has a red neighbor `j`.  Flipping `ij` produces the
alternating path `a-b-c-d-h-i`. -/
theorem lemma5_13_case4_exact_shared_i_blue_red
    (C : GoodColoring G) {a b c d h i j : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hh : C.color h = .reddish) (hi : C.color i = .blue)
    (hj : C.color j = .red)
    (hdh : G.Adj d h) (hhi : G.Adj h i) (hij : G.Adj i j) :
    a ≠ j → b ≠ j → c ≠ i → d ≠ i →
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact fun _ _ _ _ => hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  intro haj hbj hci hdi
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
      (hx : C.color x = cx) (hy : C.color y = cy) (hne : cx ≠ cy) : x ≠ y := by
    intro e; subst y; simp_all
  have hjCorrect := C.color_correct j
  rw [hj] at hjCorrect
  obtain ⟨_, t, htSide, hjt⟩ := hjCorrect
  have htCases := (C.mem_redSide_iff t).1 htSide
  have ht : C.color t = .red := by
    rcases htCases with ht | ht
    · exact ht
    · exact (C.reddish_not_adj_redSide ht (Or.inl hj) hjt.symm).elim
  obtain ⟨k, hk, hik⟩ := C.exists_blue_mate hi
  rcases exists_flipAt_or_cutEnhancer C hj hi ht hk
      (degreeC (Or.inl hj)) (degreeC (Or.inr hi)) hjt hij.symm hik with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        haj (color_ne ha hi (by decide))
        hbj (color_ne hb hi (by decide))
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hbj (color_ne hb hi (by decide))
        haj (color_ne ha hi (by decide))
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (color_ne hc hj (by decide)) hci
        (color_ne hd hj (by decide)) hdi
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (color_ne hd hj (by decide)) hdi
        (color_ne hc hj (by decide)) hci
    have hhD : D.color h = .red :=
      red_of_reddish_gains_flipped_blue C hflip hh hhi
        (color_ne hh hj (by decide)) (color_ne hh hi (by decide))
    have hiD : D.color i = .red :=
      red_of_flipped_blue_endpoint C hflip hk hik
        (degreeC (Or.inr hi))
        (color_ne hk hj (by decide))
    have hn : [a, b, c, d, h, i].Nodup := by
      simp [hab.ne, hbc.ne, hcd.ne, hdh.ne, hhi.ne,
        color_ne ha hc (by decide), color_ne ha hd (by decide),
        color_ne ha hh (by decide), color_ne ha hi (by decide),
        color_ne hb hd (by decide), color_ne hb hh (by decide),
        color_ne hb hi (by decide), color_ne hc hh (by decide),
        hci, hdi]
    have hsub : FormsNegativePath6Subgraph G a b c d h i := by
      refine ⟨?_, ?_⟩
      · have hvec : (![a, b, c, d, h, i] : Fin 6 → V) =
            [a, b, c, d, h, i].get := by funext x; fin_cases x <;> rfl
        rw [hvec]
        exact hn.injective_get
      · intro x y hxy
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hdh, hhi] at hxy ⊢
    exact HasReachableNegativeReduction.after_flip C hflip
      (lemma5_12_inline D hsub haD hbD hcD hdD hhD hiD)
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
