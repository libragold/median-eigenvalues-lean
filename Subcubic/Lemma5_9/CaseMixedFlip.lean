import Subcubic.Lemma5_9.CaseMixedAdjacent

/-!
Lemma 5.9, Case (3.4.4.3.2.2): `p` is not adjacent to `l`.

Flip the cut preserver `np`.  The formerly blue vertex `m` becomes bluish,
and the case restarts at Case (3.4.4.1).  The proof explicitly recomputes
only the colors used by that earlier case.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_lm_mixed_flip
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (_hg : C.color g = .blue) (_hh : C.color h = .blue)
    (Q : Lemma5_9MixedPConfiguration C a b c d e f g h)
    (hpl : ¬ G.Adj Q.p Q.l) :
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
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hpPath : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all

  have hpCorrect := C.color_correct Q.p
  rw [Q.hp] at hpCorrect
  obtain ⟨_, q, hqSide, hpq⟩ := hpCorrect
  have hq : C.color q = .red := by
    rcases (C.mem_redSide_iff q).1 hqSide with hq | hq
    · exact hq
    · exact (C.reddish_not_adj_redSide hq (Or.inl Q.hp) hpq.symm).elim
  rcases exists_flipAt_or_cutEnhancer C Q.hp Q.hn hq Q.hm
      (degreeC (Or.inl Q.hp)) (degreeC (Or.inr Q.hn))
      hpq Q.hnp.symm Q.hmn.symm with ⟨M, hflip⟩ | hce
  · let D := M.toGoodColoring
    have hen : ¬ G.Adj e Q.n := by
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
      · exact color_ne hf Q.hj (by decide)
      · exact color_ne hd Q.hj (by decide)
      · exact color_ne Q.hn hf (by decide)
      · exact Q.hnd
      · exact color_ne Q.hn Q.hj (by decide)
    have hap : a ≠ Q.p := by
      intro hEq
      apply Q.hna
      simpa [hEq] using Q.hnp
    have hbp : b ≠ Q.p := by
      intro hEq
      apply Q.hnb
      simpa [hEq] using Q.hnp
    have hep : e ≠ Q.p := by
      intro hEq
      apply hen
      simpa [hEq] using Q.hnp.symm
    have hfp : f ≠ Q.p := by
      intro hEq
      apply Q.hnf
      simpa [hEq] using Q.hnp
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hap (color_ne ha Q.hn (by decide)) hbp (color_ne hb Q.hn (by decide))
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hbp (color_ne hb Q.hn (by decide)) hap (color_ne ha Q.hn (by decide))
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (color_ne hc Q.hp (by decide)) Q.hnc.symm
        (color_ne hd Q.hp (by decide)) Q.hnd.symm
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (color_ne hd Q.hp (by decide)) Q.hnd.symm
        (color_ne hc Q.hp (by decide)) Q.hnc.symm
    have heD : D.color e = .red :=
      red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
        hep (color_ne he Q.hn (by decide)) hfp (color_ne hf Q.hn (by decide))
    have hfD : D.color f = .red :=
      red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
        hfp (color_ne hf Q.hn (by decide)) hep (color_ne he Q.hn (by decide))
    have hiD : D.color Q.i = .reddish := by
      apply reddish_of_untouched_reddish C hflip Q.hi
        (by simpa [SimpleGraph.adj_comm] using Q.hni)
      · exact color_ne Q.hi Q.hp (by decide)
      · exact color_ne Q.hi Q.hn (by decide)
    have hjD : D.color Q.j = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hj
        (by simpa [SimpleGraph.adj_comm] using Q.hpj)
      · exact color_ne Q.hj Q.hp (by decide)
      · exact color_ne Q.hj Q.hn (by decide)
    have hkn : ¬ G.Adj Q.k Q.n := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hck.symm Q.hkl Q.hkm Q.hlc.symm Q.hmc.symm Q.hlm
      · exact Q.hnc
      · exact color_ne Q.hn Q.hl (by decide)
      · exact Q.hmn.ne.symm
    have hkD : D.color Q.k = .reddish := by
      apply reddish_of_untouched_reddish C hflip Q.hk hkn
      · exact color_ne Q.hk Q.hp (by decide)
      · exact color_ne Q.hk Q.hn (by decide)
    have hlD : D.color Q.l = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hl
        (by simpa [SimpleGraph.adj_comm] using hpl)
      · exact color_ne Q.hl Q.hp (by decide)
      · exact color_ne Q.hl Q.hn (by decide)
    have hmp : ¬ G.Adj Q.m Q.p := by
      apply C.not_adj_fourth_neighbor (Or.inr Q.hm) Q.hmn Q.hkm.symm Q.hmo
      · exact color_ne Q.hn Q.hk (by decide)
      · exact Q.hok.symm
      · exact Q.hon.symm
      · exact Q.hnp.ne.symm
      · exact color_ne Q.hp Q.hk (by decide)
      · exact color_ne Q.hp Q.ho (by decide)
    have hmD : D.color Q.m = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip Q.hm Q.hmn
        (by simpa [SimpleGraph.adj_comm] using hmp)
      · exact color_ne Q.hm Q.hp (by decide)
      · exact Q.hmn.ne

    have hxSide := D.other_neighbor_of_red_is_blueSide haD hbD hab Q.hax Q.hxb
    rcases hxSide with hxD | hxD
    · have hjx : ¬ G.Adj Q.j Q.x :=
        D.bluish_not_adj_blueSide hjD (Or.inl hxD)
      have hjd : ¬ G.Adj Q.j d :=
        D.bluish_not_adj_blueSide hjD (Or.inl hdD)
      have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
      have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
      have hxe : ¬ G.Adj Q.x e := by
        intro hxe
        exact (D.not_adj_fourth_neighbor (Or.inl heD) hef hde.symm Q.hej
          (hv (u := (5 : Fin 8)) (v := 3) (by decide))
          (vertex_ne_of_color_eq hfD hjD (by decide))
          (vertex_ne_of_color_eq hdD hjD (by decide))
          (by
            intro hEq
            exact (nonedge 0 5 (by native_decide)) (by simpa [hEq] using Q.hax))
          (by
            intro hEq
            exact (nonedge 0 3 (by native_decide)) (by simpa [hEq] using Q.hax))
          Q.hxj) hxe.symm
      have hxc : Q.x ≠ c := by
        intro hEq
        exact (nonedge 0 2 (by native_decide)) (by simpa [hEq] using Q.hax)
      have hxd : ¬ G.Adj Q.x d := by
        simpa [SimpleGraph.adj_comm] using
          D.blueSide_not_adj_second_neighbor
            (by simp [hdD]) (by simp [hcD]) (by simp [hxD]) hcd.symm hxc.symm
      have hceSwap := containsCutEnhancerB_of D.swapSides
        (by simp [hjD]) (by simp [haD]) (by simp [hxD])
        (by simp [heD]) (by simp [hdD])
        Q.hja Q.hej.symm Q.hax hde.symm hjx hjd hae had hxe hxd
      have hresult : HasReachableNegativeReduction D :=
        HasReachableNegativeReduction.of_current_ce D
          ((containsInducedUpToSwap_swapSides IsCutEnhancer D).1 hceSwap)
      exact HasReachableNegativeReduction.after_flip C hflip hresult
    · have hySide := D.other_neighbor_of_red_is_blueSide hbD haD hab.symm Q.hby Q.hya
      have hyd : Q.y ≠ d := by
        intro hEq
        exact (nonedge 1 3 (by native_decide)) (by simpa [hEq] using Q.hby)
      rcases lemma3_3 D hbD hcD hdD hySide hbc Q.hby hcd Q.hyc.symm hyd.symm with
        hyD | hceD
      · have hNoBlueAtAD : ∀ v, G.Adj a v → D.color v ≠ .blue := by
          intro v hav hvblue
          have hbj : b ≠ Q.j := vertex_ne_of_color_eq hbD hjD (by decide)
          rcases D.neighbor_eq_of_three_neighbors (Or.inl haD)
              hab Q.hja.symm Q.hax hbj Q.hxb.symm Q.hxj.symm hav with
            rfl | rfl | rfl
          · simp [hbD] at hvblue
          · simp [hjD] at hvblue
          · simp [hxD] at hvblue
        have hresult := lemma5_9_case_lm_bluish D hpPath haD hbD hcD hdD heD
          hNoBlueAtAD Q.toLemma5_9LMConfiguration hiD hjD hxD hyD hkD hlD hmD
        exact HasReachableNegativeReduction.after_flip C hflip hresult
      · exact HasReachableNegativeReduction.after_flip C hflip
          (HasReachableNegativeReduction.of_current_ce D hceD)
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
