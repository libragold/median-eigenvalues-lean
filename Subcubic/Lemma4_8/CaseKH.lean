import Subcubic.Lemma4_8.CaseKJ

/-! Case (3.4.2) of Lemma 4.8. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_case_k_not_adj_j_adj_h
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8KConfiguration C a b c d e f g h)
    (hkj : ¬ G.Adj Q.k Q.j) (hkh : G.Adj Q.k h) :
    HasReachableReduction C := by
  classical
  rcases Q with ⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, k, hk, hck, hkb, hkd, hkg, hkdeg⟩
  change ¬ G.Adj k j at hkj
  change G.Adj k h at hkh
  change ¬ G.Adj i c at hic
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8)
      (huv : (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8)
      (huv : ¬ (graphOfEdges
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
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have hca : ¬ G.Adj c a := by
    simpa using nonedge 2 0 (by native_decide)
  have hkc : k ≠ c := hck.ne.symm
  have hib : i ≠ b := by
    intro hib
    rw [hib] at hi
    simp [hb] at hi
  have hicV : i ≠ c := by
    intro hicV
    rw [hicV] at hi
    simp [hc] at hi
  have hjbV : j ≠ b := by
    intro hjbV
    rw [hjbV] at hj
    simp [hb] at hj
  have hjcV : j ≠ c := by
    intro hjcV
    rw [hjcV] at hj
    simp [hc] at hj
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd hab.symm hbc hcd
      with hflip1 | hce
  · obtain ⟨M₁, hflip1⟩ := hflip1
    let D := M₁.toGoodColoring
    have hcD : D.color c = .red := by
      apply red_of_flipped_blue_with_reddish_neighbor C hflip1 hk hck
      · exact hkb
      · exact hkc
    have hkD : D.color k = .red := by
      apply red_of_reddish_gains_flipped_blue C hflip1 hk hck.symm
      · exact hkb
      · exact hkc
    have hgD : D.color g = .blue := by
      apply blue_of_untouched_blue_edge C hflip1 (by simp [hg]) (by simp [hh]) hgh
      · exact hv (u := (6 : Fin 8)) (v := 1) (by decide)
      · exact hv (u := (6 : Fin 8)) (v := 2) (by decide)
      · exact hv (u := (7 : Fin 8)) (v := 1) (by decide)
      · exact hv (u := (7 : Fin 8)) (v := 2) (by decide)
    have hhD : D.color h = .blue := by
      apply blue_of_untouched_blue_edge C hflip1 (by simp [hh]) (by simp [hg]) hgh.symm
      · exact hv (u := (7 : Fin 8)) (v := 1) (by decide)
      · exact hv (u := (7 : Fin 8)) (v := 2) (by decide)
      · exact hv (u := (6 : Fin 8)) (v := 1) (by decide)
      · exact hv (u := (6 : Fin 8)) (v := 2) (by decide)
    have hiD : D.color i = .reddish := by
      apply reddish_of_untouched_reddish C hflip1 hi hic
      · exact hib
      · exact hicV
    have hjD : D.color j = .bluish := by
      apply bluish_of_untouched_bluish C hflip1 hj
        (by simpa [SimpleGraph.adj_comm] using hjb)
      · exact hjbV
      · exact hjcV
    have haD : D.color a = .reddish := by
      apply reddish_of_red_loses_flipped_mate C hflip1 ha hab
      · simpa [SimpleGraph.adj_comm] using hca
      · exact hab.ne
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
    have hdD : D.color d = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip1 hd hcd.symm
      · simpa using nonedge 3 1 (by native_decide)
      · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
      · exact hcd.ne.symm
    have hhc : ¬ G.Adj h c := by
      simpa using nonedge 7 2 (by native_decide)
    rcases exists_flipAt_or_cutEnhancer D hkD hhD hcD hgD hck.symm hkh hgh.symm
        with hflip2 | hceD
    · obtain ⟨M₂, hflip2⟩ := hflip2
      let E := M₂.toGoodColoring
      have heD : D.color e = .red := by
        apply red_of_untouched_red_edge C hflip1 (by simp [he]) (by simp [hf]) hef
        · exact hv (u := (4 : Fin 8)) (v := 1) (by decide)
        · exact hv (u := (4 : Fin 8)) (v := 2) (by decide)
        · exact hv (u := (5 : Fin 8)) (v := 1) (by decide)
        · exact hv (u := (5 : Fin 8)) (v := 2) (by decide)
      have hfD : D.color f = .red := by
        apply red_of_untouched_red_edge C hflip1 (by simp [hf]) (by simp [he]) hef.symm
        · exact hv (u := (5 : Fin 8)) (v := 1) (by decide)
        · exact hv (u := (5 : Fin 8)) (v := 2) (by decide)
        · exact hv (u := (4 : Fin 8)) (v := 1) (by decide)
        · exact hv (u := (4 : Fin 8)) (v := 2) (by decide)
      have hek : e ≠ k := by
        intro hek
        rw [← hek] at hk
        simp [he] at hk
      have hfkV : f ≠ k := by
        intro hfkV
        rw [← hfkV] at hk
        simp [hf] at hk
      have hik : i ≠ k := by
        intro hik
        rw [hik] at hiD
        simp [hkD] at hiD
      have hgkV : g ≠ k := by
        intro hgkV
        rw [← hgkV] at hk
        simp [hg] at hk
      have hjkV : j ≠ k := by
        intro hjkV
        rw [hjkV] at hjD
        simp [hkD] at hjD
      have heE : E.color e = .red := by
        apply red_of_untouched_red_edge D hflip2 (by simp [heD]) (by simp [hfD]) hef
        · exact hek
        · exact hv (u := (4 : Fin 8)) (v := 7) (by decide)
        · exact hfkV
        · exact hv (u := (5 : Fin 8)) (v := 7) (by decide)
      have hfE : E.color f = .red := by
        apply red_of_untouched_red_edge D hflip2 (by simp [hfD]) (by simp [heD]) hef.symm
        · exact hfkV
        · exact hv (u := (5 : Fin 8)) (v := 7) (by decide)
        · exact hek
        · exact hv (u := (4 : Fin 8)) (v := 7) (by decide)
      have hiE : E.color i = .red := by
        apply red_of_reddish_gains_flipped_blue D hflip2 hiD hih
        · exact hik
        · exact hih.ne
      have hhE : E.color h = .red := by
        apply red_of_flipped_blue_endpoint D hflip2 hgD hgh.symm
        exact hgkV
      have hkE : E.color k = .blue := by
        apply blue_of_flipped_red_endpoint D hflip2 hcD hck.symm
        exact hv (u := (2 : Fin 8)) (v := 7) (by decide)
      have hcE : E.color c = .reddish := by
        apply reddish_of_red_loses_flipped_mate D hflip2 hcD hck
        · simpa [SimpleGraph.adj_comm] using hhc
        · exact hck.ne
        · exact hv (u := (2 : Fin 8)) (v := 7) (by decide)
      have hgE : E.color g = .bluish := by
        apply bluish_of_blue_loses_flipped_mate D hflip2 hgD hgh
        · simpa [SimpleGraph.adj_comm] using hkg
        · exact hgkV
        · exact hgh.ne
      have hjE : E.color j = .bluish := by
        apply bluish_of_untouched_bluish D hflip2 hjD
          (by simpa [SimpleGraph.adj_comm] using hkj)
        · exact hjkV
        · intro hjh
          rw [hjh] at hjD
          simp [hhD] at hjD
      have hdE : E.color d = .bluish := by
        have hdk : ¬ G.Adj d k := by
          apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
          · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
          · intro hci
            rw [← hci] at hi
            simp [hc] at hi
          · intro hei
            rw [← hei] at hi
            simp [he] at hi
          · exact hkc
          · exact hek.symm
          · intro hki
            rw [hki] at hck
            exact hic hck.symm
        apply bluish_of_untouched_bluish D hflip2 hdD hdk
        · exact hkd.symm
        · exact hv (u := (3 : Fin 8)) (v := 7) (by decide)
      have haE : E.color a = .reddish := by
        have hah : ¬ G.Adj a h := by
          simpa using nonedge 0 7 (by native_decide)
        apply reddish_of_untouched_reddish D hflip2 haD hah
        · intro hak
          rw [hak] at haD
          simp [hkD] at haD
        · exact hv (u := (0 : Fin 8)) (v := 7) (by decide)
      by_cases hblue : ∃ l, G.Adj f l ∧ E.color l = .blue
      · obtain ⟨l, hfl, hlE⟩ := hblue
        have hgf : G.Adj g f := hfg.symm
        have hgh' : G.Adj g h := hgh
        have hgl : ¬ G.Adj g l :=
          E.bluish_not_adj_blueSide hgE (Or.inl hlE)
        have hgk : ¬ G.Adj g k :=
          E.bluish_not_adj_blueSide hgE (Or.inl hkE)
        have hfh : ¬ G.Adj f h := by
          simpa using nonedge 5 7 (by native_decide)
        have hfk : ¬ G.Adj f k := by
          simpa [SimpleGraph.adj_comm] using
            C.reddish_not_adj_redSide hk (Or.inl hf)
        have hhl : ¬ G.Adj h l := by
          apply not_adj_fourth_neighbor_of_subcubic E.subcubic hih.symm hgh.symm hkh.symm
          · intro higV
            rw [higV] at hi
            simp [hg] at hi
          · exact hik
          · exact hgkV
          · intro hli
            rw [hli] at hlE
            simp [hiE] at hlE
          · intro hlg
            rw [hlg] at hlE
            simp [hgE] at hlE
          · intro hlk
            rw [hlk] at hfl
            exact hfk hfl
        by_cases hlk : G.Adj l k
        · have hptr := containsPositiveC E hfE hhE hlE hkE hgE
              hfl hfg hkh.symm hgh.symm hlk hfh hfk hhl
          exact HasReachableReduction.after_flip C hflip1
            (HasReachableReduction.after_flip D hflip2
              (HasReachableReduction.of_current_ptr E hptr))
        · have hceSwap := containsCutEnhancerB_of E.swapSides
              (by simp [hgE]) (by simp [hfE]) (by simp [hlE])
              (by simp [hhE]) (by simp [hkE]) hgf hgh' hfl hkh.symm
              hgl hgk hfh hfk (by simpa [SimpleGraph.adj_comm] using hhl) hlk
          have hceE : ContainsCutEnhancer E :=
            (containsInducedUpToSwap_swapSides IsCutEnhancer E).1 hceSwap
          exact HasReachableReduction.after_flip C hflip1
            (HasReachableReduction.after_flip D hflip2
              (HasReachableReduction.of_current_ce E hceE))
      · have heOther : ∀ z, G.Adj e z → z ≠ f →
            E.color z = .bluish := by
          intro z hez hzf
          have hz := C.neighbor_eq_of_three_neighbors (Or.inl he)
            hef hde.symm hej
            (hv (u := (5 : Fin 8)) (v := 3) (by decide))
            (by
              intro hfj
              rw [← hfj] at hj
              simp [hf] at hj)
            (by
              intro hdj
              rw [← hdj] at hj
              simp [hd] at hj) hez
          rcases hz with rfl | rfl | rfl
          · exact (hzf rfl).elim
          · exact hdE
          · exact hjE
        have hfOther : ∀ z, G.Adj f z → z ≠ e →
            E.color z = .bluish := by
          intro z hfz hze
          have hzSide := E.other_neighbor_of_red_is_blueSide
            hfE heE hef.symm hfz hze
          rcases hzSide with hz | hz
          · exact (hblue ⟨z, hfz, hz⟩).elim
          · exact hz
        have hptr := lemma4_4 E heE hfE hef heOther hfOther
        exact HasReachableReduction.after_flip C hflip1
          (HasReachableReduction.after_flip D hflip2
            (HasReachableReduction.of_current_ptr E hptr))
    · exact HasReachableReduction.after_flip C hflip1
        (HasReachableReduction.of_current_ce D hceD)
  · exact HasReachableReduction.of_current_ce C hce

end Subcubic
