import Subcubic.Lemma4_8.SetupK

/-! Case (3.4.1) of Lemma 4.8. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_case_k_adj_j
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8KConfiguration C a b c d e f g h)
    (hkj : G.Adj Q.k Q.j) : HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  rcases Q with ⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, k, hk, hck, hkb, hkd, hkg, hkdeg⟩
  change G.Adj k j at hkj
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
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have heg : ¬ G.Adj g e := by
    simpa using nonedge 6 4 (by native_decide)
  have hek : e ≠ k := by
    intro hek
    rw [← hek] at hk
    simp [he] at hk
  have hak : a ≠ k := by
    intro hak
    rw [← hak] at hk
    simp [ha] at hk
  have hfk : f ≠ k := by
    intro hfk
    rw [← hfk] at hk
    simp [hf] at hk
  have hkgV : k ≠ g := by
    intro hkgV
    rw [hkgV] at hk
    simp [hg] at hk
  have hjfV : j ≠ f := by
    intro hjfV
    rw [hjfV] at hj
    simp [hf] at hj
  have hjgV : j ≠ g := by
    intro hjgV
    rw [hjgV] at hj
    simp [hg] at hj
  rcases exists_flipAt_or_cutEnhancer C hf hg he hh
      (degree_of_color (Or.inl hf)) (degree_of_color (Or.inr hg))
      hef.symm hfg hgh
      with hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hjf : ¬ G.Adj j f := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        hej.symm hja hkj.symm
      · exact hv (u := (4 : Fin 8)) (v := 0) (by decide)
      · exact hek
      · exact hak
      · exact hef.ne.symm
      · exact hv (u := (5 : Fin 8)) (v := 0) (by decide)
      · exact hfk
    have haD : D.color a = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
      · exact hv (u := (0 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (0 : Fin 8)) (v := 6) (by decide)
      · exact hv (u := (1 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (1 : Fin 8)) (v := 6) (by decide)
    have hbD : D.color b = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
      · exact hv (u := (1 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (1 : Fin 8)) (v := 6) (by decide)
      · exact hv (u := (0 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (0 : Fin 8)) (v := 6) (by decide)
    have hcD : D.color c = .blue := by
      apply blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
      · exact hv (u := (2 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (2 : Fin 8)) (v := 6) (by decide)
      · exact hv (u := (3 : Fin 8)) (v := 5) (by decide)
      · exact hv (u := (3 : Fin 8)) (v := 6) (by decide)
    have heD : D.color e = .reddish := by
      apply reddish_of_red_loses_flipped_mate C hflip he hef
      · exact fun h => heg h.symm
      · exact hef.ne
      · exact hv (u := (4 : Fin 8)) (v := 6) (by decide)
    have hkD : D.color k = .reddish := by
      apply reddish_of_untouched_reddish C hflip hk
      · exact hkg
      · exact hfk.symm
      · exact hkgV
    have hjD : D.color j = .bluish := by
      apply bluish_of_untouched_bluish C hflip hj hjf
      · exact hjfV
      · exact hjgV
    have hjc : ¬ G.Adj j c :=
      C.bluish_not_adj_blueSide hj (Or.inl hc)
    have hce : ¬ G.Adj c e := by
      simpa using nonedge 2 4 (by native_decide)
    have hca : ¬ G.Adj c a := by
      simpa using nonedge 2 0 (by native_decide)
    have hjcV : j ≠ c := by
      intro hjcV
      rw [hjcV] at hj
      simp [hc] at hj
    have hjeV : j ≠ e := hej.ne.symm
    have hjkV : j ≠ k := hkj.ne.symm
    have hjaV : j ≠ a := hja.ne
    have hjbV : j ≠ b := by
      intro hjbV
      rw [hjbV] at hj
      simp [hb] at hj
    have hckV : c ≠ k := by
      intro hckV
      rw [← hckV] at hk
      simp [hc] at hk
    have hcaV : c ≠ a := hv (u := (2 : Fin 8)) (v := 0) (by decide)
    have hcbV : c ≠ b := hbc.ne.symm
    have hceV : c ≠ e := hv (u := (2 : Fin 8)) (v := 4) (by decide)
    have heaV : e ≠ a := hv (u := (4 : Fin 8)) (v := 0) (by decide)
    have hebV : e ≠ b := hv (u := (4 : Fin 8)) (v := 1) (by decide)
    have hn : [j, c, e, k, a, b].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, not_false_eq_true, and_true]
      exact ⟨⟨hjcV, hjeV, hjkV, hjaV, hjbV⟩,
        ⟨hceV, hckV, hcaV, hcbV⟩,
        ⟨hek, heaV, hebV⟩, ⟨hak.symm, hkb⟩, hab.ne⟩
    have hptrSwap : ContainsPositiveTailReducer D.swapSides :=
      containsPositiveM D.swapSides (a := j) (b := c) (c := e)
        (d := k) (e := a) (f := b)
        (by simp [hjD]) (by simp [hcD]) (by simp [heD]) (by simp [hkD])
        (by simp [haD]) (by simp [hbD])
        hej.symm hkj.symm hja hck hbc.symm hab hjc hjb hce hca hn
    have hptr : ContainsPositiveTailReducer D :=
      (containsInducedUpToSwap_swapSides IsPositiveTailReducer D).1 hptrSwap
    exact HasReachableReduction.after_flip C hflip
      (HasReachableReduction.of_current_ptr D hptr)
  · exact HasReachableReduction.of_current_ce C hce

end Subcubic
