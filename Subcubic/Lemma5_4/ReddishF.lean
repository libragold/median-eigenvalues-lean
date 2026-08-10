import Subcubic.Lemma5_4.RedF
import Subcubic.Lemma3_7

/-! Case 2.2.5 of Lemma 5.4. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem redSide_ne_bluish_5_4 {C : GoodColoring G} {x y : V}
    (hx : C.color x = .red ∨ C.color x = .reddish)
    (hy : C.color y = .bluish) : x ≠ y := by
  intro h
  subst y
  rcases hx with hx | hx <;> simp_all

private theorem blue_not_adj_bluish_5_4 (C : GoodColoring G) {x y : V}
    (hx : C.color x = .blue) (hy : C.color y = .bluish) :
    ¬ G.Adj x y := by
  simpa [SimpleGraph.adj_comm] using
    C.bluish_not_adj_blueSide hy (Or.inl hx)

private theorem saturated_a_not_adj
    (C : GoodColoring G) {a b w : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hwa : w ≠ b) (hwc : w ≠ Q.c) (hwd : w ≠ Q.d) :
    ¬ G.Adj a w :=
  C.not_adj_fourth_neighbor (Or.inl ha) hab Q.hac Q.had
    (vertex_ne_of_color_eq hb Q.hc (by decide))
    (vertex_ne_of_color_eq hb Q.hd (by decide)) Q.hcd
    hwa hwc hwd

private theorem saturated_b_not_adj
    (C : GoodColoring G) {a b w : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hwa : w ≠ a) (hwd : w ≠ Q.d) (hwe : w ≠ Q.e) :
    ¬ G.Adj b w :=
  C.not_adj_fourth_neighbor (Or.inl hb) hab.symm Q.hbd Q.hbe
    (vertex_ne_of_color_eq ha Q.hd (by decide))
    (vertex_ne_of_color_eq ha Q.he (by decide)) Q.hde
    hwa hwd hwe

/-- The `h` reddish alternative in Case 2.2.5. -/
private theorem reddish_second_neighbor_gives_H
    (C : GoodColoring G) {a b f g h : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hf : C.color f = .reddish) (hff : f = Q.f)
    (hg : C.color g = .blue) (hh : C.color h = .reddish)
    (hfg : G.Adj f g) (hgh : G.Adj g h) (hhf : h ≠ f) :
    HasReachableNegativeReduction C := by
  subst f
  have hga : ¬ G.Adj g a := by
    simpa [SimpleGraph.adj_comm] using saturated_a_not_adj C ha hb hab Q
      (vertex_ne_of_color_eq hg hb (by decide))
      (vertex_ne_of_color_eq hg Q.hc (by decide))
      (vertex_ne_of_color_eq hg Q.hd (by decide))
  have hgb : ¬ G.Adj g b := by
    simpa [SimpleGraph.adj_comm] using saturated_b_not_adj C ha hb hab Q
      (vertex_ne_of_color_eq hg ha (by decide))
      (vertex_ne_of_color_eq hg Q.hd (by decide))
      (vertex_ne_of_color_eq hg Q.he (by decide))
  have hgd := blue_not_adj_bluish_5_4 C hg Q.hd
  have hha : h ≠ a := vertex_ne_of_color_eq hh ha (by decide)
  have hhb : h ≠ b := vertex_ne_of_color_eq hh hb (by decide)
  have hdh : ¬ G.Adj Q.d h := by
    apply not_adj_fourth_neighbor_of_degree_three Q.hdDegree
      Q.had.symm Q.hbd.symm Q.hdf hab.ne Q.hfa.symm Q.hfb.symm
      hha hhb hhf
  have hntrSwap := containsNegativeH C.swapSides
    (a := g) (b := Q.d) (c := h) (d := Q.f) (e := a) (f := b)
    (by simp [hg]) (by simp [Q.hd]) (by simp [hh]) (by simp [hf])
    (by simp [ha]) (by simp [hb]) hgh hfg.symm Q.hdf
    Q.had.symm Q.hbd.symm hab hgd hga hgb hdh
    (by
      simp [hgh.ne, Q.hdf.ne, hab.ne,
        vertex_ne_of_color_eq hg Q.hd (by decide),
        vertex_ne_of_color_eq hg hf (by decide),
        vertex_ne_of_color_eq hg ha (by decide),
        vertex_ne_of_color_eq hg hb (by decide),
        (redSide_ne_bluish_5_4 (Or.inr hh) Q.hd).symm,
        Q.had.ne.symm, Q.hbd.ne.symm, Q.hfa, Q.hfb,
        hha, hhb, hhf])
  exact HasReachableNegativeReduction.of_current_ntr C
    ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap)

/-- Case 2.2.5.2: after flipping `gh`, the configuration is either the
no-blue case 2.2.2 or the red case 2.2.4. -/
private theorem flip_when_h_meets_neither
    (C : GoodColoring G) {a b g i h r : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hf : C.color Q.f = .reddish) (hg : C.color g = .blue)
    (hi : C.color i = .blue) (hh : C.color h = .red)
    (hr : C.color r = .red)
    (hfg : G.Adj Q.f g) (hgi : G.Adj g i)
    (hgh : G.Adj g h) (hhr : G.Adj h r)
    (hfc : ¬ G.Adj Q.f Q.c) (hfe : ¬ G.Adj Q.f Q.e)
    (hhc : ¬ G.Adj h Q.c) (hhe : ¬ G.Adj h Q.e) :
    HasReachableNegativeReduction C := by
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  rcases exists_flipAt_or_cutEnhancer C hh hg hr hi
      (degree_of_color (Or.inl hh)) (degree_of_color (Or.inr hg))
      hhr hgh.symm hgi with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hga : ¬ G.Adj g a := by
      simpa [SimpleGraph.adj_comm] using saturated_a_not_adj C ha hb hab Q
        (vertex_ne_of_color_eq hg hb (by decide))
        (vertex_ne_of_color_eq hg Q.hc (by decide))
        (vertex_ne_of_color_eq hg Q.hd (by decide))
    have hgb : ¬ G.Adj g b := by
      simpa [SimpleGraph.adj_comm] using saturated_b_not_adj C ha hb hab Q
        (vertex_ne_of_color_eq hg ha (by decide))
        (vertex_ne_of_color_eq hg Q.hd (by decide))
        (vertex_ne_of_color_eq hg Q.he (by decide))
    have hha : h ≠ a := by intro hEq; subst h; exact hga hgh
    have hhb : h ≠ b := by intro hEq; subst h; exact hgb hgh
    have hdh : ¬ G.Adj Q.d h := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hdDegree
        Q.had.symm Q.hbd.symm Q.hdf hab.ne Q.hfa.symm Q.hfb.symm
        hha hhb (vertex_ne_of_color_eq hh hf (by decide))
    have hfD : D.color Q.f = .red :=
      red_of_reddish_gains_flipped_blue C hflip hf hfg
        (vertex_ne_of_color_eq hf hh (by decide)) hfg.ne
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hha.symm (vertex_ne_of_color_eq ha hg (by decide))
        hhb.symm (vertex_ne_of_color_eq hb hg (by decide))
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hhb.symm (vertex_ne_of_color_eq hb hg (by decide))
        hha.symm (vertex_ne_of_color_eq ha hg (by decide))
    have hcD : D.color Q.c = .bluish :=
      bluish_of_untouched_bluish C hflip Q.hc
        (by simpa [SimpleGraph.adj_comm] using hhc)
        (redSide_ne_bluish_5_4 (Or.inl hh) Q.hc).symm
        (vertex_ne_of_color_eq Q.hc hg (by decide))
    have hdD : D.color Q.d = .bluish :=
      bluish_of_untouched_bluish C hflip Q.hd hdh
        (redSide_ne_bluish_5_4 (Or.inl hh) Q.hd).symm
        (vertex_ne_of_color_eq Q.hd hg (by decide))
    have heD : D.color Q.e = .bluish :=
      bluish_of_untouched_bluish C hflip Q.he
        (by simpa [SimpleGraph.adj_comm] using hhe)
        (redSide_ne_bluish_5_4 (Or.inl hh) Q.he).symm
        (vertex_ne_of_color_eq Q.he hg (by decide))
    let R : Lemma5_4SharedConfiguration D a b :=
      { c := Q.c, d := Q.d, e := Q.e, f := Q.f
        hc := hcD, hd := hdD, he := heD, hf := Or.inl hfD
        hac := Q.hac, had := Q.had, hbd := Q.hbd, hbe := Q.hbe
        hdf := Q.hdf, hcd := Q.hcd, hce := Q.hce, hde := Q.hde
        hfa := Q.hfa, hfb := Q.hfb, hdDegree := Q.hdDegree }
    apply HasReachableNegativeReduction.after_flip C hflip
    by_cases hblue : ∃ z, D.color z = .blue ∧ G.Adj Q.f z
    · obtain ⟨z, hz, hfz⟩ := hblue
      exact lemma5_4_red_f_blue_neighbor D haD hbD hab R hfD hz hfz
    · apply HasReachableNegativeReduction.of_current_ntr D
      have hfDDegree : vertexDegree G Q.f = 3 := by
        rcases lemma3_6_negative D (Or.inl hfD) with hdegree | hntr | hce
        · exact hdegree
        · exact (hdone (HasReachableNegativeReduction.after_flip C hflip
            (.of_current_ntr D hntr))).elim
        · exact (hdone (HasReachableNegativeReduction.after_flip C hflip
            (.of_current_ce D hce))).elim
      apply lemma5_4_noBlue_meets_neither D haD hbD hab R
        (fun _ ↦ hfDDegree)
        (by simpa [R] using hfc) (by simpa [R] using hfe)
      intro z hfz hz
      exact hblue ⟨z, hz, hfz⟩
  · exact HasReachableNegativeReduction.of_current_ce C hce

/-- Case 2.2.5.3, oriented by `h-e`. -/
private theorem hard_oriented
    (C : GoodColoring G) {a b g i h r : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hf : C.color Q.f = .reddish) (hg : C.color g = .blue)
    (hi : C.color i = .blue) (hh : C.color h = .red)
    (hr : C.color r = .red)
    (hfg : G.Adj Q.f g) (hgi : G.Adj g i)
    (hgh : G.Adj g h) (hhr : G.Adj h r)
    (hfc : ¬ G.Adj Q.f Q.c) (hfe : ¬ G.Adj Q.f Q.e)
    (hhe : G.Adj h Q.e) : HasReachableNegativeReduction C := by
  have hga : ¬ G.Adj g a := by
    simpa [SimpleGraph.adj_comm] using saturated_a_not_adj C ha hb hab Q
      (vertex_ne_of_color_eq hg hb (by decide))
      (vertex_ne_of_color_eq hg Q.hc (by decide))
      (vertex_ne_of_color_eq hg Q.hd (by decide))
  have hgb : ¬ G.Adj g b := by
    simpa [SimpleGraph.adj_comm] using saturated_b_not_adj C ha hb hab Q
      (vertex_ne_of_color_eq hg ha (by decide))
      (vertex_ne_of_color_eq hg Q.hd (by decide))
      (vertex_ne_of_color_eq hg Q.he (by decide))
  have hgiV : g ≠ i := hgi.ne
  have hgeV : g ≠ Q.e := vertex_ne_of_color_eq hg Q.he (by decide)
  have hreV : r ≠ Q.e := redSide_ne_bluish_5_4 (Or.inl hr) Q.he
  have hrg : r ≠ g := vertex_ne_of_color_eq hr hg (by decide)
  have nonadj_h (w : V) (hwr : w ≠ r) (hwg : w ≠ g)
      (hwe : w ≠ Q.e) : ¬ G.Adj h w :=
    C.not_adj_fourth_neighbor (Or.inl hh) hhr hgh.symm hhe
      hrg hreV hgeV hwr hwg hwe
  rcases lemma3_7 C hh hg hf hgh.symm hfg.symm with hfdeg | hce
  · by_cases hfi : G.Adj Q.f i
    · have hbf : ¬ G.Adj b Q.f := by
        exact fun h => C.reddish_not_adj_redSide hf (Or.inl hb) h.symm
      have hbi : ¬ G.Adj b i := saturated_b_not_adj C ha hb hab Q
        (vertex_ne_of_color_eq hi ha (by decide))
        (vertex_ne_of_color_eq hi Q.hd (by decide))
        (vertex_ne_of_color_eq hi Q.he (by decide))
      have hbg : ¬ G.Adj b g := by
        simpa [SimpleGraph.adj_comm] using hgb
      have hntr := containsNegativeH C
        (a := b) (b := Q.f) (c := Q.e) (d := Q.d) (e := g) (f := i)
        hb hf Q.he Q.hd hg hi Q.hbe Q.hbd Q.hdf.symm hfg hfi hgi
        hbf hbg hbi hfe
        (by
          simp [Q.hbe.ne, Q.hbd.ne, hfg.ne, hfi.ne,
            vertex_ne_of_color_eq hb hg (by decide),
            vertex_ne_of_color_eq hb hi (by decide),
            redSide_ne_bluish_5_4 (Or.inr hf) Q.he,
            redSide_ne_bluish_5_4 (Or.inr hf) Q.hd,
            vertex_ne_of_color_eq Q.he hg (by decide),
            vertex_ne_of_color_eq Q.he hi (by decide),
            vertex_ne_of_color_eq Q.hd hg (by decide),
            vertex_ne_of_color_eq Q.hd hi (by decide), hgi.ne,
            Q.hfb.symm, Q.hde.symm])
      exact HasReachableNegativeReduction.of_current_ntr C hntr
    · obtain ⟨j, hfj, hjd, hjg⟩ :=
        exists_third_neighbor_of_degree_three hfdeg
          (vertex_ne_of_color_eq Q.hd hg (by decide))
      have hji : j ≠ i := by
        intro hEq
        subst j
        exact hfi hfj
      have hjSide : C.color j = .blue ∨ C.color j = .bluish := by
        cases hj : C.color j with
        | red => exact (C.reddish_not_adj_redSide hf (Or.inl hj) hfj).elim
        | reddish => exact (C.reddish_not_adj_redSide hf (Or.inr hj) hfj).elim
        | blue => exact Or.inl rfl
        | bluish => exact Or.inr rfl
      have hjb : j ≠ b := by
        intro hEq
        subst j
        rcases hjSide with hj | hj <;> simp_all
      have haj : ¬ G.Adj a j := saturated_a_not_adj C ha hb hab Q hjb
        (by intro hEq; subst j; exact hfc hfj)
        hjd
      have hai : ¬ G.Adj a i := saturated_a_not_adj C ha hb hab Q
        (vertex_ne_of_color_eq hi hb (by decide))
        (vertex_ne_of_color_eq hi Q.hc (by decide))
        (vertex_ne_of_color_eq hi Q.hd (by decide))
      have hae : ¬ G.Adj a Q.e := saturated_a_not_adj C ha hb hab Q
        (vertex_ne_of_color_eq Q.he hb (by decide)) Q.hce.symm Q.hde.symm
      have hhbV : h ≠ b := by
        intro hEq
        subst h
        exact hgb hgh
      have hah : ¬ G.Adj a h :=
        saturated_a_not_adj C ha hb hab Q hhbV
          (vertex_ne_of_color_eq hh Q.hc (by decide))
          (vertex_ne_of_color_eq hh Q.hd (by decide))
      have hhf : ¬ G.Adj h Q.f := by
        simpa [SimpleGraph.adj_comm] using
          C.reddish_not_adj_redSide hf (Or.inl hh)
      have hhc : ¬ G.Adj h Q.c := nonadj_h Q.c
        (redSide_ne_bluish_5_4 (Or.inl hr) Q.hc).symm
        (vertex_ne_of_color_eq Q.hc hg (by decide)) Q.hce
      have hhd : ¬ G.Adj h Q.d := nonadj_h Q.d
        (redSide_ne_bluish_5_4 (Or.inl hr) Q.hd).symm
        (vertex_ne_of_color_eq Q.hd hg (by decide)) Q.hde
      have hhi : ¬ G.Adj h i := nonadj_h i
        (vertex_ne_of_color_eq hi hr (by decide)) hgiV.symm
        (vertex_ne_of_color_eq hi Q.he (by decide))
      rcases hjSide with hj | hj
      · have hgj : ¬ G.Adj g j := by
          exact C.blueSide_not_adj_second_neighbor
            (by simp [hg]) (by simp [hi]) (by simp [hj]) hgi hji.symm
        by_cases hhjAdj : G.Adj h j
        · exact HasReachableNegativeReduction.of_current_ce C
            (containsCutEnhancerA_of C hh hg hj hgh.symm hhjAdj
              hjg.symm hgj)
        · have hjdNon := blue_not_adj_bluish_5_4 C hj Q.hd
          have hjeNon := blue_not_adj_bluish_5_4 C hj Q.he
          have hgdNon := blue_not_adj_bluish_5_4 C hg Q.hd
          have hgeNon := blue_not_adj_bluish_5_4 C hg Q.he
          have hdeNon := C.bluish_not_adj_blueSide Q.hd (Or.inr Q.he)
          have hjbNon : ¬ G.Adj j b := by
            simpa [SimpleGraph.adj_comm] using saturated_b_not_adj C ha hb hab Q
              (vertex_ne_of_color_eq hj ha (by decide))
              (vertex_ne_of_color_eq hj Q.hd (by decide))
              (vertex_ne_of_color_eq hj Q.he (by decide))
          have hhbNon : ¬ G.Adj h b := by
            simpa [SimpleGraph.adj_comm] using saturated_b_not_adj C ha hb hab Q
              (by intro hEq; subst h; exact hga hgh)
              (vertex_ne_of_color_eq hh Q.hd (by decide))
              (vertex_ne_of_color_eq hh Q.he (by decide))
          have hceSwap := containsCutEnhancerE_of C.swapSides
            (a := j) (b := Q.d) (c := g) (d := Q.e)
            (e := Q.f) (f := h) (g := b)
            (by simp [hj]) (by simp [Q.hd]) (by simp [hg])
            (by simp [Q.he]) (by simp [hf]) (by simp [hh]) (by simp [hb])
            hfj.symm Q.hdf Q.hbd.symm hfg.symm hgh hhe.symm Q.hbe.symm
            hjdNon (by simpa [SimpleGraph.adj_comm] using hgj)
            (by simpa [SimpleGraph.adj_comm] using hjeNon)
            (by simpa [SimpleGraph.adj_comm] using hhjAdj) hjbNon
            (by simpa [SimpleGraph.adj_comm] using hgdNon)
            hdeNon (by simpa [SimpleGraph.adj_comm] using hhd)
            hgeNon hgb (by simpa [SimpleGraph.adj_comm] using hfe)
            (by simpa [SimpleGraph.adj_comm] using hhf)
            (C.reddish_not_adj_redSide hf (Or.inl hb)) hhbNon
            (by
              simp [hjg, Q.hde,
                vertex_ne_of_color_eq hj Q.hd (by decide),
                vertex_ne_of_color_eq hj Q.he (by decide),
                vertex_ne_of_color_eq hj hf (by decide),
                vertex_ne_of_color_eq hj hh (by decide),
                vertex_ne_of_color_eq hj hb (by decide),
                vertex_ne_of_color_eq Q.hd hg (by decide),
                (redSide_ne_bluish_5_4 (Or.inr hf) Q.hd).symm,
                (redSide_ne_bluish_5_4 (Or.inl hh) Q.hd).symm,
                (redSide_ne_bluish_5_4 (Or.inl hb) Q.hd).symm,
                vertex_ne_of_color_eq hg Q.he (by decide),
                vertex_ne_of_color_eq hg hf (by decide),
                vertex_ne_of_color_eq hg hh (by decide),
                vertex_ne_of_color_eq hg hb (by decide),
                (redSide_ne_bluish_5_4 (Or.inr hf) Q.he).symm,
                (redSide_ne_bluish_5_4 (Or.inl hh) Q.he).symm,
                (redSide_ne_bluish_5_4 (Or.inl hb) Q.he).symm,
                vertex_ne_of_color_eq hf hh (by decide), Q.hfb,
                hhbV])
          exact HasReachableNegativeReduction.of_current_ce C
            ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
      · have hhj : ¬ G.Adj h j := nonadj_h j
          (redSide_ne_bluish_5_4 (Or.inl hr) hj).symm
          (vertex_ne_of_color_eq hj hg (by decide))
          (by intro hEq; subst j; exact hfe hfj)
        have hhaV : h ≠ a := by
          intro hEq
          subst h
          exact hga hgh
        have hcj : Q.c ≠ j := by
          intro hEq
          subst j
          exact hfc hfj
        have hje : j ≠ Q.e := by
          intro hEq
          subst j
          exact hfe hfj
        have hntr := containsNegativeZ C ha hf hh Q.hc Q.hd hj hg hi Q.he
          Q.hac Q.had Q.hdf.symm hfj hfg hgh.symm hhe hgi
          (by simpa [SimpleGraph.adj_comm] using
            C.reddish_not_adj_redSide hf (Or.inl ha))
          hah haj hai hae (by simpa [SimpleGraph.adj_comm] using hhf)
          hfc hfi hfe hhc hhd hhj hhi
          (by
            simp [Q.hac.ne, Q.had.ne, hfj.ne, hfg.ne,
              hhe.ne, Q.hcd, Q.hce, Q.hde,
              Q.hfa.symm, hhaV.symm,
              vertex_ne_of_color_eq ha hj (by decide),
              vertex_ne_of_color_eq ha hg (by decide),
              vertex_ne_of_color_eq ha hi (by decide),
              redSide_ne_bluish_5_4 (Or.inr hf) Q.hc,
              redSide_ne_bluish_5_4 (Or.inr hf) Q.hd,
              vertex_ne_of_color_eq hf hh (by decide),
              vertex_ne_of_color_eq hf hi (by decide),
              redSide_ne_bluish_5_4 (Or.inl hh) Q.hc,
              redSide_ne_bluish_5_4 (Or.inl hh) Q.hd,
              redSide_ne_bluish_5_4 (Or.inl hh) hj,
              vertex_ne_of_color_eq hh hg (by decide),
              vertex_ne_of_color_eq hh hi (by decide),
              hcj, hjd.symm, hje,
              vertex_ne_of_color_eq Q.hc hg (by decide),
              vertex_ne_of_color_eq Q.hc hi (by decide),
              vertex_ne_of_color_eq Q.hd hg (by decide),
              vertex_ne_of_color_eq Q.hd hi (by decide),
              vertex_ne_of_color_eq hj hg (by decide),
              vertex_ne_of_color_eq hj hi (by decide), hgi.ne,
              redSide_ne_bluish_5_4 (Or.inl ha) Q.he,
              redSide_ne_bluish_5_4 (Or.inr hf) Q.he,
              vertex_ne_of_color_eq hg Q.he (by decide),
              vertex_ne_of_color_eq hi Q.he (by decide)])
        exact HasReachableNegativeReduction.of_current_ntr C hntr
  · exact HasReachableNegativeReduction.of_lemma3_6 C hce

/-- Case 2.2.5. -/
theorem lemma5_4_reddish_f_blue_neighbor
    (C : GoodColoring G) {a b g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hf : C.color Q.f = .reddish) (hg : C.color g = .blue)
    (hfg : G.Adj Q.f g)
    (hfc : ¬ G.Adj Q.f Q.c) (hfe : ¬ G.Adj Q.f Q.e) :
    HasReachableNegativeReduction C := by
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  have hgCorrect := C.color_correct g
  rw [hg] at hgCorrect
  obtain ⟨_, i, hiSide, hgi⟩ := hgCorrect
  have hiCases := (C.not_mem_redSide_iff i).1 hiSide
  have hi : C.color i = .blue := by
    rcases hiCases with hi | hi
    · exact hi
    · exact (C.bluish_not_adj_blueSide hi (Or.inl hg) hgi.symm).elim
  have hif : i ≠ Q.f := vertex_ne_of_color_eq hi hf (by decide)
  obtain ⟨h, hgh, hhi, hhf⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inr hg)) hif
  have hhSide := C.other_neighbor_of_blue_is_redSide hg hi hgi hgh hhi
  have hhCases : C.color h = .reddish ∨ C.color h = .red :=
    hhSide.elim Or.inr Or.inl
  rcases hhCases with hh | hh
  · exact reddish_second_neighbor_gives_H C ha hb hab Q hf rfl
      hg hh hfg hgh hhf
  · have hhCorrect := C.color_correct h
    rw [hh] at hhCorrect
    obtain ⟨_, r, hrSide, hhr⟩ := hhCorrect
    have hrCases := (C.mem_redSide_iff r).1 hrSide
    have hr : C.color r = .red := by
      rcases hrCases with hr | hr
      · exact hr
      · exact (C.reddish_not_adj_redSide hr (Or.inl hh) hhr.symm).elim
    by_cases hhe : G.Adj h Q.e
    · exact hard_oriented C ha hb hab Q hf hg hi hh hr
        hfg hgi hgh hhr hfc hfe hhe
    · by_cases hhc : G.Adj h Q.c
      · exact hard_oriented C hb ha hab.symm Q.reverse hf hg hi hh hr
          hfg hgi hgh hhr hfe hfc hhc
      · exact flip_when_h_meets_neither C ha hb hab Q hf hg hi hh hr
          hfg hgi hgh hhr hfc hfe hhc hhe

end Subcubic
