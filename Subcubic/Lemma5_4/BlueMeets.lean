import Subcubic.Lemma5_4.NoBlue

/-! Case 2.2.3 of Lemma 5.4. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem redSide_ne_bluish' {C : GoodColoring G} {x y : V}
    (hx : C.color x = .red ∨ C.color x = .reddish)
    (hy : C.color y = .bluish) : x ≠ y := by
  intro h; subst y; rcases hx with hx | hx <;> simp_all

/-- If the third neighbor meets an exclusive bluish neighbor and also has a
blue neighbor, subcubicity forces it to be reddish. -/
private theorem f_reddish_of_meets_e_and_blue
    (C : GoodColoring G) {a b g : V}
    (Q : Lemma5_4SharedConfiguration C a b)
    (hfe : G.Adj Q.f Q.e) (hg : C.color g = .blue)
    (hfg : G.Adj Q.f g) : C.color Q.f = .reddish := by
  rcases Q.hf with hf | hf
  · have hfCorrect := C.color_correct Q.f
    rw [hf] at hfCorrect
    obtain ⟨_, r, hrSide, hfr⟩ := hfCorrect
    have hrCases := (C.mem_redSide_iff r).1 hrSide
    have hr : C.color r = .red := by
      rcases hrCases with hr | hr
      · exact hr
      · exact (C.reddish_not_adj_redSide hr (Or.inl hf) hfr.symm).elim
    have hde := Q.hde
    have hdg : Q.d ≠ g := vertex_ne_of_color_eq Q.hd hg (by decide)
    have heg : Q.e ≠ g := vertex_ne_of_color_eq Q.he hg (by decide)
    have hrd : r ≠ Q.d := redSide_ne_bluish' (Or.inl hr) Q.hd
    have hre : r ≠ Q.e := redSide_ne_bluish' (Or.inl hr) Q.he
    have hrg : r ≠ g := vertex_ne_of_color_eq hr hg (by decide)
    exact (not_adj_fourth_neighbor_of_subcubic C.subcubic
      Q.hdf.symm hfe hfg hde hdg heg hrd hre hrg hfr).elim
  · exact hf

/-- Case 2.2.3, oriented by `f-e`. -/
theorem lemma5_4_blue_meets_e
    (C : GoodColoring G) {a b g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hfe : G.Adj Q.f Q.e) (hg : C.color g = .blue)
    (hfg : G.Adj Q.f g) : HasReachableNegativeReduction C := by
  have hf := f_reddish_of_meets_e_and_blue C Q hfe hg hfg
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
    C.exists_third_neighbor (Or.inr hg) hif
  have hhSide := C.other_neighbor_of_blue_is_redSide hg hi hgi hgh hhi
  have hgd : ¬ G.Adj g Q.d := by
    simpa [SimpleGraph.adj_comm] using
      C.bluish_not_adj_blueSide Q.hd (Or.inl hg)
  have hge : ¬ G.Adj g Q.e := by
    simpa [SimpleGraph.adj_comm] using
      C.bluish_not_adj_blueSide Q.he (Or.inl hg)
  have hga : ¬ G.Adj g a := by
    simpa [SimpleGraph.adj_comm] using
      C.not_adj_fourth_neighbor (Or.inl ha) hab Q.hac Q.had
        (vertex_ne_of_color_eq hb Q.hc (by decide))
        (vertex_ne_of_color_eq hb Q.hd (by decide)) Q.hcd
        (vertex_ne_of_color_eq hg hb (by decide))
        (vertex_ne_of_color_eq hg Q.hc (by decide))
        (vertex_ne_of_color_eq hg Q.hd (by decide))
  have hgb : ¬ G.Adj g b := by
    simpa [SimpleGraph.adj_comm] using
      C.not_adj_fourth_neighbor (Or.inl hb) hab.symm Q.hbd Q.hbe
        (vertex_ne_of_color_eq ha Q.hd (by decide))
        (vertex_ne_of_color_eq ha Q.he (by decide)) Q.hde
        (vertex_ne_of_color_eq hg ha (by decide))
        (vertex_ne_of_color_eq hg Q.hd (by decide))
        (vertex_ne_of_color_eq hg Q.he (by decide))
  have hhSide' : C.color h = .reddish ∨ C.color h = .red :=
    hhSide.elim Or.inr Or.inl
  rcases hhSide' with hh | hh
  · have hha : h ≠ a := by
      intro hEq
      subst h
      exact hga hgh
    have hhb : h ≠ b := by
      intro hEq
      subst h
      exact hgb hgh
    have hdh : ¬ G.Adj Q.d h := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hdDegree
        Q.had.symm Q.hbd.symm Q.hdf
        hab.ne Q.hfa.symm Q.hfb.symm hha hhb hhf
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
          (redSide_ne_bluish' (Or.inr hh) Q.hd).symm,
          Q.had.ne.symm, Q.hbd.ne.symm, Q.hfa, Q.hfb,
          hha, hhb, hhf])
    exact HasReachableNegativeReduction.of_current_ntr C
      ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap)
  · by_cases hhe : G.Adj h Q.e
    · have hhfAdj : ¬ G.Adj h Q.f := by
        simpa [SimpleGraph.adj_comm] using
          C.reddish_not_adj_redSide hf (Or.inl hh)
      have hhbAdj : ¬ G.Adj h b := by
        simpa [SimpleGraph.adj_comm] using
          C.redSide_not_adj_second_neighbor
            ((C.mem_redSide_iff b).2 (Or.inl hb))
            ((C.mem_redSide_iff a).2 (Or.inl ha))
            ((C.mem_redSide_iff h).2 (Or.inl hh)) hab.symm
            (by
              intro hEq
              subst h
              exact hga hgh)
      have hfbAdj : ¬ G.Adj Q.f b := by
        exact C.reddish_not_adj_redSide hf (Or.inl hb)
      exact HasReachableNegativeReduction.of_current_ce C
        (containsCutEnhancerD_of C hh hf hg Q.he hb hgh.symm hhe
          hfg hfe Q.hbe.symm hhfAdj hhbAdj hfbAdj hge hgb
          (by
            intro hEq
            apply hgb
            simpa [hEq] using hgh))
    · have hha : h ≠ a := by
        intro hEq
        subst h
        exact hga hgh
      have hhb : h ≠ b := by
        intro hEq
        subst h
        exact hgb hgh
      have hdh : ¬ G.Adj Q.d h := by
        apply not_adj_fourth_neighbor_of_degree_three Q.hdDegree
          Q.had.symm Q.hbd.symm Q.hdf
          hab.ne Q.hfa.symm Q.hfb.symm hha hhb
          (vertex_ne_of_color_eq hh hf (by decide))
      have hhCorrect := C.color_correct h
      rw [hh] at hhCorrect
      obtain ⟨_, r, hrSide, hhr⟩ := hhCorrect
      have hrCases := (C.mem_redSide_iff r).1 hrSide
      have hr : C.color r = .red := by
        rcases hrCases with hr | hr
        · exact hr
        · exact (C.reddish_not_adj_redSide hr (Or.inl hh) hhr.symm).elim
      rcases exists_flipAt_or_cutEnhancer C hh hg hr hi hhr hgh.symm hgi with
        hflip | hce
      · obtain ⟨M, hflip⟩ := hflip
        let D := M.toGoodColoring
        have hfh : Q.f ≠ h := vertex_ne_of_color_eq hf hh (by decide)
        have hfgV : Q.f ≠ g := hfg.ne
        have hfD : D.color Q.f = .red :=
          red_of_reddish_gains_flipped_blue C hflip hf hfg hfh hfgV
        have hbD : D.color b = .red :=
          red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
            hhb.symm (vertex_ne_of_color_eq hb hg (by decide))
            hha.symm (vertex_ne_of_color_eq ha hg (by decide))
        have hdD : D.color Q.d = .bluish :=
          bluish_of_untouched_bluish C hflip Q.hd hdh
            (redSide_ne_bluish' (Or.inl hh) Q.hd).symm
            (vertex_ne_of_color_eq Q.hd hg (by decide))
        have heD : D.color Q.e = .bluish :=
          bluish_of_untouched_bluish C hflip Q.he
            (by simpa [SimpleGraph.adj_comm] using hhe)
            (redSide_ne_bluish' (Or.inl hh) Q.he).symm
            (vertex_ne_of_color_eq Q.he hg (by decide))
        have hbf : ¬ G.Adj b Q.f := by
          simpa [SimpleGraph.adj_comm] using
            C.reddish_not_adj_redSide hf (Or.inl hb)
        apply HasReachableNegativeReduction.after_flip C hflip
        apply HasReachableNegativeReduction.of_current_ntr D
        apply containsNegativeB D hbD hfD hdD heD
          Q.hbd Q.hbe Q.hdf.symm hfe hbf
        simp [Q.hbd.ne, Q.hbe.ne, hfe.ne, Q.hde,
          vertex_ne_of_color_eq hb hf (by decide),
          redSide_ne_bluish' (Or.inr hf) Q.hd]
      · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
