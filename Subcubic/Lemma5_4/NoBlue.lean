import Subcubic.Lemma5_4.Basic

/-! Cases 2.2.1 and 2.2.2 of Lemma 5.4. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem redSide_ne_bluish {C : MatchingCutColoring G} {x y : V}
    (hx : C.color x = .red ∨ C.color x = .reddish)
    (hy : C.color y = .bluish) : x ≠ y := by
  intro h
  subst y
  rcases hx with hx | hx <;> simp_all

private theorem no_blue_neighbor_is_bluish
    (C : MatchingCutColoring G) {f g : V}
    (hf : C.color f = .reddish) (hfg : G.Adj f g)
    (hnoBlue : ∀ v, G.Adj f v → C.color v ≠ .blue) :
    C.color g = .bluish := by
  cases hg : C.color g with
  | red => exact (C.reddish_not_adj_redSide hf (Or.inl hg) hfg).elim
  | reddish => exact (C.reddish_not_adj_redSide hf (Or.inr hg) hfg).elim
  | blue => exact (hnoBlue g hfg hg).elim
  | bluish => exact rfl

/-- Case 2.2.1, oriented so that the third neighbor `f` meets `e`.
The reducers `ntr-dc-b` and `ntr-b` are exactly the degree-two reddish and
red alternatives. -/
theorem lemma5_4_noBlue_meets_e
    (C : MatchingCutColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hfe : G.Adj Q.f Q.e)
    (hnoBlue : ∀ v, G.Adj Q.f v → C.color v ≠ .blue) :
    ContainsNegativeTailReducer C := by
  have hfd : Q.f ≠ Q.d := Q.hdf.ne.symm
  have hfc : Q.f ≠ Q.c := redSide_ne_bluish Q.hf Q.hc
  have hfeV : Q.f ≠ Q.e := hfe.ne
  have hbf : ¬ G.Adj b Q.f := by
    rcases Q.hf with hf | hf
    · exact C.redSide_not_adj_second_neighbor
        (by simp [hb]) (by simp [ha]) (by simp [hf]) hab.symm
        Q.hfa.symm
    · exact fun h => C.reddish_not_adj_redSide hf (Or.inl hb) h.symm
  rcases Q.hf with hf | hf
  · apply containsNegativeB C hb hf Q.hd Q.he
      Q.hbd Q.hbe Q.hdf.symm hfe hbf
    simp [Q.hbd.ne, Q.hbe.ne, hfd, hfeV, Q.hde,
      Q.hfb.symm]
  · have lower : 2 ≤ vertexDegree G Q.f := by
      have hs : ({Q.d, Q.e} : Set V) ⊆ G.neighborSet Q.f := by
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact Q.hdf.symm
        · exact hfe
      unfold vertexDegree
      simpa [Q.hde] using Set.ncard_le_ncard hs
    by_cases hfdeg2 : vertexDegree G Q.f = 2
    · apply containsNegativeDcB C hb hf Q.hd Q.he hfdeg2
        Q.hbd Q.hbe Q.hdf.symm hfe hbf
      simp [Q.hbd.ne, Q.hbe.ne, hfd, hfeV, Q.hde,
        Q.hfb.symm]
    · have hfdeg3 : vertexDegree G Q.f = 3 := by
        have upper := C.subcubic Q.f
        omega
      obtain ⟨g, hfg, hgd, hge⟩ :=
        exists_third_neighbor_of_degree_three hfdeg3 Q.hde
      have hg := no_blue_neighbor_is_bluish C hf hfg hnoBlue
      have hbg : ¬ G.Adj b g := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic
          hab.symm Q.hbd Q.hbe
        · exact redSide_ne_bluish (Or.inl ha) Q.hd
        · exact redSide_ne_bluish (Or.inl ha) Q.he
        · exact Q.hde
        · exact vertex_ne_of_color_eq hg ha (by decide)
        · exact hgd
        · exact hge
      apply containsNegativeE C hb hf Q.hd Q.he hg
        Q.hbd Q.hbe Q.hdf.symm hfe hfg hbf hbg
      simp [Q.hbd.ne, Q.hbe.ne, hfd, hfeV, Q.hde,
        redSide_ne_bluish (Or.inl hb) hg,
        Q.hfb.symm, hfg.ne, hgd.symm, hge.symm]

/-- Case 2.2.2: `f` meets neither exclusive bluish neighbor.  Its number of
displayed bluish neighbors selects `s-`, `sx-minus-`, or `sx-minus2-`. -/
theorem lemma5_4_noBlue_meets_neither
    (C : MatchingCutColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hfDegree : C.color Q.f = .red → vertexDegree G Q.f = 3)
    (hfc : ¬ G.Adj Q.f Q.c) (hfe : ¬ G.Adj Q.f Q.e)
    (hnoBlue : ∀ v, G.Adj Q.f v → C.color v ≠ .blue) :
    ContainsNegativeTailReducer C := by
  have hfd : Q.f ≠ Q.d := Q.hdf.ne.symm
  have hfcV : Q.f ≠ Q.c := redSide_ne_bluish Q.hf Q.hc
  have hfeV : Q.f ≠ Q.e := redSide_ne_bluish Q.hf Q.he
  rcases Q.hf with hf | hf
  · have hfCorrect := C.color_correct Q.f
    rw [hf] at hfCorrect
    obtain ⟨_, r, hrSide, hfr⟩ := hfCorrect
    have hrCases := (C.mem_redSide_iff r).1 hrSide
    have hr : C.color r = .red := by
      rcases hrCases with hr | hr
      · exact hr
      · exact (C.reddish_not_adj_redSide hr (Or.inl hf) hfr.symm).elim
    have hdr : Q.d ≠ r := redSide_ne_bluish (Or.inl hr) Q.hd |>.symm
    obtain ⟨g, hfg, hgd, hgr⟩ :=
      C.exists_third_neighbor (hfDegree hf) hdr
    have hgSide := C.other_neighbor_of_red_is_blueSide hf hr hfr hfg hgr
    have hg : C.color g = .bluish := by
      rcases hgSide with hg | hg
      · exact (hnoBlue g hfg hg).elim
      · exact hg
    have hcg : Q.c ≠ g := by intro h; subst g; exact hfc hfg
    have heg : Q.e ≠ g := by intro h; subst g; exact hfe hfg
    apply containsNegativeN C ha hb hf Q.hc Q.he Q.hd hg
      hab Q.hac Q.had Q.hbe Q.hbd Q.hdf.symm hfg hfc hfe
    simp [hab.ne, Q.hac.ne, Q.had.ne, Q.hbe.ne, Q.hbd.ne,
      hfd, hfcV, hfeV, Q.hcd, Q.hce,
      redSide_ne_bluish (Or.inl hf) hg,
      redSide_ne_bluish (Or.inl ha) hg,
      redSide_ne_bluish (Or.inl hb) hg, Q.hfa.symm, Q.hfb.symm,
      vertex_ne_of_color_eq ha Q.he (by decide),
      vertex_ne_of_color_eq hb Q.hc (by decide),
      hcg, heg, Q.hde.symm,
      hgd.symm]
  · have lower : 1 ≤ vertexDegree G Q.f := by
      unfold vertexDegree
      have hs : ({Q.d} : Set V) ⊆ G.neighborSet Q.f := by
        intro z hz
        have : z = Q.d := by simpa using hz
        subst z
        exact Q.hdf.symm
      simpa using Set.ncard_le_ncard hs
    by_cases hfdeg1 : vertexDegree G Q.f = 1
    · apply containsNegativeDcE C ha hb hf Q.hc Q.he Q.hd hfdeg1
        hab Q.hac Q.had Q.hbe Q.hbd Q.hdf.symm hfc hfe
      simp [hab.ne, Q.hac.ne, Q.had.ne, Q.hbe.ne, Q.hbd.ne,
        hfd, hfcV, hfeV, Q.hcd, Q.hce, Q.hde.symm,
        Q.hfa.symm, Q.hfb.symm,
        vertex_ne_of_color_eq ha Q.he (by decide),
        vertex_ne_of_color_eq hb Q.hc (by decide)]
    · by_cases hfdeg2 : vertexDegree G Q.f = 2
      · obtain ⟨g, hfg, hgd⟩ :=
          exists_other_neighbor_of_degree_two hfdeg2 Q.hdf.symm
        have hg := no_blue_neighbor_is_bluish C hf hfg hnoBlue
        have hcg : Q.c ≠ g := by intro h; subst g; exact hfc hfg
        have heg : Q.e ≠ g := by intro h; subst g; exact hfe hfg
        apply containsNegativeDcD C ha hb hf Q.hc Q.he Q.hd hg hfdeg2
          hab Q.hac Q.had Q.hbe Q.hbd Q.hdf.symm hfg hfc hfe
        simp [hab.ne, Q.hac.ne, Q.had.ne, Q.hbe.ne, Q.hbd.ne,
          hfd, hfcV, hfeV, Q.hcd, Q.hce,
          redSide_ne_bluish (Or.inr hf) hg,
          redSide_ne_bluish (Or.inl ha) hg,
          redSide_ne_bluish (Or.inl hb) hg, Q.hfa.symm, Q.hfb.symm,
          vertex_ne_of_color_eq ha Q.he (by decide),
          vertex_ne_of_color_eq hb Q.hc (by decide),
          hcg, heg, Q.hde.symm,
          hgd.symm]
      · have hfdeg3 : vertexDegree G Q.f = 3 := by
          have upper := C.subcubic Q.f
          omega
        obtain ⟨g, h, hfg, hfh, hgd, hhd, hgh⟩ :=
          exists_two_other_neighbors_of_degree_three hfdeg3 Q.hdf.symm
        have hg := no_blue_neighbor_is_bluish C hf hfg hnoBlue
        have hh := no_blue_neighbor_is_bluish C hf hfh hnoBlue
        have hcg : Q.c ≠ g := by intro h; subst g; exact hfc hfg
        have hch : Q.c ≠ h := by intro h; subst h; exact hfc hfh
        have heg : Q.e ≠ g := by intro h; subst g; exact hfe hfg
        have heh : Q.e ≠ h := by intro h; subst h; exact hfe hfh
        apply containsNegativeT C ha hb hf Q.hc Q.he Q.hd hg hh
          hab Q.hac Q.had Q.hbe Q.hbd Q.hdf.symm hfg hfh hfc hfe
        simp [hab.ne, Q.hac.ne, Q.had.ne, Q.hbe.ne, Q.hbd.ne,
          hfd, hfcV, hfeV, hgh, Q.hcd, Q.hce,
          redSide_ne_bluish (Or.inr hf) hg,
          redSide_ne_bluish (Or.inr hf) hh,
          redSide_ne_bluish (Or.inl ha) hg,
          redSide_ne_bluish (Or.inl ha) hh,
          redSide_ne_bluish (Or.inl hb) hg,
          redSide_ne_bluish (Or.inl hb) hh, Q.hfa.symm, Q.hfb.symm,
          vertex_ne_of_color_eq ha Q.he (by decide),
          vertex_ne_of_color_eq hb Q.hc (by decide),
          hcg, hch, heg, heh, Q.hde.symm,
          hgd.symm, hhd.symm]

end Subcubic
