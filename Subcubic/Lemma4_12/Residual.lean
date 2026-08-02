import Subcubic.Lemma4_12.InlinePath3

/-! Residual configurations whose proofs use the inlined Lemma 4.11 step. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A single valid flip has produced the three alternating monochromatic
edges to which the distance-free Lemma 4.11 argument is applied. -/
structure OneFlipPath3Configuration (C : GoodColoring G) where
  M : MatchingCut G
  r₀ : V
  r₁ : V
  b₀ : V
  b₁ : V
  r₂ : V
  r₃ : V
  hflip : ∃ x y, C.toMatchingCut.IsFlipAt M x y
  hpath : FormsPath6Subgraph G r₀ r₁ b₀ b₁ r₂ r₃
  hr₀ : M.toGoodColoring.color r₀ = .red
  hr₁ : M.toGoodColoring.color r₁ = .red
  hb₀ : M.toGoodColoring.color b₀ = .blue
  hb₁ : M.toGoodColoring.color b₁ = .blue
  hr₂ : M.toGoodColoring.color r₂ = .red
  hr₃ : M.toGoodColoring.color r₃ = .red

/-- Discharge a residual three-edge alternating path by the distance-free,
inlined form of Lemma 4.11, and transport the result back across the flip. -/
theorem OneFlipPath3Configuration.reduces
    {C : GoodColoring G} (Q : OneFlipPath3Configuration C) :
    HasReachableReduction C := by
  obtain ⟨x, y, hflip⟩ := Q.hflip
  exact HasReachableReduction.after_flip C hflip
    (lemma4_11_inline Q.M.toGoodColoring Q.hpath
      Q.hr₀ Q.hr₁ Q.hb₀ Q.hb₁ Q.hr₂ Q.hr₃)

/-- Case (2): besides its red neighbor `b`, the bluish vertex `e` has a red
neighbor `g`; `h` is the red mate of `g`. -/
structure Lemma4_12Case2Configuration (C : GoodColoring G)
    (a b c d : V) extends Lemma4_12CoreConfiguration C a b c d where
  g : V
  h : V
  hg : C.color g = .red
  hh : C.color h = .red
  heg : G.Adj e g
  hgh : G.Adj g h
  hgb : g ≠ b

theorem lemma4_12_case2_setup
    (C : GoodColoring G) {a b c d : V}
    (Q : Lemma4_12CoreConfiguration C a b c d)
    {g : V} (hg : C.color g = .red) (heg : G.Adj Q.e g)
    (hgb : g ≠ b) :
    ∃ R : Lemma4_12Case2Configuration C a b c d,
      R.toLemma4_12CoreConfiguration = Q := by
  have hgCorrect := C.color_correct g
  rw [hg] at hgCorrect
  obtain ⟨_, h, hhSide, hgh⟩ := hgCorrect
  have hhSide' := (C.mem_redSide_iff h).1 hhSide
  have hh : C.color h = .red := by
    rcases hhSide' with hh | hh
    · exact hh
    · exact (C.reddish_not_adj_redSide hh (Or.inl hg) hgh.symm).elim
  exact ⟨⟨Q, g, h, hg, hh, heg, hgh, hgb⟩, rfl⟩

/-- The formal content of the flip in Case (2).  A cut enhancer may be
found while validating the flip; otherwise the recomputed coloring contains
the path `f-c-b-e-g-h`. -/
theorem lemma4_12_case2_flip_path
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma4_12Case2Configuration C a b c d)
    (hea : ¬ G.Adj Q.e a) :
    HasReachableReduction C ∨
      Nonempty (OneFlipPath3Configuration C) := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd hab.symm hbc hcd with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hbD : D.color b = .blue :=
      blue_of_flipped_red_endpoint C hflip ha hab.symm
        (hv (x := (0 : Fin 4)) (y := 2) (by decide))
    have hcD : D.color c = .red :=
      red_of_flipped_blue_endpoint C hflip hd hcd
        (hv (x := (3 : Fin 4)) (y := 1) (by decide))
    have heD : D.color Q.e = .blue := by
      apply blue_of_bluish_gains_flipped_red C hflip Q.he Q.hbe.symm
      · exact Q.hbe.ne.symm
      · exact Q.hec
    have hfD : D.color Q.f = .red := by
      apply red_of_reddish_gains_flipped_blue C hflip Q.hf Q.hcf.symm
      · exact Q.hfb
      · exact Q.hcf.ne.symm
    have hga : Q.g ≠ a := fun h => hea (by simpa [h] using Q.heg)
    have hhb : Q.h ≠ b := by
      intro h
      have hnot := C.redSide_not_adj_second_neighbor
        (by simp [hb]) (by simp [ha]) (by simp [Q.hg]) hab.symm hga.symm
      exact hnot (by simpa [h] using Q.hgh.symm)
    have hgc : Q.g ≠ c := by
      intro h
      have := congrArg C.color h
      simp [Q.hg, hc] at this
    have hhc : Q.h ≠ c := by
      intro h
      have := congrArg C.color h
      simp [Q.hh, hc] at this
    have hgD : D.color Q.g = .red :=
      red_of_untouched_red_edge C hflip (by simp [Q.hg]) (by simp [Q.hh])
        Q.hgh Q.hgb hgc hhb hhc
    have hhD : D.color Q.h = .red :=
      red_of_untouched_red_edge C hflip (by simp [Q.hh]) (by simp [Q.hg])
        Q.hgh.symm hhb hhc Q.hgb hgc
    have color_ne {x y : V} {cx cy : Color}
        (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) :
        x ≠ y := by
      intro h
      subst y
      simp_all
    have hnodup : [Q.f, c, b, Q.e, Q.g, Q.h].Nodup := by
      simp [color_ne Q.hf hc (by decide), color_ne Q.hf hb (by decide),
        color_ne Q.hf Q.he (by decide), color_ne Q.hf Q.hg (by decide),
        color_ne Q.hf Q.hh (by decide), color_ne hc hb (by decide),
        color_ne hc Q.he (by decide), hgc.symm, hhc.symm,
        color_ne hb Q.he (by decide), Q.hgb.symm, hhb.symm,
        color_ne Q.he Q.hg (by decide), color_ne Q.he Q.hh (by decide),
        Q.hgh.ne]
    have hsub : FormsPath6Subgraph G Q.f c b Q.e Q.g Q.h := by
      refine ⟨?_, ?_⟩
      · have hvec : (![Q.f, c, b, Q.e, Q.g, Q.h] : Fin 6 → V) =
            [Q.f, c, b, Q.e, Q.g, Q.h].get := by
          funext x
          fin_cases x <;> rfl
        rw [hvec]
        exact hnodup.injective_get
      · intro x y hxy
        have hcf : G.Adj c Q.f := Q.hcf
        have hfc : G.Adj Q.f c := Q.hcf.symm
        have hbc' : G.Adj b c := hbc
        have hcb : G.Adj c b := hbc.symm
        have hbe : G.Adj b Q.e := Q.hbe
        have heb : G.Adj Q.e b := Q.hbe.symm
        have heg : G.Adj Q.e Q.g := Q.heg
        have hge : G.Adj Q.g Q.e := Q.heg.symm
        have hgh : G.Adj Q.g Q.h := Q.hgh
        have hhg : G.Adj Q.h Q.g := Q.hgh.symm
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
        all_goals assumption
    exact Or.inr ⟨⟨M, Q.f, c, b, Q.e, Q.g, Q.h,
      ⟨b, c, hflip⟩, hsub, hfD, hcD, hbD, heD, hgD, hhD⟩⟩
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

/-- Case (4.1) has the same recomputed path as Case (2). -/
theorem lemma4_12_case4_red_flip_path
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma4_12RedGConfiguration C a b c d) :
    HasReachableReduction C ∨
      Nonempty (OneFlipPath3Configuration C) := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd hab.symm hbc hcd with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hbD : D.color b = .blue :=
      blue_of_flipped_red_endpoint C hflip ha hab.symm
        (hv (x := (0 : Fin 4)) (y := 2) (by decide))
    have hcD : D.color c = .red :=
      red_of_flipped_blue_endpoint C hflip hd hcd
        (hv (x := (3 : Fin 4)) (y := 1) (by decide))
    have heD : D.color Q.e = .blue := by
      apply blue_of_bluish_gains_flipped_red C hflip Q.he Q.hbe.symm
      · exact Q.hbe.ne.symm
      · exact Q.hec
    have hfD : D.color Q.f = .red := by
      apply red_of_reddish_gains_flipped_blue C hflip Q.hf Q.hcf.symm
      · exact Q.hfb
      · exact Q.hcf.ne.symm
    have hhb : Q.h ≠ b := by
      intro h
      have hnot := C.redSide_not_adj_second_neighbor
        (by simp [hb]) (by simp [ha]) (by simp [Q.hg]) hab.symm Q.hga.symm
      exact hnot (by simpa [h] using Q.hgh.symm)
    have hgc : Q.g ≠ c := by
      intro h
      have := congrArg C.color h
      simp [Q.hg, hc] at this
    have hhc : Q.h ≠ c := by
      intro h
      have := congrArg C.color h
      simp [Q.hh, hc] at this
    have hgD : D.color Q.g = .red :=
      red_of_untouched_red_edge C hflip (by simp [Q.hg]) (by simp [Q.hh])
        Q.hgh Q.hgb hgc hhb hhc
    have hhD : D.color Q.h = .red :=
      red_of_untouched_red_edge C hflip (by simp [Q.hh]) (by simp [Q.hg])
        Q.hgh.symm hhb hhc Q.hgb hgc
    have color_ne {x y : V} {cx cy : Color}
        (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) :
        x ≠ y := by
      intro h
      subst y
      simp_all
    have hnodup : [Q.f, c, b, Q.e, Q.g, Q.h].Nodup := by
      simp [color_ne Q.hf hc (by decide), color_ne Q.hf hb (by decide),
        color_ne Q.hf Q.he (by decide), color_ne Q.hf Q.hg (by decide),
        color_ne Q.hf Q.hh (by decide), color_ne hc hb (by decide),
        color_ne hc Q.he (by decide), hgc.symm, hhc.symm,
        color_ne hb Q.he (by decide), Q.hgb.symm, hhb.symm,
        color_ne Q.he Q.hg (by decide), color_ne Q.he Q.hh (by decide),
        Q.hgh.ne]
    have hsub : FormsPath6Subgraph G Q.f c b Q.e Q.g Q.h := by
      refine ⟨?_, ?_⟩
      · have hvec : (![Q.f, c, b, Q.e, Q.g, Q.h] : Fin 6 → V) =
            [Q.f, c, b, Q.e, Q.g, Q.h].get := by
          funext x
          fin_cases x <;> rfl
        rw [hvec]
        exact hnodup.injective_get
      · intro x y hxy
        have hcf : G.Adj c Q.f := Q.hcf
        have hfc : G.Adj Q.f c := Q.hcf.symm
        have hbc' : G.Adj b c := hbc
        have hcb : G.Adj c b := hbc.symm
        have hbe : G.Adj b Q.e := Q.hbe
        have heb : G.Adj Q.e b := Q.hbe.symm
        have heg : G.Adj Q.e Q.g := Q.heg
        have hge : G.Adj Q.g Q.e := Q.heg.symm
        have hgh : G.Adj Q.g Q.h := Q.hgh
        have hhg : G.Adj Q.h Q.g := Q.hgh.symm
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
        all_goals assumption
    exact Or.inr ⟨⟨M, Q.f, c, b, Q.e, Q.g, Q.h,
      ⟨b, c, hflip⟩, hsub, hfD, hcD, hbD, heD, hgD, hhD⟩⟩
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

/-- Case (3.1.2.2): flipping the red neighbor `j` of `h` produces the
three-edge path `a-b-c-d-g-h`. -/
theorem lemma4_12_shared_h_red_flip_path
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (R : Lemma4_12SharedBlueConfiguration C a b c d)
    (hef : ¬ G.Adj R.e R.f)
    {j : V} (hj : C.color j = .red) (hhj : G.Adj R.h j) :
    HasReachableReduction C ∨
      Nonempty (OneFlipPath3Configuration C) := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hhc : R.h ≠ c := by
    intro hhc
    have hgf : R.g ≠ R.f := fun h => hef (by simpa [h] using R.heg)
    have hnot := not_adj_fourth_neighbor_of_subcubic C.subcubic
      hbc.symm hcd R.hcf
      (hv (x := (1 : Fin 4)) (y := 3) (by decide))
      R.hfb.symm R.hfd.symm
      (by intro h; have := congrArg C.color h; simp [R.hg, hb] at this)
      (by intro h; have := congrArg C.color h; simp [R.hg, hd] at this) hgf
    exact hnot (by simpa [hhc] using R.hgh.symm)
  have hja : j ≠ a := by
    intro h
    apply hNoBlueAtA R.h
    · simpa [h] using hhj.symm
    · exact R.hh
  have hha : R.h ≠ a := by
    intro h
    have ht := R.hh
    rw [h, ha] at ht
    contradiction
  have hhe : R.h ≠ R.e := by
    intro h
    have ht := R.hh
    have he := R.he
    rw [h, he] at ht
    contradiction
  have hjb : j ≠ b := by
    intro h
    have hnot := C.not_adj_fourth_neighbor
      (v := b) (x := a) (y := c) (z := R.e) (w := R.h) (Or.inl hb)
      hab.symm hbc R.hbe
      (hv (x := (0 : Fin 4)) (y := 2) (by decide))
      R.hea.symm R.hec.symm
      hha hhc hhe
    exact hnot (by simpa [h] using hhj.symm)
  have hjCorrect := C.color_correct j
  rw [hj] at hjCorrect
  obtain ⟨_, k, hkSide, hjk⟩ := hjCorrect
  have hkSide' := (C.mem_redSide_iff k).1 hkSide
  have hk : C.color k = .red := by
    rcases hkSide' with hk | hk
    · exact hk
    · exact (C.reddish_not_adj_redSide hk (Or.inl hj) hjk.symm).elim
  rcases exists_flipAt_or_cutEnhancer C hj R.hh hk R.hi
      hjk hhj.symm R.hhi with hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hjc : j ≠ c := by intro h; subst j; simp_all
    have hjd : j ≠ d := by intro h; subst j; simp_all
    have hhb : R.h ≠ b := by
      intro h; have := congrArg C.color h; simp [R.hh, hb] at this
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hja.symm hha.symm hjb.symm hhb.symm
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hjb.symm hhb.symm hja.symm hha.symm
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        hjc.symm hhc.symm hjd.symm R.hhd.symm
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        hjd.symm R.hhd.symm hjc.symm hhc.symm
    have hgD : D.color R.g = .red := by
      apply red_of_reddish_gains_flipped_blue C hflip R.hg R.hgh
      · intro h; have := congrArg C.color h; simp [R.hg, hj] at this
      · exact R.hgh.ne
    have hhD : D.color R.h = .red :=
      red_of_flipped_blue_endpoint C hflip R.hi R.hhi
        (by intro h; have := congrArg C.color h; simp [R.hi, hj] at this)
    have color_ne {x y : V} {cx cy : Color}
        (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) :
        x ≠ y := by intro h; subst y; simp_all
    have hnodup : [a, b, c, d, R.g, R.h].Nodup := by
      simp [hab.ne, color_ne ha hc (by decide), color_ne ha hd (by decide),
        hbc.ne, color_ne hb hd (by decide), hcd.ne,
        color_ne ha R.hg (by decide), color_ne ha R.hh (by decide),
        color_ne hb R.hg (by decide), color_ne hb R.hh (by decide),
        color_ne hc R.hg (by decide), hhc.symm,
        color_ne hd R.hg (by decide), R.hhd.symm, R.hgh.ne]
    have hsub : FormsPath6Subgraph G a b c d R.g R.h := by
      refine ⟨?_, ?_⟩
      · have hvec : (![a, b, c, d, R.g, R.h] : Fin 6 → V) =
            [a, b, c, d, R.g, R.h].get := by
          funext x
          fin_cases x <;> rfl
        rw [hvec]
        exact hnodup.injective_get
      · intro x y hxy
        have hba := hab.symm
        have hcb := hbc.symm
        have hdc := hcd.symm
        have hdg := R.hdg
        have hgd := R.hdg.symm
        have hgh := R.hgh
        have hhg := R.hgh.symm
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
        all_goals assumption
    exact Or.inr ⟨⟨M, a, b, c, d, R.g, R.h,
      ⟨j, R.h, hflip⟩, hsub, haD, hbD, hcD, hdD, hgD, hhD⟩⟩
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

end Subcubic
