import Subcubic.Lemma5_4.BlueMeets

/-! Case 2.2.4 of Lemma 5.4. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem redSide_ne_bluish'' {C : MatchingCutColoring G} {x y : V}
    (hx : C.color x = .red ∨ C.color x = .reddish)
    (hy : C.color y = .bluish) : x ≠ y := by
  intro h; subst y; rcases hx with hx | hx <;> simp_all

/-- Case 2.2.4: when `f` is red and has a blue neighbor, flipping `fg`
turns the common bluish neighbor `d` blue, giving reversed `ntr-a`. -/
theorem lemma5_4_red_f_blue_neighbor
    (C : MatchingCutColoring G) {a b g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) (Q : Lemma5_4SharedConfiguration C a b)
    (hf : C.color Q.f = .red) (hg : C.color g = .blue)
    (hfg : G.Adj Q.f g) : HasReachableNegativeReduction C := by
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  have hfCorrect := C.color_correct Q.f
  rw [hf] at hfCorrect
  obtain ⟨_, r, hrSide, hfr⟩ := hfCorrect
  have hrCases := (C.mem_redSide_iff r).1 hrSide
  have hr : C.color r = .red := by
    rcases hrCases with hr | hr
    · exact hr
    · exact (C.reddish_not_adj_redSide hr (Or.inl hf) hfr.symm).elim
  have hgCorrect := C.color_correct g
  rw [hg] at hgCorrect
  obtain ⟨_, i, hiSide, hgi⟩ := hgCorrect
  have hiCases := (C.not_mem_redSide_iff i).1 hiSide
  have hi : C.color i = .blue := by
    rcases hiCases with hi | hi
    · exact hi
    · exact (C.bluish_not_adj_blueSide hi (Or.inl hg) hgi.symm).elim
  rcases exists_flipAt_or_cutEnhancer C hf hg hr hi
      (degree_of_color (Or.inl hf)) (degree_of_color (Or.inr hg))
      hfr hfg hgi with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toColoring
    have hdf : Q.d ≠ Q.f := Q.hdf.ne
    have hdg : Q.d ≠ g := vertex_ne_of_color_eq Q.hd hg (by decide)
    have hdD : D.color Q.d = .blue :=
      blue_of_bluish_gains_flipped_red C hflip Q.hd Q.hdf hdf hdg
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        Q.hfa.symm
        (vertex_ne_of_color_eq ha hg (by decide))
        Q.hfb.symm
        (vertex_ne_of_color_eq hb hg (by decide))
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        Q.hfb.symm
        (vertex_ne_of_color_eq hb hg (by decide))
        Q.hfa.symm
        (vertex_ne_of_color_eq ha hg (by decide))
    have hntrSwap := containsNegativeA D.swapSides
      (a := Q.d) (b := a) (c := b)
      (by simp [hdD]) (by simp [haD]) (by simp [hbD])
      Q.had.symm Q.hbd.symm hab
      (by simp [List.nodup_cons, Q.had.ne.symm, Q.hbd.ne.symm, hab.ne])
    apply HasReachableNegativeReduction.after_flip C hflip
    apply HasReachableNegativeReduction.of_current_ntr D
    exact (containsInducedUpToSwap_swapSides IsNegativeTailReducer D).1 hntrSwap
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
