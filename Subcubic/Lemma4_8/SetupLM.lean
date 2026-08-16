import Subcubic.Lemma4_8.CaseKH

/-! Entering case (3.4.3): expose the other two neighbors of `k`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_8LMConfiguration (C : MatchingCutColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8KConfiguration C a b c d e f g h where
  hkj : ¬ G.Adj k j
  hkh : ¬ G.Adj k h
  l : V
  m : V
  hkl : G.Adj k l
  hkm : G.Adj k m
  hlc : l ≠ c
  hmc : m ≠ c
  hlm : l ≠ m
  hlSide : C.color l = .blue ∨ C.color l = .bluish
  hmSide : C.color m = .blue ∨ C.color m = .bluish

theorem lemma4_8_k_cases
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8KConfiguration C a b c d e f g h) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8LMConfiguration C a b c d e f g h) := by
  by_cases hkj : G.Adj Q.k Q.j
  · exact Or.inl (lemma4_8_case_k_adj_j C hpath ha hb hc hd he hf hg hh Q hkj)
  by_cases hkh : G.Adj Q.k h
  · exact Or.inl (lemma4_8_case_k_not_adj_j_adj_h C hpath ha hb hc hd he hf hg hh
      Q hkj hkh)
  obtain ⟨l, m, hkl, hkm, hlc, hmc, hlm⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hkdeg Q.hck.symm
  have neighbor_blueSide {z : V} (hkz : G.Adj Q.k z) :
      C.color z = .blue ∨ C.color z = .bluish := by
    rw [← C.not_mem_redSide_iff]
    intro hzRed
    have hcorrect := C.color_correct Q.k
    rw [Q.hk] at hcorrect
    exact hcorrect.2 ⟨z, hzRed, hkz⟩
  exact Or.inr ⟨{ Q with
    hkj := hkj
    hkh := hkh
    l := l
    m := m
    hkl := hkl
    hkm := hkm
    hlc := hlc
    hmc := hmc
    hlm := hlm
    hlSide := neighbor_blueSide hkl
    hmSide := neighbor_blueSide hkm }⟩

end Subcubic
