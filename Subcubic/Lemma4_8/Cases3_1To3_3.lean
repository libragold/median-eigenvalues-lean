import Subcubic.Lemma4_8.Case3_3

/-! Dispatcher for cases (3.1)--(3.3) of Lemma 4.8. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_cases3_1_to_3_3
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8Case3Configuration C a b c d e f g h) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8Case3_4Configuration C a b c d e f g h) := by
  by_cases hxy : Q.x = Q.y
  · exact Or.inl (lemma4_8_case_shared_ab_neighbor C hpath ha hb hc hd he hf Q hxy)
  by_cases hij : G.Adj Q.i Q.j
  · exact Or.inl (lemma4_8_case_i_adj_j C hpath hc hd he hf Q hij)
  by_cases hic : G.Adj Q.i c
  · by_cases hjf : G.Adj Q.j f
    · exact Or.inl (lemma4_8_case_w C hpath ha hb hc hd he hf hg hh Q
        hxy hij hic hjf)
    · exact Or.inr ⟨{ Q with
        hxy := hxy
        hij := hij
        hnotBoth := fun h => hjf h.2 }⟩
  · exact Or.inr ⟨{ Q with
      hxy := hxy
      hij := hij
      hnotBoth := fun h => hic h.1 }⟩

end Subcubic
