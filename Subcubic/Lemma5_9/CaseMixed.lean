import Subcubic.Lemma5_9.CaseMixedFlip

/-! Assembly of Lemma 5.9, Case (3.4.4.3.2). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_lm_mixed
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma5_9LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .blue) :
    HasReachableNegativeReduction C := by
  rcases lemma5_9_case_lm_mixed_setup C hpath ha hb hc hd he hf hg hh Q hl hm with
    hresult | hconfig
  · exact hresult
  · obtain ⟨P⟩ := hconfig
    by_cases hpl : G.Adj P.p P.l
    · exact lemma5_9_case_lm_mixed_adjacent C hpath ha hb hc hd he hf hg hh P hpl
    · exact lemma5_9_case_lm_mixed_flip C hpath ha hb hc hd he hf hg hh P hpl

end Subcubic
