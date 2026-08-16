import Subcubic.Lemma5_9.CaseMixed
import Subcubic.Lemma5_9.CaseKH

/-! Assembly of Lemma 5.9, Case (3.4). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case3_4
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_9Case3_4Configuration C a b c d e f g h)
    (hic : ¬ G.Adj Q.i c) :
    HasReachableNegativeReduction C := by
  rcases lemma5_9_setup_i C hpath hc hd he hf hg hh Q hic with hresult | hI
  · exact hresult
  · obtain ⟨I⟩ := hI
    rcases lemma5_9_setup_k C hpath ha hb hc hd hf hg I with hresult | hK
    · exact hresult
    · obtain ⟨K⟩ := hK
      by_cases hkj : G.Adj K.k K.j
      · rcases lemma5_9_case_k_adj_j C hpath ha hb hc hd he hNoBlueAtA K hkj with
          hresult | hblue
        · exact hresult
        · obtain ⟨B⟩ := hblue
          rcases lemma5_9_case_kj_blue_setup C hpath ha hb hc hd he hf hg hh
              hNoBlueAtA B with hresult | hflip
          · exact hresult
          · obtain ⟨F⟩ := hflip
            exact lemma5_9_case_kj_blue_flip C hpath ha hb hc hd he hf F
      · by_cases hkh : G.Adj K.k h
        · exact lemma5_9_case_k_not_adj_j_adj_h C hpath ha hb hc hd he hf hg hh
            K hkj hkh
        · obtain ⟨R⟩ := lemma5_9_setup_lm C K hkj hkh
          rcases R.hlSide with hl | hl <;> rcases R.hmSide with hm | hm
          · exact lemma5_9_case_lm_blue C hpath ha hb hc hd he R hl hm
          · let R' : Lemma5_9LMConfiguration C a b c d e f g h := { R with
              l := R.m
              m := R.l
              hkl := R.hkm
              hkm := R.hkl
              hlc := R.hmc
              hmc := R.hlc
              hlm := R.hlm.symm
              hlSide := Or.inr hm
              hmSide := Or.inl hl }
            exact lemma5_9_case_lm_mixed C hpath ha hb hc hd he hf hg hh R' hm hl
          · exact lemma5_9_case_lm_mixed C hpath ha hb hc hd he hf hg hh R hl hm
          · exact lemma5_9_case_lm_bluish C hpath ha hb hc hd he hNoBlueAtA R
              R.hi R.hj R.hx R.hy R.hk hl hm

end Subcubic
