import Subcubic.Lemma4_10.Case3_2_2_3_2_3

/-!
# Lemma 4.10

Public assembly of the case lemmas.  Distance bounds from the paper are not
part of the statement.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 4.10.**  If `a-b-c-d-e-f` is an induced path, `ab` and `ef`
are red edges, and `cd` is a blue edge, then a permitted sequence of flips
produces a positive tail reducer or a cut enhancer.  The two endpoint
hypotheses are the additional assumptions used in the paper. -/
theorem lemma4_10
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoBlueAtF : ∀ v, G.Adj f v → C.color v ≠ .blue) :
    HasReachableReduction C := by
  classical
  rcases lemma4_10_cases1_and_2_setup3 C hpath ha hb hc hd he hf
      hNoBlueAtA hNoBlueAtF with hresult | hDeep
  · exact hresult
  · obtain ⟨Q3⟩ := hDeep
    rcases lemma4_10_case_3_1 C hpath ha hb hc hd he hf Q3 with
      hresult | hLate
    · exact hresult
    · obtain ⟨Q3_2⟩ := hLate
      rcases lemma4_10_setup_i C hpath ha hb hc hd he hf Q3_2 with
        hresult | hI
      · exact hresult
      · obtain ⟨I⟩ := hI
        by_cases hBlue : ∃ j, G.Adj I.i j ∧ j ≠ c ∧ j ≠ d ∧ C.color j = .blue
        · obtain ⟨j, hij, hjc, hjd, hj⟩ := hBlue
          exact lemma4_10_case_3_2_1 C hpath ha hb hc hd he hf I
            hj hij hjc hjd
        · have hOutsideBluish : ∀ z, G.Adj I.i z → z ≠ c → z ≠ d →
              C.color z = .bluish := by
            intro z hiz hzc hzd
            cases hz : C.color z with
            | red =>
                exact (C.reddish_not_adj_redSide I.hi (Or.inl hz) hiz).elim
            | reddish =>
                exact (C.reddish_not_adj_redSide I.hi (Or.inr hz) hiz).elim
            | blue =>
                exact (hBlue ⟨z, hiz, hzc, hzd, hz⟩).elim
            | bluish => exact rfl
          rcases lemma4_10_bluish_i_cases C hpath ha hb hc hd he hf I
              hOutsideBluish with hresult | hJK
          · exact hresult
          · obtain ⟨JK⟩ := hJK
            rcases lemma4_10_jk_cases C hpath ha hb hc hd he hf
                hNoBlueAtA JK with hresult | hJ
            · exact hresult
            · obtain ⟨J⟩ := hJ
              rcases lemma4_10_j_cases C hpath ha hb hc hd he hf J with
                hresult | hOther
              · exact hresult
              · obtain ⟨l, hl, hjl, hla, hjf⟩ := hOther
                let Q : Lemma4_10OtherRedConfiguration C a b c d e f := {
                  toLemma4_10JConfiguration := J
                  l := l
                  hl := hl
                  hjl := hjl
                  hla := hla
                  hjf := hjf }
                exact lemma4_10_other_red_complete C hpath ha hb hc hd he hf Q

end Subcubic
