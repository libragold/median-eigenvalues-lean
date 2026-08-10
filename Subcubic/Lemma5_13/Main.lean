import Subcubic.Lemma5_13.Case4Main
import Subcubic.Lemma5_13.Case1

/-! Final assembly of the distance-free Lemma 5.13. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 5.13.** If `a-b-c-d` is an induced path, `ab` is red and
`cd` is blue, while `a` has no blue neighbor and `d` has no red neighbor,
then a negative tail reducer is reachable by permitted flips or a cut
enhancer occurs.  The paper's distance bound is omitted. -/
theorem lemma5_13
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red) :
    HasReachableNegativeReduction C := by
  classical
  rcases lemma5_13_third_neighbor_setup C hpath ha hb hc hd with
      hresult | hcore
  · exact hresult
  · obtain ⟨Q⟩ := hcore
    by_cases hef : G.Adj Q.e Q.f
    · exact lemma5_13_case_ef C hpath ha hb hc hd Q hef
    · by_cases hOutsideF : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ d →
          C.color z = .bluish
      · by_cases hea : G.Adj Q.e a
        · rcases lemma5_13_case4_setup C hpath ha hb hc hd hNoBlueAtA
              Q hea hef with hresult | hcase4
          · exact hresult
          · obtain ⟨R, hRQ⟩ := hcase4
            have hRf : R.f = Q.f := by
              exact congrArg (fun T => T.f) hRQ
            have hOutsideR : ∀ z, G.Adj R.f z → z ≠ c → z ≠ d →
                C.color z = .bluish := by
              intro z hfz hzc hzd
              rw [hRf] at hfz
              exact hOutsideF z hfz hzc hzd
            exact lemma5_13_case4 C hpath ha hb hc hd hNoBlueAtA
              hNoRedAtD R hOutsideR
        · by_cases hfd : G.Adj Q.f d
          · by_cases hOutsideE : ∀ z, G.Adj Q.e z → z ≠ b → z ≠ a →
                C.color z = .reddish
            · let R : Lemma5_13ThirdNeighborConfiguration C.swapSides d c b a := {
                e := Q.f
                f := Q.e
                he := by simp [Q.hf]
                hf := by simp [Q.he]
                hbe := Q.hcf
                hcf := Q.hbe
                hea := Q.hfd
                hec := Q.hfb
                hfb := Q.hec
                hfd := Q.hea
                hedeg := Q.hfdeg
                hfdeg := Q.hedeg }
              have hNoBlueAtDRev :
                ∀ v, G.Adj d v → C.swapSides.color v ≠ .blue := by
                intro v hdv hv
                apply hNoRedAtD v hdv
                change (C.color v).swap = .blue at hv
                exact (Color.swap_eq_blue _).1 hv
              have hNoRedAtARev :
                ∀ v, G.Adj a v → C.swapSides.color v ≠ .red := by
                intro v hav hv
                apply hNoBlueAtA v hav
                change (C.color v).swap = .red at hv
                exact (Color.swap_eq_red _).1 hv
              rcases lemma5_13_case4_setup C.swapSides hpath.reverse
                (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
                hNoBlueAtDRev R hfd (fun h => hef h.symm) with
                hresult | hcase4
              · exact HasReachableNegativeReduction.of_swapSides C hresult
              · obtain ⟨S, hSR⟩ := hcase4
                have hSfR : S.f = R.f := by
                  exact congrArg (fun T => T.f) hSR
                have hSf : S.f = Q.e := by
                  simpa [R] using hSfR
                have hOutsideRev : ∀ z, G.Adj S.f z → z ≠ b → z ≠ a →
                  C.swapSides.color z = .bluish := by
                  intro z hsz hzb hza
                  rw [hSf] at hsz
                  have hz := hOutsideE z hsz hzb hza
                  simp [GoodColoring.swapSides, hz]
                have hRev := lemma5_13_case4 C.swapSides hpath.reverse
                  (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
                  hNoBlueAtDRev hNoRedAtARev S hOutsideRev
                exact HasReachableNegativeReduction.of_swapSides C hRev
            · push Not at hOutsideE
              obtain ⟨z, hez, hzb, hza, hzNot⟩ := hOutsideE
              have hz : C.color z = .red := by
                cases hcz : C.color z with
                | red => rfl
                | reddish => exact (hzNot hcz).elim
                | blue =>
                    exact (C.bluish_not_adj_blueSide Q.he (Or.inl hcz) hez).elim
                | bluish =>
                    exact (C.bluish_not_adj_blueSide Q.he (Or.inr hcz) hez).elim
              obtain ⟨T, hTQ⟩ := lemma5_13_case2_setup C Q hz hez hza hzb
              rcases lemma5_13_case2_flip_path C hpath ha hb hc hd T with
                hresult | hpath3
              · exact hresult
              · obtain ⟨P⟩ := hpath3
                exact P.reduces
          · exact lemma5_13_case3 C hpath ha hb hc hd hNoBlueAtA
              Q hef hea hfd hOutsideF
      · push Not at hOutsideF
        obtain ⟨z, hfz, hzc, hzd, hzNot⟩ := hOutsideF
        have hz : C.color z = .blue := by
          cases hcz : C.color z with
          | red =>
              exact (C.reddish_not_adj_redSide Q.hf (Or.inl hcz) hfz).elim
          | reddish =>
              exact (C.reddish_not_adj_redSide Q.hf (Or.inr hcz) hfz).elim
          | blue => rfl
          | bluish => exact (hzNot hcz).elim
        let R : Lemma5_13ThirdNeighborConfiguration C.swapSides d c b a := {
              e := Q.f
              f := Q.e
              he := by simp [Q.hf]
              hf := by simp [Q.he]
              hbe := Q.hcf
              hcf := Q.hbe
              hea := Q.hfd
              hec := Q.hfb
              hfb := Q.hec
              hfd := Q.hea
              hedeg := Q.hfdeg
              hfdeg := Q.hedeg }
        obtain ⟨S, hSR⟩ := lemma5_13_case2_setup C.swapSides R
          (by simp [hz]) hfz (by exact hzd) (by exact hzc)
        subst R
        rcases lemma5_13_case2_flip_path C.swapSides hpath.reverse
            (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha]) S with
          hresult | hpath3
        · exact HasReachableNegativeReduction.of_swapSides C hresult
        · obtain ⟨P⟩ := hpath3
          exact HasReachableNegativeReduction.of_swapSides C P.reduces

end Subcubic
