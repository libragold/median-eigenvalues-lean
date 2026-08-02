import Subcubic.Lemma4_12.Case3SharedFlip

/-!
# Lemma 4.12 proof assembly

The paper's invocations of Lemma 4.11 have been expanded in
`InlinePath3.lean`; no distance bound occurs in this statement.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Complete the proof after orienting the path so that the third neighbor
`e` of `b` is not adjacent to the left endpoint `a`. -/
theorem lemma4_12_oriented
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma4_12CoreConfiguration C a b c d)
    (hef : ¬ G.Adj Q.e Q.f) (hea : ¬ G.Adj Q.e a) :
    HasReachableReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  by_cases hOtherRed : ∃ g, G.Adj Q.e g ∧ C.color g = .red ∧ g ≠ b
  · obtain ⟨g, heg, hg, hgb⟩ := hOtherRed
    obtain ⟨R, hRQ⟩ := lemma4_12_case2_setup C Q hg heg hgb
    subst Q
    rcases lemma4_12_case2_flip_path C ⟨hinj, hedge⟩ ha hb hc hd R
        hea with
      hresult | hpath3
    · exact hresult
    · obtain ⟨P⟩ := hpath3
      exact P.reduces
  · have hOnlyRedB : ∀ z, G.Adj Q.e z → C.color z = .red → z = b := by
      intro z hez hz
      by_contra hzb
      exact hOtherRed ⟨z, hez, hz, hzb⟩
    by_cases hShare : ∃ g, C.color g = .reddish ∧ G.Adj Q.e g ∧ G.Adj d g
    · obtain ⟨g, hg, heg, hdg⟩ := hShare
      rcases lemma4_12_case3_shared_setup C ⟨hinj, hedge⟩ ha hb hc hd
          Q hg heg hdg with hresult | hshared
      · exact hresult
      · obtain ⟨R, hRQ⟩ := hshared
        subst Q
        by_cases hRedH : ∃ j, G.Adj R.h j ∧ C.color j = .red
        · obtain ⟨j, hhj, hj⟩ := hRedH
          rcases lemma4_12_shared_h_red_flip_path C ⟨hinj, hedge⟩
              ha hb hc hd hNoBlueAtA R hef hj hhj with
              hresult | hpath3
          · exact hresult
          · obtain ⟨P⟩ := hpath3
            exact P.reduces
        · have hNoRedH : ∀ z, G.Adj R.h z → C.color z ≠ .red := by
            intro z hhz hz
            exact hRedH ⟨z, hhz, hz⟩
          by_cases hRedI : ∃ j, G.Adj R.i j ∧ C.color j = .red
          · obtain ⟨j, hij, hj⟩ := hRedI
            exact lemma4_12_shared_i_red_flip C ⟨hinj, hedge⟩
              ha hb hc hd hNoBlueAtA R hOnlyRedB
              hNoRedH hj hij
          · have hNoRedI : ∀ z, G.Adj R.i z → C.color z ≠ .red := by
              intro z hiz hz
              exact hRedI ⟨z, hiz, hz⟩
            exact lemma4_12_case3_shared_blue_isolated C R hNoRedH hNoRedI
    · have hNoShare : ∀ z, C.color z = .reddish →
          G.Adj Q.e z → ¬ G.Adj d z := by
        intro z hz hez hdz
        exact hShare ⟨z, hz, hez, hdz⟩
      obtain ⟨R, hRQ⟩ := lemma4_12_no_share_setup C hd hc hcd hNoRedAtD
        Q hOnlyRedB hNoShare
      subst Q
      exact lemma4_12_case3_no_share C ⟨hinj, hedge⟩ ha hb hc hd
        hNoRedAtD R hNoShare hea hef

/-- **Lemma 4.12.**  If `a-b-c-d` is an induced path, `ab` is a red edge,
`cd` is a blue edge, `a` has no blue neighbor, and `d` has no red neighbor,
then a permitted sequence of flips produces a positive tail reducer or a
cut enhancer. -/
theorem lemma4_12
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red) :
    HasReachableReduction C := by
  classical
  rcases lemma4_12_setup C hpath ha hb hc hd with hresult | hcore
  · exact hresult
  · obtain ⟨Q⟩ := hcore
    by_cases hef : G.Adj Q.e Q.f
    · exact lemma4_12_case_ef C hpath ha hb hc hd Q hef
    · by_cases hea : G.Adj Q.e a
      · by_cases hfd : G.Adj Q.f d
        · rcases lemma4_12_case4_split C hpath ha hb hc hd hNoRedAtD
              Q hea hfd hef with hresult | hred
          · exact hresult
          · obtain ⟨R⟩ := hred
            rcases lemma4_12_case4_red_flip_path C hpath ha hb hc hd R with
              hresult | hpath3
            · exact hresult
            · obtain ⟨P⟩ := hpath3
              exact P.reduces
        · let R : Lemma4_12CoreConfiguration C.swapSides d c b a := {
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
          have hRev := lemma4_12_oriented C.swapSides hpath.reverse
            (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
            hNoBlueAtDRev hNoRedAtARev R (fun h => hef h.symm) hfd
          exact HasReachableReduction.of_swapSides C hRev
      · exact lemma4_12_oriented C hpath ha hb hc hd
          hNoBlueAtA hNoRedAtD Q hef hea

end Subcubic
