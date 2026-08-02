import Subcubic.Lemma4_8.CaseMixed

/-!
# Lemma 4.8 proof assembly

This is the final module in the Lemma 4.8 dependency chain.  Additional
case modules should be imported here as the proof is completed.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Split the subcases of Case (3.4) after orienting the proof so that `i` is
not adjacent to `c`. The right disjunct is precisely Case (3.4.3.3.2.2),
where the prose flips `np` and returns to the all-bluish case. -/
theorem lemma4_8_case3_4_split
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8Case3_4Configuration C a b c d e f g h)
    (hic : ¬ G.Adj Q.i c) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8MixedPConfiguration C a b c d e f g h) := by
  rcases lemma4_8_setup_k C hpath ha hb hc hd he hf hg hh Q hic with
    hresult | hK
  · exact Or.inl hresult
  · obtain ⟨K⟩ := hK
    rcases lemma4_8_k_cases C hpath ha hb hc hd he hf hg hh K with
      hresult | hLM
    · exact Or.inl hresult
    · obtain ⟨R⟩ := hLM
      rcases R.hlSide with hl | hl <;> rcases R.hmSide with hm | hm
      · exact Or.inl (lemma4_8_case_lm_blue C hpath ha hb hc hd he R hl hm)
      · let R' : Lemma4_8LMConfiguration C a b c d e f g h := { R with
          l := R.m
          m := R.l
          hkl := R.hkm
          hkm := R.hkl
          hlc := R.hmc
          hmc := R.hlc
          hlm := R.hlm.symm
          hlSide := Or.inr hm
          hmSide := Or.inl hl }
        rcases lemma4_8_case_lm_mixed_setup C hpath ha hb hc hd he hf hg hh
            R' hm hl with hresult | hP
        · exact Or.inl hresult
        · exact Or.inr hP
      · rcases lemma4_8_case_lm_mixed_setup C hpath ha hb hc hd he hf hg hh
            R hl hm with hresult | hP
        · exact Or.inl hresult
        · exact Or.inr hP
      · exact Or.inl
          (lemma4_8_case_lm_bluish_complete C hpath ha hb hc hd he hf hg hh
            R hl hm)

/-- Completion of the proof once Case (3.4) has been oriented so that
`i` is not adjacent to `c`.  In the last mixed case, Case (3.4.3.3.2.2)
flips `np` and restarts the refactored all-bluish argument. -/
theorem lemma4_8_case3_4_complete
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8Case3_4Configuration C a b c d e f g h)
    (hic : ¬ G.Adj Q.i c) :
    HasReachableReduction C := by
  rcases lemma4_8_case3_4_split C hpath ha hb hc hd he hf hg hh Q hic with
    hresult | hP
  · exact hresult
  · obtain ⟨P⟩ := hP
    exact lemma4_8_case_lm_mixed_complete C hpath ha hb hc hd he hf hg hh P

/-- **Lemma 4.8.**  An induced path whose end pairs are red edges and whose
two intervening pairs are blue edges contains a positive tail reducer after
zero or more permitted flips, or contains a cut enhancer.  The endpoint
hypotheses are the additional assumptions from the paper: `a` has no blue
neighbor and `h` has no red neighbor. -/
theorem lemma4_8
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtH : ∀ v, G.Adj h v → C.color v ≠ .red) :
    HasReachableReduction C := by
  classical
  rcases lemma4_8_cases1_and_2_setup3 C hpath ha hb hc hd he hf hg hh
      hNoBlueAtA hNoRedAtH with hresult | hdeep
  · exact hresult
  · obtain ⟨D⟩ := hdeep
    rcases lemma4_8_cases3_1_to_3_3 C hpath ha hb hc hd he hf hg hh D with
      hresult | hlate
    · exact hresult
    · obtain ⟨Q⟩ := hlate
      by_cases hic : G.Adj Q.i c
      · have hjf : ¬ G.Adj Q.j f := fun h => Q.hnotBoth ⟨hic, h⟩
        have hNoBlueAtHSwap :
            ∀ v, G.Adj h v → C.swapSides.color v ≠ .blue := by
          intro v hhv hvblue
          apply hNoRedAtH v hhv
          change (C.color v).swap = .blue at hvblue
          exact (Color.swap_eq_blue _).1 hvblue
        have hNoRedAtASwap :
            ∀ v, G.Adj a v → C.swapSides.color v ≠ .red := by
          intro v hav hvred
          apply hNoBlueAtA v hav
          change (C.color v).swap = .red at hvred
          exact (Color.swap_eq_red _).1 hvred
        rcases lemma4_8_cases1_and_2_setup3 C.swapSides hpath.reverse
            (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
            (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
            hNoBlueAtHSwap hNoRedAtASwap with hresult | hdeepRev
        · exact HasReachableReduction.of_swapSides C hresult
        · obtain ⟨Drev⟩ := hdeepRev
          rcases lemma4_8_cases3_1_to_3_3 C.swapSides hpath.reverse
              (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              Drev with hresult | hlateRev
          · exact HasReachableReduction.of_swapSides C hresult
          · obtain ⟨R⟩ := hlateRev
            have hRi : C.color R.i = .bluish := by
              have hRiSwap := R.hi
              change (C.color R.i).swap = .reddish at hRiSwap
              exact (Color.swap_eq_reddish _).1 hRiSwap
            have color_ne {x y : V} {cx cy : Color}
                (hx : C.color x = cx) (hy : C.color y = cy)
                (hxy : cx ≠ cy) : x ≠ y := by
              intro h
              subst y
              simp_all
            have hdj : d ≠ Q.j := color_ne hd Q.hj (by decide)
            have hfj : f ≠ Q.j := color_ne hf Q.hj (by decide)
            have hdf : d ≠ f := color_ne hd hf (by decide)
            have hRieq : R.i = Q.j := by
              rcases C.neighbor_eq_of_three_neighbors (Or.inl he)
                  (by
                    dsimp [FormsInducedPath8] at hpath
                    exact ((hpath.2 3 4).mp (by native_decide)).symm)
                  (by
                    dsimp [FormsInducedPath8] at hpath
                    exact (hpath.2 4 5).mp (by native_decide))
                  Q.hej hdf hdj hfj R.hdi with h | h | h
              · rw [h, hd] at hRi
                contradiction
              · rw [h, hf] at hRi
                contradiction
              · exact h
            have hRic : ¬ G.Adj R.i f := by
              intro hrif
              apply hjf
              simpa [hRieq] using hrif
            have hresultRev := lemma4_8_case3_4_complete C.swapSides
              hpath.reverse
              (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              R hRic
            exact HasReachableReduction.of_swapSides C hresultRev
      · exact lemma4_8_case3_4_complete C hpath ha hb hc hd he hf hg hh Q hic

end Subcubic
