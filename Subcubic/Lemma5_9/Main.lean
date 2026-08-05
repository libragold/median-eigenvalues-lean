import Subcubic.Lemma5_9.Case3_4

/-! Final assembly of Lemma 5.9. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 5.9.**  For the induced eight-vertex path with alternating red
and blue matching edges, and the endpoint hypotheses from the paper, a
negative tail reducer is reachable by permitted flips or a cut enhancer is
already present.  Distance bounds are intentionally omitted. -/
theorem lemma5_9
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtH : ∀ v, G.Adj h v → C.color v ≠ .red) :
    HasReachableNegativeReduction C := by
  classical
  rcases lemma5_9_cases1_and_2_setup3 C hpath ha hb hc hd he hf hg hh
      hNoBlueAtA hNoRedAtH with hresult | hdeep
  · exact hresult
  · obtain ⟨D⟩ := hdeep
    rcases lemma5_9_cases3_1_to_3_3 C hpath ha hb hc hd he hf hg hh D with
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
        rcases lemma5_9_cases1_and_2_setup3 C.swapSides hpath.reverse
            (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
            (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
            hNoBlueAtHSwap hNoRedAtASwap with hresult | hdeepRev
        · exact HasReachableNegativeReduction.of_swapSides C hresult
        · obtain ⟨Drev⟩ := hdeepRev
          rcases lemma5_9_cases3_1_to_3_3 C.swapSides hpath.reverse
              (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              Drev with hresult | hlateRev
          · exact HasReachableNegativeReduction.of_swapSides C hresult
          · obtain ⟨R⟩ := hlateRev
            have hRi : C.color R.i = .bluish := by
              have hRiSwap := R.hi
              change (C.color R.i).swap = .reddish at hRiSwap
              exact (Color.swap_eq_reddish _).1 hRiSwap
            have color_ne {x y : V} {cx cy : Color}
                (hx : C.color x = cx) (hy : C.color y = cy)
                (hxy : cx ≠ cy) : x ≠ y := by
              intro hEq
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
                  Q.hej hdf hdj hfj R.hdi with hEq | hEq | hEq
              · rw [hEq, hd] at hRi
                contradiction
              · rw [hEq, hf] at hRi
                contradiction
              · exact hEq
            have hRic : ¬ G.Adj R.i f := by
              intro hrif
              apply hjf
              simpa [hRieq] using hrif
            have hresultRev := lemma5_9_case3_4 C.swapSides hpath.reverse
              (by simp [hh]) (by simp [hg]) (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              hNoBlueAtHSwap R hRic
            exact HasReachableNegativeReduction.of_swapSides C hresultRev
      · exact lemma5_9_case3_4 C hpath ha hb hc hd he hf hg hh
          hNoBlueAtA Q hic

end Subcubic
