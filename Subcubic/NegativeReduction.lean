import Subcubic.PositiveReduction

/-!
# Reachable negative reductions

The Section 5 analogue of `HasReachableReduction`: after zero or more valid
cut-preserver flips, the recomputed coloring contains a negative tail reducer
or a cut enhancer.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def HasReachableNegativeReduction (C : GoodColoring G) : Prop :=
  ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
    (ContainsNegativeTailReducer M.toGoodColoring ∨
     ContainsCutEnhancer M.toGoodColoring)

theorem HasReachableNegativeReduction.of_current_ntr (C : GoodColoring G)
    (hntr : ContainsNegativeTailReducer C) :
    HasReachableNegativeReduction C := by
  refine ⟨C.toMatchingCut, .refl, Or.inl ?_⟩
  exact (containsInducedUpToSwap_congr_color IsNegativeTailReducer
    (by simp)).1 hntr

theorem HasReachableNegativeReduction.of_current_ce (C : GoodColoring G)
    (hce : ContainsCutEnhancer C) : HasReachableNegativeReduction C := by
  refine ⟨C.toMatchingCut, .refl, Or.inr ?_⟩
  exact (containsInducedUpToSwap_congr_color IsCutEnhancer
    (by simp)).1 hce

/-- An absolute reducer or cut enhancer reachable in the sense of Lemma 3.6
is a reachable negative reduction. -/
theorem HasReachableNegativeReduction.of_lemma3_6
    (C : GoodColoring G) (h : HasReachableLemma3_6Obstruction C) :
    HasReachableNegativeReduction C := by
  rcases h with ⟨M, hreach, habsolute | hce⟩
  · exact ⟨M, hreach, Or.inl habsolute.2⟩
  · exact ⟨M, hreach, Or.inr hce⟩

theorem HasReachableNegativeReduction.after_flip (C : GoodColoring G)
    {M₁ : MatchingCut G} {r s : V}
    (hflip : C.toMatchingCut.IsFlipAt M₁ r s)
    (hresult : HasReachableNegativeReduction M₁.toGoodColoring) :
    HasReachableNegativeReduction C := by
  rcases hresult with ⟨M, hreach, hfound⟩
  have hround : M₁.toGoodColoring.toMatchingCut = M₁ := by
    apply MatchingCut.ext _ _
    simp [GoodColoring.toMatchingCut_side, GoodColoring.redSide,
      MatchingCut.redSideOf_color]
  rw [hround] at hreach
  have prepend : ∀ {N : MatchingCut G},
      M₁.FlipReachable N → C.toMatchingCut.FlipReachable N := by
    intro N hN
    induction hN with
    | refl => exact .step .refl hflip
    | @step N₁ N₂ x y hN hxy ih => exact .step ih hxy
  exact ⟨M, prepend hreach, hfound⟩

theorem HasReachableNegativeReduction.of_swapSides (C : GoodColoring G)
    (h : HasReachableNegativeReduction C.swapSides) :
    HasReachableNegativeReduction C := by
  rcases h with ⟨M, hreach, hfound⟩
  have hstart : C.swapSides.toMatchingCut.swapSides = C.toMatchingCut := by
    apply MatchingCut.ext
    ext v
    cases hc : C.color v <;>
      simp [GoodColoring.toMatchingCut_side, GoodColoring.redSide,
        redSideOf, Color.IsRedSide, Color.swap, hc]
  have hreach' := hreach.swapSides
  rw [hstart] at hreach'
  let D := M.toGoodColoring
  have hcolor : M.swapSides.toGoodColoring.color = D.swapSides.color := by
    funext v
    simp [D]
  have hfoundD : ContainsNegativeTailReducer D.swapSides ∨
      ContainsCutEnhancer D.swapSides := by
    rcases hfound with hntr | hce
    · exact Or.inl
        ((containsInducedUpToSwap_swapSides IsNegativeTailReducer D).2 hntr)
    · exact Or.inr
        ((containsInducedUpToSwap_swapSides IsCutEnhancer D).2 hce)
  refine ⟨M.swapSides, hreach', ?_⟩
  rcases hfoundD with hntr | hce
  · exact Or.inl
      ((containsInducedUpToSwap_congr_color IsNegativeTailReducer hcolor).2 hntr)
  · exact Or.inr
      ((containsInducedUpToSwap_congr_color IsCutEnhancer hcolor).2 hce)

end Subcubic
