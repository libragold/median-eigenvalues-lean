import Subcubic.FlipLemmas
import Subcubic.TailReducers
import Subcubic.Lemma3_6

/-!
# Reachable positive reductions

General infrastructure for reaching a positive tail reducer or a cut enhancer
after zero or more valid cut-preserver flips.  This is independent of any
particular local lemma.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def HasReachableReduction (C : GoodColoring G) : Prop :=
  ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
    (ContainsPositiveTailReducer M.toGoodColoring ∨
     ContainsCutEnhancer M.toGoodColoring)

theorem HasReachableReduction.of_current_ptr (C : GoodColoring G)
    (hptr : ContainsPositiveTailReducer C) : HasReachableReduction C := by
  refine ⟨C.toMatchingCut, .refl, Or.inl ?_⟩
  exact (containsInducedUpToSwap_congr_color IsPositiveTailReducer
    (by simp)).1 hptr

theorem HasReachableReduction.of_current_ce (C : GoodColoring G)
    (hce : ContainsCutEnhancer C) : HasReachableReduction C := by
  refine ⟨C.toMatchingCut, .refl, Or.inr ?_⟩
  exact (containsInducedUpToSwap_congr_color IsCutEnhancer
    (by simp)).1 hce

/-- An absolute reducer or cut enhancer reachable in the sense of Lemma 3.6
is a reachable positive reduction. -/
theorem HasReachableReduction.of_lemma3_6
    (C : GoodColoring G) (h : HasReachableLemma3_6Obstruction C) :
    HasReachableReduction C := by
  rcases h with ⟨M, hreach, habsolute | hce⟩
  · exact ⟨M, hreach, Or.inl habsolute.1⟩
  · exact ⟨M, hreach, Or.inr hce⟩

/-- A reduction reachable after one valid first flip is also reachable from
the original coloring. -/
theorem HasReachableReduction.after_flip (C : GoodColoring G)
    {M₁ : MatchingCut G} {r s : V}
    (hflip : C.toMatchingCut.IsFlipAt M₁ r s)
    (hresult : HasReachableReduction M₁.toGoodColoring) :
    HasReachableReduction C := by
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

/-- The reduction conclusion is invariant under exchanging the two sides of
the cut.  Flip directions reverse, but the underlying toggled pair is the
same. -/
theorem HasReachableReduction.of_swapSides (C : GoodColoring G)
    (h : HasReachableReduction C.swapSides) : HasReachableReduction C := by
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
  have hfoundD : ContainsPositiveTailReducer D.swapSides ∨
      ContainsCutEnhancer D.swapSides := by
    rcases hfound with hptr | hce
    · exact Or.inl
        ((containsInducedUpToSwap_swapSides IsPositiveTailReducer D).2 hptr)
    · exact Or.inr
        ((containsInducedUpToSwap_swapSides IsCutEnhancer D).2 hce)
  refine ⟨M.swapSides, hreach', ?_⟩
  rcases hfoundD with hptr | hce
  · exact Or.inl
      ((containsInducedUpToSwap_congr_color IsPositiveTailReducer hcolor).2 hptr)
  · exact Or.inr
      ((containsInducedUpToSwap_congr_color IsCutEnhancer hcolor).2 hce)

end Subcubic
