import Subcubic.Lemma4_5
import Mathlib.Data.Fin.VecNotation

/-!
# Basic definitions for Lemma 4.8

The displayed configuration is the induced path
`a-b-c-d-e-f-g-h`, with red edges `ab`, `ef` and blue edges `cd`, `gh`.
This file first isolates the routine third-neighbor setup used throughout the
case analysis in the paper.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The eight displayed vertices, in order, induce exactly a path. -/
def FormsInducedPath8 (G : SimpleGraph V)
    (a b c d e f g h : V) : Prop :=
  let p : Fin 8 → V := ![a, b, c, d, e, f, g, h]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj x y ↔ G.Adj (p x) (p y)

/-- The conclusion used by Lemmas 4.5 and 4.8: after zero or more valid
cut-preserver flips, the recomputed coloring contains a positive reducer or
a cut enhancer. -/
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

end Subcubic
