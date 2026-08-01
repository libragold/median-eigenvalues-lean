import Subcubic.Lemma4_8.Basic
import Mathlib.Tactic.FinCases

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem FormsInducedPath8.reverse {a b c d e f g h : V}
    (hp : FormsInducedPath8 G a b c d e f g h) :
    FormsInducedPath8 G h g f e d c b a := by
  classical
  dsimp [FormsInducedPath8] at hp ⊢
  rcases hp with ⟨hinj, hedge⟩
  let p : Fin 8 → V := ![a, b, c, d, e, f, g, h]
  let q : Fin 8 → V := ![h, g, f, e, d, c, b, a]
  have hq (x : Fin 8) : q x = p x.rev := by
    fin_cases x <;> rfl
  have hrev : ∀ x y : Fin 8, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj x y ↔
      (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj x.rev y.rev := by
    native_decide
  constructor
  · intro x y hxy
    apply Fin.rev_injective
    apply hinj
    change p x.rev = p y.rev
    rw [← hq x, ← hq y]
    exact hxy
  · intro x y
    rw [hrev x y, hedge (x.rev) (y.rev)]
    change G.Adj (p x.rev) (p y.rev) ↔ G.Adj (q x) (q y)
    rw [hq x, hq y]

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
