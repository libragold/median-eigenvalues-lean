import Subcubic.Lemma4_5
import Subcubic.PositiveReduction
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Induced-path infrastructure for Lemma 4.8

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

-- Reversing the displayed order gives the same induced path.
omit [Fintype V] in theorem FormsInducedPath8.reverse {a b c d e f g h : V}
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

end Subcubic
