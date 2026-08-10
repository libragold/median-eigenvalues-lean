import Subcubic.Lemma4_8
import Subcubic.Lemma3_7
import Subcubic.PositiveTailReducerWitnesses
import Mathlib.Data.Fin.VecNotation

/-!
# Basic definitions for Lemma 4.10

The displayed configuration is the induced path `a-b-c-d-e-f`, with red
edges `ab`, `ef` and blue edge `cd`.  The conclusion uses the common
`HasReachableReduction` predicate from Lemma 4.8.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The six displayed vertices, in order, induce exactly a path. -/
def FormsInducedPath6 (G : SimpleGraph V)
    (a b c d e f : V) : Prop :=
  let p : Fin 6 → V := ![a, b, c, d, e, f]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y ↔
        G.Adj (p x) (p y)

omit [Fintype V] in
/-- Reversing the displayed path preserves its induced-path hypothesis. -/
theorem FormsInducedPath6.reverse
    {a b c d e f : V} (h : FormsInducedPath6 G a b c d e f) :
    FormsInducedPath6 G f e d c b a := by
  classical
  dsimp [FormsInducedPath6] at h ⊢
  rcases h with ⟨hinj, hedge⟩
  let ρ : Fin 6 → Fin 6 := ![5, 4, 3, 2, 1, 0]
  have hρ : Function.Injective ρ := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ρ]
  have hmap (z : Fin 6) :
      (![f, e, d, c, b, a] z) = (![a, b, c, d, e, f] (ρ z)) := by
    fin_cases z <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hρ
    apply hinj
    simpa [hmap] using hxy
  intro x y
  rw [hmap x, hmap y, ← hedge]
  fin_cases x <;> fin_cases y <;>
    simp [ρ, graphOfEdges]

end Subcubic
