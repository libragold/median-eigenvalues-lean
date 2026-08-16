import Subcubic.Lemma4_10
import Subcubic.Lemma3_7
import Mathlib.Data.Fin.VecNotation

/-! Basic definitions for Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The four displayed vertices, in order, induce exactly a path. -/
def FormsInducedPath4 (G : SimpleGraph V) (a b c d : V) : Prop :=
  let p : Fin 4 → V := ![a, b, c, d]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y ↔
      G.Adj (p x) (p y)

omit [Fintype V] in
theorem FormsInducedPath4.reverse {a b c d : V}
    (h : FormsInducedPath4 G a b c d) : FormsInducedPath4 G d c b a := by
  classical
  dsimp [FormsInducedPath4] at h ⊢
  rcases h with ⟨hinj, hedge⟩
  let ρ : Fin 4 → Fin 4 := ![3, 2, 1, 0]
  have hρ : Function.Injective ρ := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ρ]
  have hmap (z : Fin 4) :
      (![d, c, b, a] z) = (![a, b, c, d] (ρ z)) := by
    fin_cases z <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hρ
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ρ, graphOfEdges]

/-- The local configuration after introducing the two third neighbors. -/
structure Lemma4_12ThirdNeighborConfiguration (C : MatchingCutColoring G)
    (a b c d : V) where
  e : V
  f : V
  he : C.color e = .bluish
  hf : C.color f = .reddish
  hbe : G.Adj b e
  hcf : G.Adj c f
  hea : e ≠ a
  hec : e ≠ c
  hfb : f ≠ b
  hfd : f ≠ d
  hedeg : vertexDegree G e = 3
  hfdeg : vertexDegree G f = 3

end Subcubic
