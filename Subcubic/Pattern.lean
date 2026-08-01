import Subcubic.Basic

/-!
# Finite colored configurations

Patterns use `Fin n` as their vertex set. In prose those vertices are named
`a`, `b`, `c`, ...; in Lean they are `0`, `1`, `2`, ... . Every pattern vertex
now has one exact color.
-/

open Set

namespace Subcubic

/-- A finite graph whose vertices have prescribed exact colors. -/
structure ColoredPattern where
  vertexCount : Nat
  graph : SimpleGraph (Fin vertexCount)
  color : Fin vertexCount → Color

namespace ColoredPattern

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : ColoredPattern)

/-- Reverse the roles of the two color-sides in a pattern. Its vertices and
graph stay fixed; only its colors are swapped. -/
def swapSides : ColoredPattern where
  vertexCount := P.vertexCount
  graph := P.graph
  color i := (P.color i).swap

@[simp] theorem swapSides_swapSides : P.swapSides.swapSides = P := by
  cases P
  simp [swapSides]

/-- `P` occurs as an induced colored subgraph of the ambient good coloring. -/
def OccursInduced (C : GoodColoring G) : Prop :=
  ∃ f : Fin P.vertexCount → V,
    Function.Injective f ∧
    (∀ x y, P.graph.Adj x y ↔ G.Adj (f x) (f y)) ∧
    (∀ x, C.color (f x) = P.color x)

/-- Induced colored occurrence depends only on the color function, not on the
proof fields of `GoodColoring`. -/
theorem occursInduced_congr_color {C D : GoodColoring G}
    (hcolor : C.color = D.color) : P.OccursInduced C ↔ P.OccursInduced D := by
  unfold OccursInduced
  rw [hcolor]

/-- Reversing a pattern is equivalent to reversing the ambient coloring. -/
theorem swapSides_occursInduced_iff (C : GoodColoring G) :
    P.swapSides.OccursInduced C ↔ P.OccursInduced C.swapSides := by
  constructor
  · rintro ⟨f, hf, hedge, hcolor⟩
    refine ⟨f, hf, ?_, ?_⟩
    · simpa [swapSides] using hedge
    · intro x
      have := congrArg Color.swap (hcolor x)
      simpa [swapSides] using this
  · rintro ⟨f, hf, hedge, hcolor⟩
    refine ⟨f, hf, ?_, ?_⟩
    · simpa [swapSides] using hedge
    · intro x
      have := congrArg Color.swap (hcolor x)
      simpa [swapSides] using this

/-- `P` occurs in its displayed orientation or with all colors exchanged. -/
def OccursInducedUpToSwap (C : GoodColoring G) : Prop :=
  P.OccursInduced C ∨ P.swapSides.OccursInduced C

/-- Occurrence up to side-swap does not depend on which color-side was named
first. -/
@[simp] theorem occursInducedUpToSwap_swapSides (C : GoodColoring G) :
    P.OccursInducedUpToSwap C.swapSides ↔ P.OccursInducedUpToSwap C := by
  constructor
  · rintro (h | h)
    · exact Or.inr ((P.swapSides_occursInduced_iff C).2 h)
    · left
      simpa using (P.swapSides_occursInduced_iff C.swapSides).1 h
  · rintro (h | h)
    · right
      apply (P.swapSides_occursInduced_iff C.swapSides).2
      simpa using h
    · exact Or.inl ((P.swapSides_occursInduced_iff C).1 h)

end ColoredPattern

/-- An induced occurrence of some pattern in `Catalog`, allowing all colors to
be exchanged. -/
def ContainsInducedUpToSwap {V : Type*} [Fintype V] {G : SimpleGraph V}
    (Catalog : ColoredPattern → Prop) (C : GoodColoring G) : Prop :=
  ∃ P, Catalog P ∧ P.OccursInducedUpToSwap C

/-- Catalog containment likewise depends only on the recomputed color
function. -/
theorem containsInducedUpToSwap_congr_color {V : Type*} [Fintype V]
    {G : SimpleGraph V} (Catalog : ColoredPattern → Prop)
    {C D : GoodColoring G} (hcolor : C.color = D.color) :
    ContainsInducedUpToSwap Catalog C ↔ ContainsInducedUpToSwap Catalog D := by
  unfold ContainsInducedUpToSwap ColoredPattern.OccursInducedUpToSwap
  simp only [ColoredPattern.occursInduced_congr_color _ hcolor]

@[simp] theorem containsInducedUpToSwap_swapSides {V : Type*} [Fintype V]
    {G : SimpleGraph V} (Catalog : ColoredPattern → Prop) (C : GoodColoring G) :
    ContainsInducedUpToSwap Catalog C.swapSides ↔ ContainsInducedUpToSwap Catalog C := by
  simp only [ContainsInducedUpToSwap, ColoredPattern.occursInducedUpToSwap_swapSides]

/-! ## Data-driven finite patterns -/

/-- The simple graph containing exactly the unordered pairs in `edges`.
The explicit inequality makes loops impossible even if malformed input data
were to contain a pair `(v, v)`. -/
def graphOfEdges {n : Nat} (edges : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u, v) ∈ edges ∨ (v, u) ∈ edges)

instance {n : Nat} (edges : List (Fin n × Fin n)) :
    DecidableRel (graphOfEdges edges).Adj := fun _ _ => by
  unfold graphOfEdges
  infer_instance

/-- Compact source data for a tail reducer.

Vertices are `0, 1, ...`, corresponding to `a, b, ...`. The first `sideCount`
vertices are on the red side. Listed exceptions are reddish; all other
red-side vertices are red. A blue-side vertex is blue exactly when it has a
listed neighbor on that side, and is bluish otherwise.
-/
structure PatternData where
  label : String
  vertexCount : Nat
  sideCount : Nat
  edges : List (Fin vertexCount × Fin vertexCount)
  reddish : List (Fin vertexCount) := []

namespace PatternData

/-- The exact color forced by one row of reducer data. -/
def color (D : PatternData) (i : Fin D.vertexCount) : Color :=
  if i.val < D.sideCount then
    if i ∈ D.reddish then .reddish else .red
  else if ∃ j : Fin D.vertexCount,
      D.sideCount ≤ j.val ∧ (graphOfEdges D.edges).Adj i j then .blue
  else .bluish

/-- Turn the row data into the corresponding exact colored graph. -/
def toPattern (D : PatternData) : ColoredPattern where
  vertexCount := D.vertexCount
  graph := graphOfEdges D.edges
  color := D.color

end PatternData

end Subcubic
