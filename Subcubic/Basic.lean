import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Set.Card

/-!
# Subcubic graphs with a matching-cut four-coloring

The four colors contain the cut information: red and reddish vertices form one
side, while blue and bluish vertices form the other.  Thus no separate set `A`
is carried through theorem statements.
-/

open Set

namespace Subcubic

variable {V : Type*}

/-- The degree of a vertex, written using `Set.ncard` so that subsequent
definitions do not need to carry a decidability instance for adjacency. -/
noncomputable def vertexDegree (G : SimpleGraph V) (v : V) : Nat :=
  (G.neighborSet v).ncard

/-- Every vertex of `G` has degree at most three. -/
def IsSubcubic [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ v, vertexDegree G v ≤ 3

/-- The four actual colors of vertices in the ambient graph. -/
inductive Color
  | red
  | reddish
  | blue
  | bluish
  deriving DecidableEq, Repr

/-- Whether a color belongs to the red side of the cut. -/
def Color.IsRedSide : Color → Prop
  | .red | .reddish => True
  | .blue | .bluish => False

/-- Exchange the two sides of the cut. -/
def Color.swap : Color → Color
  | .red => .blue
  | .reddish => .bluish
  | .blue => .red
  | .bluish => .reddish

@[simp] theorem Color.swap_swap (c : Color) : c.swap.swap = c := by
  cases c <;> rfl

@[simp] theorem Color.swap_eq_red (c : Color) : c.swap = .red ↔ c = .blue := by
  cases c <;> simp [Color.swap]

@[simp] theorem Color.swap_eq_reddish (c : Color) : c.swap = .reddish ↔ c = .bluish := by
  cases c <;> simp [Color.swap]

@[simp] theorem Color.swap_eq_blue (c : Color) : c.swap = .blue ↔ c = .red := by
  cases c <;> simp [Color.swap]

@[simp] theorem Color.swap_eq_bluish (c : Color) : c.swap = .bluish ↔ c = .reddish := by
  cases c <;> simp [Color.swap]

/-- The red side determined by a complete vertex-coloring. -/
def redSideOf (color : V → Color) : Set V :=
  {v | (color v).IsRedSide}

/-- The graph-theoretic meaning of a color relative to a complete coloring. -/
def HasGraphColor (G : SimpleGraph V) (color : V → Color) (v : V) : Color → Prop
  | .red => v ∈ redSideOf color ∧ ∃ w ∈ redSideOf color, G.Adj v w
  | .reddish => v ∈ redSideOf color ∧ ¬ ∃ w ∈ redSideOf color, G.Adj v w
  | .blue => v ∉ redSideOf color ∧ ∃ w ∉ redSideOf color, G.Adj v w
  | .bluish => v ∉ redSideOf color ∧ ¬ ∃ w ∉ redSideOf color, G.Adj v w

/-- The two color-sides each induce a graph of maximum degree at most one. -/
def IsMatchingColoring [Fintype V] (G : SimpleGraph V) (color : V → Color) : Prop :=
  (∀ v ∈ redSideOf color,
      (G.neighborSet v ∩ redSideOf color).ncard ≤ 1) ∧
  (∀ v ∉ redSideOf color,
      (G.neighborSet v ∩ (redSideOf color)ᶜ).ncard ≤ 1)

/-- A valid ambient coloring, containing all standing assumptions.

`color_correct` says that the assigned color has exactly its intended
graph-theoretic meaning.  In particular, the cut is recovered from `color` and
is not stored separately.
-/
structure MatchingCutColoring [Fintype V] (G : SimpleGraph V) where
  color : V → Color
  subcubic : IsSubcubic G
  matching : IsMatchingColoring G color
  color_correct : ∀ v, HasGraphColor G color v (color v)

namespace MatchingCutColoring

variable [Fintype V] {G : SimpleGraph V} (C : MatchingCutColoring G)

/-- The red side, derived from the coloring. -/
def redSide : Set V := redSideOf C.color

@[simp] theorem mem_redSide_iff (v : V) :
    v ∈ C.redSide ↔ C.color v = .red ∨ C.color v = .reddish := by
  change (C.color v).IsRedSide ↔ _
  cases C.color v <;> simp [Color.IsRedSide]

@[simp] theorem not_mem_redSide_iff (v : V) :
    v ∉ C.redSide ↔ C.color v = .blue ∨ C.color v = .bluish := by
  change ¬ (C.color v).IsRedSide ↔ _
  cases C.color v <;> simp [Color.IsRedSide]

def IsRed (v : V) : Prop := C.color v = .red
def IsReddish (v : V) : Prop := C.color v = .reddish
def IsBlue (v : V) : Prop := C.color v = .blue
def IsBluish (v : V) : Prop := C.color v = .bluish

@[simp] theorem redSideOf_swap :
    redSideOf (fun v ↦ (C.color v).swap) = (redSideOf C.color)ᶜ := by
  ext v
  change (C.color v).swap.IsRedSide ↔ ¬ (C.color v).IsRedSide
  cases C.color v <;> simp [Color.IsRedSide, Color.swap]

private theorem isMatchingColoring_swap :
    IsMatchingColoring G (fun v ↦ (C.color v).swap) := by
  rw [IsMatchingColoring, C.redSideOf_swap]
  rcases C.matching with ⟨hred, hblue⟩
  constructor
  · intro v hv
    change v ∉ redSideOf C.color at hv
    exact hblue v hv
  · intro v hv
    have hv' : v ∈ redSideOf C.color := by
      simpa only [mem_compl_iff, not_not] using hv
    simpa only [compl_compl] using hred v hv'

private theorem hasGraphColor_swap (v : V) (c : Color) :
    HasGraphColor G (fun w ↦ (C.color w).swap) v c.swap ↔
      HasGraphColor G C.color v c := by
  cases c <;> unfold HasGraphColor
  all_goals rw [C.redSideOf_swap]
  all_goals simp only [Color.swap, mem_compl_iff, not_not]

/-- Exchange red with blue and reddish with bluish throughout a matching-cut coloring. -/
def swapSides : MatchingCutColoring G where
  color v := (C.color v).swap
  subcubic := C.subcubic
  matching := C.isMatchingColoring_swap
  color_correct := by
    intro v
    exact (C.hasGraphColor_swap v (C.color v)).2 (C.color_correct v)

@[simp] theorem swapSides_color (v : V) : C.swapSides.color v = (C.color v).swap := rfl

@[simp] theorem swapSides_swapSides : C.swapSides.swapSides = C := by
  cases C
  simp [swapSides]

end MatchingCutColoring

/-- A cut preserver is a red--blue edge. -/
def IsCutPreserver [Fintype V] {G : SimpleGraph V}
    (C : MatchingCutColoring G) (a b : V) : Prop :=
  G.Adj a b ∧ C.color a = .red ∧ C.color b = .blue

/-- Under side-swap, a cut preserver is read with its endpoints reversed. -/
@[simp] theorem isCutPreserver_swap_reverse [Fintype V] {G : SimpleGraph V}
    (C : MatchingCutColoring G) (a b : V) :
    IsCutPreserver C.swapSides b a ↔ IsCutPreserver C a b := by
  constructor
  · rintro ⟨hba, hb, ha⟩
    change (C.color b).swap = .red at hb
    change (C.color a).swap = .blue at ha
    exact ⟨(G.adj_comm b a).mp hba, (Color.swap_eq_blue _).1 ha,
      (Color.swap_eq_red _).1 hb⟩
  · rintro ⟨hab, ha, hb⟩
    refine ⟨(G.adj_comm a b).mp hab, ?_, ?_⟩
    · change (C.color b).swap = .red
      exact (Color.swap_eq_red _).2 hb
    · change (C.color a).swap = .blue
      exact (Color.swap_eq_blue _).2 ha

/-- There are at least two distinct edges with one endpoint in `S` and one in
`T`. Since `SimpleGraph` has no parallel edges, "multiple edges between two
sets" means multiple distinct endpoint pairs. -/
def HasMultipleEdgesBetween (G : SimpleGraph V) (S T : Set V) : Prop :=
  ∃ x₁ ∈ S, ∃ y₁ ∈ T, ∃ x₂ ∈ S, ∃ y₂ ∈ T,
    G.Adj x₁ y₁ ∧ G.Adj x₂ y₂ ∧ (x₁, y₁) ≠ (x₂, y₂)

/-- The number of edges between the two displayed two-vertex sets
`{a, b}` and `{c, d}`.  In the applications below the four vertices are
distinct, so these are exactly the four possible crossing edges. -/
noncomputable def fourVertexCrossEdgeCount
    (G : SimpleGraph V) (a b c d : V) : Nat := by
  classical
  exact
    (if G.Adj a c then 1 else 0) +
    (if G.Adj a d then 1 else 0) +
    (if G.Adj b c then 1 else 0) +
    (if G.Adj b d then 1 else 0)

/-- The number of edges from the two displayed vertices `a,b` into `S`.
An edge is counted once for each of its endpoints in `{a,b}`; in applications
the color assumptions ensure that neither `a` nor `b` belongs to `S`. -/
noncomputable def edgeCountFromPairToSet [Fintype V]
    (G : SimpleGraph V) (a b : V) (S : Set V) : Nat :=
  (G.neighborSet a ∩ S).ncard + (G.neighborSet b ∩ S).ncard

end Subcubic
