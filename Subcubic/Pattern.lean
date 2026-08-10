import Subcubic.ColoringLemmas

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
  /-- Optional ambient-degree requirements.  These are needed for shortened
  patterns whose drawing alone does not record that an omitted neighbor is
  genuinely absent. -/
  ambientDegree : Fin vertexCount → Option Nat := fun _ => none

namespace ColoredPattern

variable {V : Type*} [Fintype V] {G : SimpleGraph V} (P : ColoredPattern)

/-- Reverse the roles of the two color-sides in a pattern. Its vertices and
graph stay fixed; only its colors are swapped. -/
def swapSides : ColoredPattern where
  vertexCount := P.vertexCount
  graph := P.graph
  color i := (P.color i).swap
  ambientDegree := P.ambientDegree

@[simp] theorem swapSides_swapSides : P.swapSides.swapSides = P := by
  cases P
  simp [swapSides]

/-- `P` occurs as an induced colored subgraph of the ambient good coloring. -/
def OccursInduced (C : GoodColoring G) : Prop :=
  ∃ f : Fin P.vertexCount → V,
    Function.Injective f ∧
    (∀ x y, P.graph.Adj x y ↔ G.Adj (f x) (f y)) ∧
    (∀ x, C.color (f x) = P.color x) ∧
    (∀ x d, P.ambientDegree x = some d → vertexDegree G (f x) = d)

/-- A pattern vertex is saturated when it has three displayed neighbors and
its color forces ambient degree three. -/
def SaturatedAt (x : Fin P.vertexCount) : Prop :=
  (P.color x = .red ∨ P.color x = .blue) ∧
    ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      P.graph.Adj x a ∧ P.graph.Adj x b ∧ P.graph.Adj x c

/-- Two pattern vertices lie on the same side of the encoded cut. -/
def OnSameSide (x y : Fin P.vertexCount) : Prop :=
  (P.color x).IsRedSide ↔ (P.color y).IsRedSide

/-- Reasons why a missing pattern edge is already forced to be missing in
the ambient graph. A nonedge is automatic if one endpoint is saturated, or
if both endpoints lie on the same matching-cut side. -/
def AutomaticallyForcesNonedge (x y : Fin P.vertexCount) : Prop :=
  P.SaturatedAt x ∨ P.SaturatedAt y ∨
    (P.OnSameSide x y ∧
      (P.color x = .reddish ∨ P.color x = .bluish ∨
        ∃ z, z ≠ y ∧ P.graph.Adj x z ∧ P.OnSameSide x z))

instance [DecidableRel P.graph.Adj] (x : Fin P.vertexCount) :
    Decidable (P.SaturatedAt x) := by
  unfold SaturatedAt
  infer_instance

instance (x y : Fin P.vertexCount) : Decidable (P.OnSameSide x y) := by
  cases hx : P.color x <;> cases hy : P.color y <;>
    simp only [OnSameSide, Color.IsRedSide, hx, hy]
  all_goals infer_instance

instance [DecidableRel P.graph.Adj] (x y : Fin P.vertexCount) :
    Decidable (P.AutomaticallyForcesNonedge x y) := by
  unfold AutomaticallyForcesNonedge
  infer_instance

/-- Construct an induced occurrence from an injective, edge- and
color-preserving embedding. Degree saturation and the matching-cut condition
prove the automatic nonedges; `hboundary` supplies only the remaining
cross-side nonedges. -/
theorem occursInduced_of_embedding_with_degrees
    (C : GoodColoring G)
    (f : Fin P.vertexCount → V)
    (hinj : Function.Injective f)
    (hedge : ∀ {x y}, P.graph.Adj x y → G.Adj (f x) (f y))
    (hcolor : ∀ x, C.color (f x) = P.color x)
    (hboundary : ∀ x y, x ≠ y → ¬ P.graph.Adj x y →
      ¬ P.AutomaticallyForcesNonedge x y → ¬ G.Adj (f x) (f y))
    (hdegree : ∀ x d, P.ambientDegree x = some d →
      vertexDegree G (f x) = d) :
    P.OccursInduced C := by
  refine ⟨f, hinj, ?_, hcolor, hdegree⟩
  intro x y
  constructor
  · exact hedge
  · intro hxy
    by_cases hne : x = y
    · subst y
      exact (G.loopless.irrefl _ hxy).elim
    by_contra hpattern
    have mem_side_iff (i : Fin P.vertexCount) :
        f i ∈ C.redSide ↔ (P.color i).IsRedSide := by
      rw [C.mem_redSide_iff, hcolor i]
      cases P.color i <;> simp [Color.IsRedSide]
    by_cases hauto : P.AutomaticallyForcesNonedge x y
    · rcases hauto with hsat | hsat | hside
      · rcases hsat with ⟨hxcolor, a, b, c, hab, hac, hbc,
          hxa, hxb, hxc⟩
        have hya : y ≠ a := fun h => by subst a; exact hpattern hxa
        have hyb : y ≠ b := fun h => by subst b; exact hpattern hxb
        have hyc : y ≠ c := fun h => by subst c; exact hpattern hxc
        exact (C.not_adj_fourth_neighbor
          (by simpa [hcolor x] using hxcolor)
          (hedge hxa) (hedge hxb) (hedge hxc)
          (hinj.ne hab) (hinj.ne hac) (hinj.ne hbc)
          (hinj.ne hya) (hinj.ne hyb) (hinj.ne hyc)) hxy
      · rcases hsat with ⟨hycolor, a, b, c, hab, hac, hbc,
          hya, hyb, hyc⟩
        have hxa : x ≠ a := fun h => by subst a; exact hpattern hya.symm
        have hxb : x ≠ b := fun h => by subst b; exact hpattern hyb.symm
        have hxc : x ≠ c := fun h => by subst c; exact hpattern hyc.symm
        exact (C.not_adj_fourth_neighbor
          (by simpa [hcolor y] using hycolor)
          (hedge hya) (hedge hyb) (hedge hyc)
          (hinj.ne hab) (hinj.ne hac) (hinj.ne hbc)
          (hinj.ne hxa) (hinj.ne hxb) (hinj.ne hxc)) hxy.symm
      · rcases hside with ⟨hxySide, hrest⟩
        rcases hrest with hquiet | hrest
        · have hxquiet : C.color (f x) = .reddish := by
            rw [hcolor x, hquiet]
          have hymem : f y ∈ C.redSide :=
            (mem_side_iff y).2 (hxySide.mp (by
              simp [hquiet, Color.IsRedSide]))
          exact (C.reddish_not_adj_redSide hxquiet
            ((C.mem_redSide_iff _).1 hymem)) hxy
        · rcases hrest with hquiet | ⟨z, hzy, hxz, hxzSide⟩
          · have hxquiet : C.color (f x) = .bluish := by
              rw [hcolor x, hquiet]
            have hxblue : ¬ (P.color x).IsRedSide := by
              simp [hquiet, Color.IsRedSide]
            have hyblue : ¬ (P.color y).IsRedSide := fun hy =>
              hxblue (hxySide.mpr hy)
            have hymem : f y ∉ C.redSide := fun hy =>
              hyblue ((mem_side_iff y).1 hy)
            exact (C.bluish_not_adj_blueSide hxquiet
              ((C.not_mem_redSide_iff _).1 hymem)) hxy
          · by_cases hxred : (P.color x).IsRedSide
            · have hxmem : f x ∈ C.redSide := (mem_side_iff x).2 hxred
              have hymem : f y ∈ C.redSide :=
                (mem_side_iff y).2 (hxySide.mp hxred)
              have hzmem : f z ∈ C.redSide :=
                (mem_side_iff z).2 (hxzSide.mp hxred)
              exact (C.redSide_not_adj_second_neighbor hxmem hzmem hymem
                (hedge hxz) (hinj.ne hzy)) hxy
            · have hxmem : f x ∉ C.redSide := fun hx =>
                hxred ((mem_side_iff x).1 hx)
              have hyblue : ¬ (P.color y).IsRedSide := by
                intro hy
                exact hxred (hxySide.mpr hy)
              have hymem : f y ∉ C.redSide := fun hy =>
                hyblue ((mem_side_iff y).1 hy)
              have hzblue : ¬ (P.color z).IsRedSide := by
                intro hz
                exact hxred (hxzSide.mpr hz)
              have hzmem : f z ∉ C.redSide := fun hz =>
                hzblue ((mem_side_iff z).1 hz)
              exact (C.blueSide_not_adj_second_neighbor hxmem hzmem hymem
                (hedge hxz) (hinj.ne hzy)) hxy
    · exact hboundary x y hne hpattern hauto hxy

/-- The common constructor for patterns without ambient-degree requirements.
Degree-sensitive catalogue entries use `occursInduced_of_embedding_with_degrees`
instead. Keeping the two APIs separate makes the ordinary witnesses small and
fast to elaborate. -/
theorem occursInduced_of_embedding
    (C : GoodColoring G)
    (f : Fin P.vertexCount → V)
    (hinj : Function.Injective f)
    (hedge : ∀ {x y}, P.graph.Adj x y → G.Adj (f x) (f y))
    (hcolor : ∀ x, C.color (f x) = P.color x)
    (hboundary : ∀ x y, x ≠ y → ¬ P.graph.Adj x y →
      ¬ P.AutomaticallyForcesNonedge x y → ¬ G.Adj (f x) (f y))
    (hdegreeNone : ∀ x, P.ambientDegree x = none := by native_decide) :
    P.OccursInduced C := by
  apply P.occursInduced_of_embedding_with_degrees C f hinj hedge hcolor hboundary
  intro x d hdegree
  rw [hdegreeNone x] at hdegree
  contradiction

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
  · rintro ⟨f, hf, hedge, hcolor, hdegree⟩
    refine ⟨f, hf, ?_, ?_, ?_⟩
    · simpa [swapSides] using hedge
    · intro x
      have := congrArg Color.swap (hcolor x)
      simpa [swapSides] using this
    · simpa [swapSides] using hdegree
  · rintro ⟨f, hf, hedge, hcolor, hdegree⟩
    refine ⟨f, hf, ?_, ?_, ?_⟩
    · simpa [swapSides] using hedge
    · intro x
      have := congrArg Color.swap (hcolor x)
      simpa [swapSides] using this
    · simpa [swapSides] using hdegree

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
  ambientDegree : List (Fin vertexCount × Nat) := []

namespace PatternData

/-- Every edge listed in `D` is sent to an ambient edge.  This is the compact
input used by generated occurrence proofs: callers check the edge list once,
rather than considering every ordered pair of pattern vertices. -/
def EdgesMapTo (D : PatternData) {V : Type*} (G : SimpleGraph V)
    (f : Fin D.vertexCount → V) : Prop :=
  ∀ e ∈ D.edges, G.Adj (f e.1) (f e.2)

/-- Mapping the explicit edge list to ambient edges preserves all adjacency
of the graph generated by that list. -/
theorem adj_map_of_edgesMapTo (D : PatternData) {V : Type*}
    (G : SimpleGraph V) (f : Fin D.vertexCount → V)
    (h : D.EdgesMapTo G f) {x y : Fin D.vertexCount}
    (hxy : (graphOfEdges D.edges).Adj x y) : G.Adj (f x) (f y) := by
  rcases hxy with ⟨_, hxy | hyx⟩
  · exact h (x, y) hxy
  · exact (h (y, x) hyx).symm

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
  ambientDegree i := D.ambientDegree.lookup i

end PatternData

end Subcubic
