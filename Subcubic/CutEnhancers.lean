import Subcubic.Pattern
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Cut enhancers

The drawing coordinates from the TikZ source play no role here. Vertices
`0, 1, ...` represent `a, b, ...`; the edge lists come only from `\drawe`, and
the colors come only from the corresponding node declarations.
-/

open Set

namespace Subcubic

/-- Names of the seven supplied cut enhancers. -/
inductive CutEnhancerName
  | a | b | c | d | e | f | g
  deriving DecidableEq, Repr

/-- The seven cut enhancers, with their edges and colors written explicitly. -/
def cutEnhancer : CutEnhancerName → ColoredPattern
  | .a => {
      vertexCount := 3
      graph := graphOfEdges [(0, 1), (0, 2)]
      color := ![.red, .blue, .blue] }
  | .b => {
      vertexCount := 5
      graph := graphOfEdges [(0, 1), (0, 3), (1, 2), (3, 4)]
      color := ![.reddish, .blue, .red, .blue, .red] }
  | .c => {
      vertexCount := 5
      graph := graphOfEdges [(0, 2), (0, 3), (1, 3), (3, 4)]
      color := ![.red, .red, .blue, .bluish, .red] }
  | .d => {
      vertexCount := 5
      graph := graphOfEdges [(0, 2), (0, 3), (1, 2), (1, 3), (3, 4)]
      color := ![.red, .reddish, .blue, .bluish, .red] }
  | .e => {
      vertexCount := 7
      graph := graphOfEdges [(0, 4), (1, 4), (1, 6), (2, 4), (2, 5), (3, 5), (3, 6)]
      color := ![.red, .reddish, .red, .reddish, .bluish, .blue, .blue] }
  | .f => {
      vertexCount := 7
      graph := graphOfEdges [(0, 4), (1, 4), (1, 5), (2, 5), (2, 6), (3, 6)]
      color := ![.red, .reddish, .reddish, .red, .blue, .blue, .blue] }
  | .g => {
      vertexCount := 7
      graph := graphOfEdges [(0, 4), (1, 4), (2, 4), (2, 5), (2, 6), (3, 6)]
      color := ![.red, .red, .reddish, .red, .bluish, .blue, .blue] }

/-- Every supplied cut enhancer graph is subcubic. -/
theorem cutEnhancer_subcubic (name : CutEnhancerName) :
    IsSubcubic (cutEnhancer name).graph := by
  cases name <;>
    change IsSubcubic (graphOfEdges _) <;>
    intro v <;>
    unfold vertexDegree <;>
    rw [Set.ncard_eq_toFinset_card'] <;>
    native_decide +revert

/-- Membership in the complete seven-element cut-enhancer catalog. -/
def IsCutEnhancer (P : ColoredPattern) : Prop :=
  ∃ name, P = cutEnhancer name

theorem IsCutEnhancer.subcubic {P : ColoredPattern}
    (hP : IsCutEnhancer P) : IsSubcubic P.graph := by
  obtain ⟨name, rfl⟩ := hP
  exact cutEnhancer_subcubic name

/-- The colored graph contains an induced cut enhancer in the catalog's
displayed orientation. -/
def ContainsOrientedCutEnhancer {V : Type*}
    [Fintype V] {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ∃ P, IsCutEnhancer P ∧ P.OccursInduced C

/-- The colored graph contains an induced copy of a supplied cut enhancer,
possibly after exchanging `A` with `B` and hence red with blue. -/
def ContainsCutEnhancer {V : Type*} [Fintype V]
    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ContainsInducedUpToSwap IsCutEnhancer C

/-! Named facts for the first enhancer make its interpretation explicit. -/

@[simp] theorem cutEnhancerA_adj_ab :
    (cutEnhancer .a).graph.Adj ⟨0, by native_decide⟩ ⟨1, by native_decide⟩ := by
  change (graphOfEdges [(0, 1), (0, 2)]).Adj _ _
  native_decide

@[simp] theorem cutEnhancerA_adj_ac :
    (cutEnhancer .a).graph.Adj ⟨0, by native_decide⟩ ⟨2, by native_decide⟩ := by
  change (graphOfEdges [(0, 1), (0, 2)]).Adj _ _
  native_decide

@[simp] theorem cutEnhancerA_not_adj_bc :
    ¬ (cutEnhancer .a).graph.Adj ⟨1, by native_decide⟩ ⟨2, by native_decide⟩ := by
  change ¬ (graphOfEdges [(0, 1), (0, 2)]).Adj _ _
  native_decide

@[simp] theorem cutEnhancerA_color_a :
    (cutEnhancer .a).color ⟨0, by native_decide⟩ = .red := by
  native_decide

@[simp] theorem cutEnhancerA_color_b :
    (cutEnhancer .a).color ⟨1, by native_decide⟩ = .blue := by
  native_decide

@[simp] theorem cutEnhancerA_color_c :
    (cutEnhancer .a).color ⟨2, by native_decide⟩ = .blue := by
  native_decide

@[simp] theorem cutEnhancerA_swapped_color_a :
    (cutEnhancer .a).swapSides.color ⟨0, by native_decide⟩ = .blue := by
  native_decide

@[simp] theorem cutEnhancerA_swapped_color_b :
    (cutEnhancer .a).swapSides.color ⟨1, by native_decide⟩ = .red := by
  native_decide

/-- Three vertices with colors red, blue, blue and exactly the two edges from
the red vertex induce cut enhancer `a`.  This is the standard constructor used
whenever a red vertex has two nonadjacent blue neighbors. -/
theorem containsCutEnhancerA_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c : V}
    (ha : C.color a = .red) (hb : C.color b = .blue)
    (hc : C.color c = .blue) (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc_vertices : b ≠ c) (hbc : ¬ G.Adj b c) : ContainsCutEnhancer C := by
  have hab_ne : a ≠ b := hab.ne
  have hac_ne : a ≠ c := hac.ne
  refine ⟨cutEnhancer .a, ⟨.a, rfl⟩, Or.inl ?_⟩
  refine ⟨![a, b, c], ?_, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · change a = b at hxy; exact (hab_ne hxy).elim
    · change a = c at hxy; exact (hac_ne hxy).elim
    · change b = a at hxy; exact (hab_ne hxy.symm).elim
    · rfl
    · change b = c at hxy; exact (hbc_vertices hxy).elim
    · change c = a at hxy; exact (hac_ne hxy.symm).elim
    · change c = b at hxy; exact (hbc_vertices hxy.symm).elim
    · rfl
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hab, hac, hbc]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc]

end Subcubic
