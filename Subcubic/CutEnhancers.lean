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

/-- Exact constructor for cut enhancer `b`. -/
theorem containsCutEnhancerB_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .reddish) (hb : C.color b = .blue)
    (hc : C.color c = .red) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (hab : G.Adj a b) (had : G.Adj a d)
    (hbc : G.Adj b c) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e) :
    ContainsCutEnhancer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hab_ne := hab.ne
    have had_ne := had.ne
    have hbc_ne := hbc.ne
    have hde_ne := hde.ne
    have hac_ne : a ≠ c := by intro h; subst c; simp_all
    have hae_ne : a ≠ e := by intro h; subst e; simp_all
    have hbd_ne : b ≠ d := by intro h; subst d; simp_all
    have hbe_ne : b ≠ e := by intro h; subst e; simp_all
    have hcd_ne : c ≠ d := by intro h; subst d; simp_all
    have hce_ne : c ≠ e := by intro h; subst e; simp_all
    simp [hab_ne, hac_ne, had_ne, hae_ne, hbc_ne, hbd_ne, hbe_ne,
      hcd_ne, hce_ne, hde_ne]
  refine ⟨cutEnhancer .b, ⟨.b, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hab, had, hbc, hde,
        hac, hae, hbd, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]

/-- Exact constructor for cut enhancer `c`. -/
theorem containsCutEnhancerC_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .bluish)
    (he : C.color e = .red)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbd : G.Adj b d) (hde : G.Adj d e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hbc : ¬ G.Adj b c) (hbe : ¬ G.Adj b e)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (habV : a ≠ b) (haeV : a ≠ e) (hbeV : b ≠ e) :
    ContainsCutEnhancer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hac_ne := hac.ne
    have had_ne := had.ne
    have hbd_ne := hbd.ne
    have hde_ne := hde.ne
    have hab_ne : a ≠ b := habV
    have hae_ne : a ≠ e := haeV
    have hbc_ne : b ≠ c := by intro h; subst c; simp_all
    have hbe_ne : b ≠ e := hbeV
    have hcd_ne : c ≠ d := by intro h; subst d; simp_all
    have hce_ne : c ≠ e := by intro h; subst e; simp_all
    simp [hab_ne, hac_ne, had_ne, hae_ne, hbc_ne, hbd_ne, hbe_ne,
      hcd_ne, hce_ne, hde_ne]
  refine ⟨cutEnhancer .c, ⟨.c, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hac, had, hbd, hde,
        hab, hae, hbc, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]

end Subcubic
