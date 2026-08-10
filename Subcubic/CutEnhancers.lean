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

/-- Names of the seven supplied cut enhancers and the two low-degree
enhancers used in Lemma 3.4. -/
inductive CutEnhancerName
  | a | b | c | d | e | f | g
  | degreeOne | degreeTwoCross
  deriving DecidableEq, Repr

/-- The nine cut enhancers, with their edges, colors, and any ambient-degree
guards written explicitly. -/
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
  | .degreeOne => {
      vertexCount := 1
      graph := graphOfEdges []
      color := ![.red]
      ambientDegree := ![some 1] }
  | .degreeTwoCross => {
      vertexCount := 2
      graph := graphOfEdges [(0, 1)]
      color := ![.red, .blue]
      ambientDegree := ![some 2, none] }

/-- Every supplied cut enhancer graph is subcubic. -/
theorem cutEnhancer_subcubic (name : CutEnhancerName) :
    IsSubcubic (cutEnhancer name).graph := by
  cases name <;>
    change IsSubcubic (graphOfEdges _) <;>
    intro v <;>
    unfold vertexDegree <;>
    rw [Set.ncard_eq_toFinset_card'] <;>
    native_decide +revert

/-- Membership in the complete nine-element cut-enhancer catalog. -/
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
  refine ⟨![a, b, c], ?_, ?_, ?_, ?_⟩
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
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

/-- The one-vertex cut enhancer from Lemma 3.4(1). -/
theorem containsCutEnhancerDegreeOne_of
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a : V}
    (ha : C.color a = .red) (haDegree : vertexDegree G a = 1) :
    ContainsCutEnhancer C := by
  refine ⟨cutEnhancer .degreeOne, ⟨.degreeOne, rfl⟩, Or.inl ?_⟩
  refine ⟨![a], ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    fin_cases x
    fin_cases y
    rfl
  · intro x y
    fin_cases x
    fin_cases y
    simp [cutEnhancer, graphOfEdges]
  · intro x
    fin_cases x
    simpa [cutEnhancer] using ha
  · intro x d hdegree
    fin_cases x
    have hd : d = 1 := by simpa [cutEnhancer] using hdegree.symm
    simpa [hd] using haDegree

/-- The red--blue degree-two cut enhancer from Lemma 3.4(2.1). -/
theorem containsCutEnhancerDegreeTwoCross_of
    {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .blue)
    (hab : G.Adj a b) (haDegree : vertexDegree G a = 2) :
    ContainsCutEnhancer C := by
  refine ⟨cutEnhancer .degreeTwoCross, ⟨.degreeTwoCross, rfl⟩, Or.inl ?_⟩
  refine ⟨![a, b], ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact (hab.ne hxy).elim
    · exact (hab.ne hxy.symm).elim
    · rfl
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hab]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb]
  · intro x d hdegree
    fin_cases x
    · have hd : d = 2 := by simpa [cutEnhancer] using hdegree.symm
      change vertexDegree G a = d
      simpa [hd] using haDegree
    · simp [cutEnhancer] at hdegree

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
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hab, had, hbc, hde,
        hac, hae, hbd, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

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
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hac, had, hbd, hde,
        hab, hae, hbc, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

/-- Exact constructor for cut enhancer `d`. -/
theorem containsCutEnhancerD_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .blue) (hd : C.color d = .bluish)
    (he : C.color e = .red)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hde : G.Adj d e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hbe : ¬ G.Adj b e) (hcd : ¬ G.Adj c d)
    (hce : ¬ G.Adj c e) (haeV : a ≠ e) : ContainsCutEnhancer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hacV := hac.ne
    have hadV := had.ne
    have hbcV := hbc.ne
    have hbdV := hbd.ne
    have hdeV := hde.ne
    have habV : a ≠ b := by intro h; subst b; simp_all
    have hbeV : b ≠ e := by intro h; subst e; simp_all
    have hcdV : c ≠ d := by intro h; subst d; simp_all
    have hceV : c ≠ e := by intro h; subst e; simp_all
    simp [habV, hacV, hadV, haeV, hbcV, hbdV, hbeV,
      hcdV, hceV, hdeV]
  refine ⟨cutEnhancer .d, ⟨.d, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hac, had, hbc, hbd,
        hde, hab, hae, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

/-- Exact constructor for cut enhancer `e`. -/
theorem containsCutEnhancerE_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .red) (hd : C.color d = .reddish)
    (he : C.color e = .bluish) (hf : C.color f = .blue)
    (hg : C.color g = .blue)
    (hae : G.Adj a e) (hbe : G.Adj b e) (hbg : G.Adj b g)
    (hce : G.Adj c e) (hcf : G.Adj c f)
    (hdf : G.Adj d f) (hdg : G.Adj d g)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (had : ¬ G.Adj a d) (haf : ¬ G.Adj a f)
    (hag : ¬ G.Adj a g) (hbc : ¬ G.Adj b c)
    (hbd : ¬ G.Adj b d) (hbf : ¬ G.Adj b f)
    (hcd : ¬ G.Adj c d) (hcg : ¬ G.Adj c g)
    (hde : ¬ G.Adj d e) (hef : ¬ G.Adj e f)
    (heg : ¬ G.Adj e g) (hfg : ¬ G.Adj f g)
    (hn : [a, b, c, d, e, f, g].Nodup) : ContainsCutEnhancer C := by
  refine ⟨cutEnhancer .e, ⟨.e, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e, f, g].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hae, hbe, hbg, hce, hcf,
        hdf, hdg, hab, hac, had, haf, hag, hbc, hbd, hbf, hcd, hcg, hde,
        hef, heg, hfg]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he, hf, hg]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

/-- Exact constructor for cut enhancer `f`. -/
theorem containsCutEnhancerF_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .reddish) (hd : C.color d = .red)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hg : C.color g = .blue)
    (hae : G.Adj a e) (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hdg : G.Adj d g)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (had : ¬ G.Adj a d) (haf : ¬ G.Adj a f)
    (hag : ¬ G.Adj a g) (hbc : ¬ G.Adj b c)
    (hbd : ¬ G.Adj b d) (hbg : ¬ G.Adj b g)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hde : ¬ G.Adj d e) (hdf : ¬ G.Adj d f)
    (hef : ¬ G.Adj e f) (heg : ¬ G.Adj e g)
    (hfg : ¬ G.Adj f g)
    (hn : [a, b, c, d, e, f, g].Nodup) : ContainsCutEnhancer C := by
  refine ⟨cutEnhancer .f, ⟨.f, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e, f, g].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hae, hbe, hbf, hcf,
        hcg, hdg, hab, hac, had, haf, hag, hbc, hbd, hbg, hcd, hce,
        hde, hdf, hef, heg, hfg]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he, hf, hg]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

/-- Exact constructor for cut enhancer `g`. -/
theorem containsCutEnhancerG_of {V : Type*} [Fintype V] {G : SimpleGraph V}
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish) (hd : C.color d = .red)
    (he : C.color e = .bluish) (hf : C.color f = .blue)
    (hg : C.color g = .blue)
    (hae : G.Adj a e) (hbe : G.Adj b e) (hce : G.Adj c e)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hdg : G.Adj d g)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (had : ¬ G.Adj a d) (haf : ¬ G.Adj a f)
    (hag : ¬ G.Adj a g) (hbc : ¬ G.Adj b c)
    (hbd : ¬ G.Adj b d) (hbf : ¬ G.Adj b f)
    (hbg : ¬ G.Adj b g) (hcd : ¬ G.Adj c d)
    (hde : ¬ G.Adj d e) (hdf : ¬ G.Adj d f)
    (hef : ¬ G.Adj e f) (heg : ¬ G.Adj e g)
    (hfg : ¬ G.Adj f g)
    (hn : [a, b, c, d, e, f, g].Nodup) : ContainsCutEnhancer C := by
  refine ⟨cutEnhancer .g, ⟨.g, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e, f, g].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hae, hbe, hce, hcf,
        hcg, hdg, hab, hac, had, haf, hag, hbc, hbd, hbf, hbg, hcd,
        hde, hdf, hef, heg, hfg]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he, hf, hg]
  · intro x d hdegree
    fin_cases x <;> simp [cutEnhancer] at hdegree

end Subcubic
