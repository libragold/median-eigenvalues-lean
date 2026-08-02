import Subcubic.TailReducers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Small negative-tail-reducer witnesses

These constructors list ambient vertices in the catalog order.  The catalog's
generated saturation checks discharge every forced nonedge; the hypotheses of
`containsNegativeM` and `containsNegativeN` are precisely their remaining
boundary nonedges.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Negative reducer `a1-`, in catalog order. -/
theorem containsNegativeA1
    (C : GoodColoring G) {a b c : V}
    (ha : C.color a = .red) (hb : C.color b = .blue)
    (hc : C.color c = .blue)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hn : [a, b, c].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .a1, ⟨.a1, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .a1).occursInduced_of_embedding C
    ([a, b, c].get) hn.injective_get
  · intro x y hxy
    fin_cases x <;> fin_cases y <;>
      simp [negativeTailReducer, negativeTailReducerData,
        PatternData.toPattern, graphOfEdges] at hxy ⊢
    all_goals first | exact hab | exact hab.symm | exact hac |
      exact hac.symm | exact hbc | exact hbc.symm
  · intro x
    have hcolors : (negativeTailReducer .a1).color =
        ![.red, .blue, .blue] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeA1_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `f-`, in catalog order. -/
theorem containsNegativeF
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .blue)
    (he : C.color e = .blue) (hf : C.color f = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbe : G.Adj b e) (hbf : G.Adj b f) (hde : G.Adj d e)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .f, ⟨.f, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .f).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .f).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .f).color =
        ![.red, .red, .bluish, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeF_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `k-`, in catalog order. -/
theorem containsNegativeK
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish) (hd : C.color d = .blue)
    (he : C.color e = .blue) (hf : C.color f = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d) (hce : G.Adj c e) (hcf : G.Adj c f)
    (hde : G.Adj d e)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .k, ⟨.k, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .k).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .k).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 3), (2, 4), (2, 5), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .k).color =
        ![.red, .red, .reddish, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeK_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `m-`, in catalog order. -/
theorem containsNegativeM
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .blue)
    (he : C.color e = .blue) (hf : C.color f = .bluish)
    (hg : C.color g = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hde : G.Adj d e)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f, g].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .m, ⟨.m, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .m).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .m).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 5), (2, 6), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .m).color =
        ![.red, .red, .red, .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeM_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- Negative reducer `n-`, in catalog order. -/
theorem containsNegativeN
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish) (hd : C.color d = .blue)
    (he : C.color e = .blue) (hf : C.color f = .bluish)
    (hg : C.color g = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d) (hce : G.Adj c e) (hcg : G.Adj c g)
    (hde : G.Adj d e) (hcf : ¬ G.Adj c f)
    (hn : [a, b, c, d, e, f, g].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .n, ⟨.n, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .n).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .n).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 3), (2, 4), (2, 6), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .n).color =
        ![.red, .red, .reddish, .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeN_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcf
    · exact fun h => hcf h.symm

/-- Negative reducer `a0-`, in catalog order. -/
theorem containsNegativeA0
    (C : GoodColoring G) {a b c : V}
    (ha : C.color a = .reddish) (hb : C.color b = .blue)
    (hc : C.color c = .blue)
    (haDegree : vertexDegree G a = 2)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hn : [a, b, c].Nodup) : ContainsNegativeTailReducer C := by
  -- As for `m-minus+`, this ambient condition rules out an unlisted third
  -- neighbor of the distinguished reddish vertex.
  have _haDegree := haDegree
  refine ⟨negativeTailReducer .a0, ⟨.a0, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .a0).occursInduced_of_embedding C
    ([a, b, c].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .a0).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 2), (1, 2)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .a0).color =
        ![.reddish, .blue, .blue] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeA0_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `c-`, in catalog order. -/
theorem containsNegativeC
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hn : [a, b, c, d].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .c, ⟨.c, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .c).occursInduced_of_embedding C
    ([a, b, c, d].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .c).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .c).color =
        ![.red, .red, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeC_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `g-`, in catalog order. -/
theorem containsNegativeG
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .g, ⟨.g, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .g).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .g).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 2), (0, 3), (1, 4), (1, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .g).color =
        ![.red, .red, .bluish, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hnot
    exact (hnot (negativeG_automaticNonedges x y hne hnon)).elim

/-- Negative reducer `b-`, in catalog order. -/
theorem containsNegativeB
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hab : ¬ G.Adj a b) (hn : [a, b, c, d].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .b, ⟨.b, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .b).occursInduced_of_embedding C
    ([a, b, c, d].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .b).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 2), (1, 3)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .b).color =
        ![.red, .red, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeB_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact fun h => hab h.symm

/-- Negative reducer `d-`, in catalog order. -/
theorem containsNegativeD
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hbc : ¬ G.Adj b c) (hn : [a, b, c, d, e].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .d, ⟨.d, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .d).occursInduced_of_embedding C
    ([a, b, c, d, e].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .d).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 3), (1, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .d).color =
        ![.red, .red, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeD_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hab
    · exact hae
    · exact hbc
    · exact fun h => hab h.symm
    · exact fun h => hae h.symm
    · exact fun h => hbc h.symm

/-- Negative reducer `e-`, in catalog order. -/
theorem containsNegativeE
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hn : [a, b, c, d, e].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .e, ⟨.e, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .e).occursInduced_of_embedding C
    ([a, b, c, d, e].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .e).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 2), (1, 3), (1, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .e).color =
        ![.red, .reddish, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeE_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hab
    · exact hae
    · exact fun h => hab h.symm
    · exact fun h => hae h.symm

/-- Short reddish version `e0-minus-`; the distinguished reddish vertex has
ambient degree two, so the omitted fifth vertex is genuinely absent. -/
theorem containsNegativeE0Minus
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hbDegree : vertexDegree G b = 2)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hab : ¬ G.Adj a b) (hn : [a, b, c, d].Nodup) :
    ContainsNegativeTailReducer C := by
  have _hbDegree := hbDegree
  refine ⟨negativeTailReducer .e0Minus, ⟨.e0Minus, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .e0Minus).occursInduced_of_embedding C
    ([a, b, c, d].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .e0Minus).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 2), (1, 3)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .e0Minus).color =
        ![.red, .reddish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeE0Minus_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact fun h => hab h.symm

/-- Short red version `e1-minus-`; the red mate is outside the displayed
induced subgraph. -/
theorem containsNegativeE1Minus
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d)
    (hab : ¬ G.Adj a b) (hn : [a, b, c, d].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .e1Minus, ⟨.e1Minus, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .e1Minus).occursInduced_of_embedding C
    ([a, b, c, d].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .e1Minus).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 2), (1, 3)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .e1Minus).color =
        ![.red, .red, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeE1Minus_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact fun h => hab h.symm

/-- Negative reducer `h-`, in catalog order. -/
theorem containsNegativeH
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hac : G.Adj a c) (had : G.Adj a d) (hbd : G.Adj b d)
    (hbe : G.Adj b e) (hbf : G.Adj b f) (hef : G.Adj e f)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (haf : ¬ G.Adj a f) (hbc : ¬ G.Adj b c)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .h, ⟨.h, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .h).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .h).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 3), (1, 4), (1, 5), (4, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .h).color =
        ![.red, .reddish, .bluish, .bluish, .blue, .blue] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeH_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hab
    · exact hae
    · exact haf
    · exact hbc
    · exact fun h => hab h.symm
    · exact fun h => hae h.symm
    · exact fun h => haf h.symm
    · exact fun h => hbc h.symm

/-- Negative reducer `s-`, in catalog order. -/
theorem containsNegativeS
    (C : GoodColoring G) {a b c d e f g h : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish) (hg : C.color g = .bluish)
    (hh : C.color h = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hch : G.Adj c h)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f, g, h].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .s, ⟨.s, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .s).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .s).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 5), (2, 6), (2, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .s).color =
        ![.red, .red, .reddish, .bluish, .bluish, .bluish,
          .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeS_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- `s0-minus-`: `s-` with `h` removed and reddish `c` of ambient degree two. -/
theorem containsNegativeS0Minus
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish) (hg : C.color g = .bluish)
    (hcDegree : vertexDegree G c = 2)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcf : G.Adj c f) (hcg : G.Adj c g)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f, g].Nodup) :
    ContainsNegativeTailReducer C := by
  have _hcDegree := hcDegree
  refine ⟨negativeTailReducer .s0Minus, ⟨.s0Minus, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .s0Minus).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .s0Minus).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 5), (2, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .s0Minus).color =
        ![.red, .red, .reddish, .bluish, .bluish, .bluish, .bluish] := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeS0Minus_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- `s1-minus-`: `s-` with `h` removed and red `c`. -/
theorem containsNegativeS1Minus
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish) (hg : C.color g = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcf : G.Adj c f) (hcg : G.Adj c g)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f, g].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .s1Minus, ⟨.s1Minus, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .s1Minus).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .s1Minus).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5),
      (2, 5), (2, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .s1Minus).color =
        ![.red, .red, .red, .bluish, .bluish, .bluish, .bluish] := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeS1Minus_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- `s0-minus2-`: `s-` with `g,h` removed and reddish `c` of ambient degree one. -/
theorem containsNegativeS0Minus2
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish)
    (hcDegree : vertexDegree G c = 1)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f) (hcf : G.Adj c f)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f].Nodup) :
    ContainsNegativeTailReducer C := by
  have _hcDegree := hcDegree
  refine ⟨negativeTailReducer .s0Minus2, ⟨.s0Minus2, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .s0Minus2).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .s0Minus2).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5), (2, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .s0Minus2).color =
        ![.red, .red, .reddish, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeS0Minus2_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- `s1-minus2-`: `s-` with `g,h` removed and red `c`. -/
theorem containsNegativeS1Minus2
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbf : G.Adj b f) (hcf : G.Adj c f)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hn : [a, b, c, d, e, f].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .s1Minus2, ⟨.s1Minus2, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .s1Minus2).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .s1Minus2).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 4), (1, 5), (2, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .s1Minus2).color =
        ![.red, .red, .red, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeS1Minus2_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm

/-- Negative reducer `y-`, in catalog order. -/
theorem containsNegativeY
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .red)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish) (hg : C.color g = .blue)
    (hh : C.color h = .blue) (hi : C.color i = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e)
    (hbe : G.Adj b e) (hbf : G.Adj b f) (hbg : G.Adj b g)
    (hcg : G.Adj c g) (hci : G.Adj c i) (hgh : G.Adj g h)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (haf : ¬ G.Adj a f) (hah : ¬ G.Adj a h) (hai : ¬ G.Adj a i)
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d)
    (hbh : ¬ G.Adj b h) (hbi : ¬ G.Adj b i)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hcf : ¬ G.Adj c f) (hch : ¬ G.Adj c h)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .y, ⟨.y, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .y).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .y).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (1, 4), (1, 5),
      (1, 6), (2, 6), (2, 8), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .y).color =
        ![.red, .reddish, .red, .bluish, .bluish, .bluish,
          .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeY_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩)
    · exact hab
    · exact hac
    · exact haf
    · exact hah
    · exact hai
    · exact hbc
    · exact hbd
    · exact hbh
    · exact hbi
    · exact hcd
    · exact hce
    · exact hcf
    · exact hch
    · exact fun h => hab h.symm
    · exact fun h => hac h.symm
    · exact fun h => haf h.symm
    · exact fun h => hah h.symm
    · exact fun h => hai h.symm
    · exact fun h => hbc h.symm
    · exact fun h => hbd h.symm
    · exact fun h => hbh h.symm
    · exact fun h => hbi h.symm
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm
    · exact fun h => hcf h.symm
    · exact fun h => hch h.symm

/-! Witnesses used by the induced-pentagon argument (Lemma 5.5). -/

/-- Negative reducer `i-`, in catalog order. -/
theorem containsNegativeI
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .reddish)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (haf : ¬ G.Adj a f) (hbc : ¬ G.Adj b c)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .i, ⟨.i, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .i).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .i).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (1, 3), (1, 4), (1, 5), (2, 3)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .i).color =
        ![.red, .reddish, .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeI_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hab
    · exact hac
    · exact haf
    · exact hbc
    · exact fun h => hab h.symm
    · exact fun h => hac h.symm
    · exact fun h => haf h.symm
    · exact fun h => hbc h.symm

/-- Negative reducer `r-`, in catalog order. -/
theorem containsNegativeR
    (C : GoodColoring G) {a b c d e f g h : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .blue) (hg : C.color g = .blue)
    (hh : C.color h = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (hae : G.Adj a e)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d) (hcf : G.Adj c f) (hch : G.Adj c h)
    (hfg : G.Adj f g)
    (hce : ¬ G.Adj c e) (hcg : ¬ G.Adj c g)
    (hn : [a, b, c, d, e, f, g, h].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .r, ⟨.r, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .r).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .r).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 4), (1, 4), (1, 5),
      (2, 3), (2, 5), (2, 7), (5, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .r).color =
        ![.red, .red, .reddish, .bluish, .bluish, .blue, .blue, .bluish] := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeR_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hce
    · exact hcg
    · exact fun h => hce h.symm
    · exact fun h => hcg h.symm

/-- Negative reducer `t-`, in catalog order. -/
theorem containsNegativeT
    (C : GoodColoring G) {a b c d e f g h : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .blue) (hg : C.color g = .blue)
    (hh : C.color h = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (hah : G.Adj a h)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d) (hcf : G.Adj c f) (hch : G.Adj c h)
    (hfg : G.Adj f g)
    (hce : ¬ G.Adj c e) (hcg : ¬ G.Adj c g)
    (hn : [a, b, c, d, e, f, g, h].Nodup) : ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .t, ⟨.t, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .t).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .t).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 7), (1, 4), (1, 5),
      (2, 3), (2, 5), (2, 7), (5, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .t).color =
        ![.red, .red, .reddish, .bluish, .bluish, .blue, .blue, .bluish] := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeT_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hce
    · exact hcg
    · exact fun h => hce h.symm
    · exact fun h => hcg h.symm

/-- Negative reducer `z-`, in catalog order. -/
theorem containsNegativeZ
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .bluish) (hg : C.color g = .blue)
    (hh : C.color h = .blue) (hi : C.color i = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbc : G.Adj b c) (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcg : G.Adj c g) (hci : G.Adj c i) (hgh : G.Adj g h)
    (haf : ¬ G.Adj a f) (hah : ¬ G.Adj a h) (hai : ¬ G.Adj a i)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .z, ⟨.z, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .z).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .z).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 6), (1, 2), (1, 4),
      (1, 5), (2, 6), (2, 8), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .z).color =
        ![.reddish, .red, .red, .bluish, .bluish, .bluish,
          .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeZ_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact haf
    · exact hah
    · exact hai
    · exact fun h => haf h.symm
    · exact fun h => hah h.symm
    · exact fun h => hai h.symm

/-- Negative reducer `x-`, in catalog order. -/
theorem containsNegativeX
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .blue)
    (hf : C.color f = .blue) (hg : C.color g = .blue)
    (hh : C.color h = .blue) (hi : C.color i = .bluish)
    (hab : G.Adj a b) (had : G.Adj a d) (haf : G.Adj a f)
    (hbd : G.Adj b d) (hbg : G.Adj b g)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hci : G.Adj c i)
    (hef : G.Adj e f) (hgh : G.Adj g h)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e) (hch : ¬ G.Adj c h)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .x, ⟨.x, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .x).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .x).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 3), (0, 5), (1, 3), (1, 6),
      (2, 5), (2, 6), (2, 8), (4, 5), (6, 7)] at hedge
    simp at hedge
    rcases hedge with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .x).color =
        ![.red, .red, .reddish, .bluish, .blue, .blue, .blue, .blue,
          .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeX_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact hch
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm
    · exact fun h => hch h.symm

/-- Negative reducer `ae-`, in catalog order. -/
theorem containsNegativeAe
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish)
    (hd : C.color d = .bluish) (he : C.color e = .bluish)
    (hf : C.color f = .blue) (hg : C.color g = .blue)
    (hh : C.color h = .blue) (hi : C.color i = .blue)
    (hj : C.color j = .bluish)
    (hab : G.Adj a b) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbd : G.Adj b d) (hbh : G.Adj b h)
    (hcg : G.Adj c g) (hch : G.Adj c h) (hcj : G.Adj c j)
    (hfg : G.Adj f g) (hhi : G.Adj h i)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hcf : ¬ G.Adj c f) (hci : ¬ G.Adj c i)
    (hn : [a, b, c, d, e, f, g, h, i, j].Nodup) :
    ContainsNegativeTailReducer C := by
  refine ⟨negativeTailReducer .ae, ⟨.ae, rfl⟩, Or.inl ?_⟩
  apply (negativeTailReducer .ae).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j].get) hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .ae).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 1), (0, 4), (0, 6), (1, 3), (1, 7),
      (2, 6), (2, 7), (2, 9), (5, 6), (7, 8)] at hedge
    simp at hedge
    rcases hedge with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .ae).color =
        ![.red, .red, .reddish, .bluish, .bluish, .blue, .blue, .blue,
          .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;>
      simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj] <;> native_decide
  · intro x y hne hnon hauto
    have hp := negativeAe_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hce
    · exact hcf
    · exact hci
    · exact fun h => hcd h.symm
    · exact fun h => hce h.symm
    · exact fun h => hcf h.symm
    · exact fun h => hci h.symm

end Subcubic
