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

end Subcubic
