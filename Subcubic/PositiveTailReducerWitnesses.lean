import Subcubic.TailReducers
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Reusable witnesses for positive tail reducers

The catalog is generated from `detailed-input.txt`.  This file only
records the mathematical labellings used repeatedly in proofs.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The absolute degree-two reducer used in Lemma 3.6: a red vertex with
one displayed bluish neighbor and ambient degree two. -/
theorem containsPositiveAbs
    (C : GoodColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .bluish)
    (hab : G.Adj a b) (haDegree : vertexDegree G a = 2) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .abs, ⟨.abs, rfl⟩, Or.inl ?_⟩
  refine ⟨![a, b], ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    fin_cases x <;> fin_cases y
    · rfl
    · exact (hab.ne hxy).elim
    · exact (hab.ne hxy.symm).elim
    · rfl
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hab]
  · intro x
    fin_cases x <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        PatternData.color, ha, hb]
  · intro x d hdegree
    fin_cases x
    · change (some 2 : Option Nat) = some d at hdegree
      injection hdegree with hd
      change vertexDegree G a = d
      simpa [hd] using haDegree
    · change (none : Option Nat) = some d at hdegree
      contradiction

/-- Reducer `c+`, with its two red vertices, blue edge, and bluish vertex. -/
theorem containsPositiveC
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbe : G.Adj b e) (hcd : G.Adj c d)
    (hab : ¬ G.Adj a b) (had : ¬ G.Adj a d)
    (hbc : ¬ G.Adj b c) : ContainsPositiveTailReducer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hae_ne := hae.ne
    have hbe_ne := hbe.ne
    have hac_ne := hac.ne
    have hbd_ne := hbd.ne
    have hcd_ne := hcd.ne
    have habV : a ≠ b := by intro h; subst b; simp_all
    have hadV : a ≠ d := by intro h; subst d; simp_all
    have hbcV : b ≠ c := by intro h; subst c; simp_all
    have hceV : c ≠ e := by intro h; subst e; simp_all
    have hdeV : d ≠ e := by intro h; subst e; simp_all
    simp [habV, hac_ne, hadV, hae_ne, hbcV, hbd_ne, hbe_ne,
      hcd_ne, hceV, hdeV]
  have hce : ¬ G.Adj c e :=
    C.bluish_not_adj_blueSide he (Or.inl hc) ∘ SimpleGraph.Adj.symm
  have hde : ¬ G.Adj d e :=
    C.bluish_not_adj_blueSide he (Or.inl hd) ∘ SimpleGraph.Adj.symm
  refine ⟨positiveTailReducer .c, ⟨.c, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hac, hae, hbd, hbe, hcd,
        hab, had, hbc, hce, hde]
  · intro x
    have hcolors : (positiveTailReducer .c).color =
        ![.red, .red, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide
  · intro x d hdegree
    fin_cases x <;>
      simp [positiveTailReducer, positiveTailReducerData,
        PatternData.toPattern] at hdegree

/-- Reducer `n+`, with ambient vertices listed in catalog order. -/
theorem containsPositiveN
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .blue)
    (hg : C.color g = .blue)
    (hab : G.Adj a b) (had : G.Adj a d) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbf : G.Adj b f)
    (hce : G.Adj c e) (hcg : G.Adj c g) (hfg : G.Adj f g)
    (hcd : ¬ G.Adj c d) (hcf : ¬ G.Adj c f)
    (hn : [a, b, c, d, e, f, g].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .n, ⟨.n, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .n).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .n).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 1), (0, 3), (0, 4), (1, 3), (1, 5), (2, 4), (2, 6),
       (5, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .n).color =
        ([.red, .red, .red, .bluish, .bluish, .blue, .blue] :
          List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg]
  · intro x y hne hnon hauto
    have hp := positiveN_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hcd
    · exact hcf
    · exact fun h => hcd h.symm
    · exact fun h => hcf h.symm

/-- Reducer `x+`, with ambient vertices listed in catalog order. -/
theorem containsPositiveX
    (C : GoodColoring G) {a b c d e f g h i j k : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .reddish)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hg : C.color g = .bluish) (hh : C.color h = .blue)
    (hi : C.color i = .blue) (hj : C.color j = .blue)
    (hk : C.color k = .blue)
    (hab : G.Adj a b) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbf : G.Adj b f) (hbh : G.Adj b h)
    (hcg : G.Adj c g) (hcj : G.Adj c j)
    (hdh : G.Adj d h) (hdi : G.Adj d i) (hdk : G.Adj d k)
    (hhi : G.Adj h i) (hjk : G.Adj j k)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hcf : ¬ G.Adj c f) (hci : ¬ G.Adj c i)
    (hck : ¬ G.Adj c k) (hde : ¬ G.Adj d e)
    (hdf : ¬ G.Adj d f) (hdg : ¬ G.Adj d g)
    (hdj : ¬ G.Adj d j)
    (hn : [a, b, c, d, e, f, g, h, i, j, k].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .x, ⟨.x, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .x).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j, k].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .x).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 1), (0, 4), (0, 6), (1, 5), (1, 7), (2, 6),
       (2, 9), (3, 7), (3, 8), (3, 10), (7, 8), (9, 10)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .x).color =
        ([.red, .red, .red, .reddish, .bluish, .bluish, .bluish,
          .blue, .blue, .blue, .blue] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;>
      simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk]
  · intro x y hne hnon hauto
    have hp := positiveX_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
       ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact hcd h.symm)
      | (intro h; exact hce h.symm)
      | (intro h; exact hcf h.symm)
      | (intro h; exact hci h.symm)
      | (intro h; exact hck h.symm)
      | (intro h; exact hde h.symm)
      | (intro h; exact hdf h.symm)
      | (intro h; exact hdg h.symm)
      | (intro h; exact hdj h.symm)

/-- Reducer `m+`, in catalog order. -/
theorem containsPositiveM
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbf : G.Adj b f) (hef : G.Adj e f)
    (hab : ¬ G.Adj a b) (haf : ¬ G.Adj a f)
    (hbc : ¬ G.Adj b c) (hbe : ¬ G.Adj b e)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .m, ⟨.m, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .m).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .m).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (0, 4), (1, 3), (1, 5), (4, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .m).color =
        ([.reddish, .red, .bluish, .bluish, .blue, .blue] : List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf]
  · intro x y hne hnon hauto
    have hp := positiveM_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact hab h.symm)
      | (intro h; exact haf h.symm)
      | (intro h; exact hbc h.symm)
      | (intro h; exact hbe h.symm)

/-- Reducer `ptr-dc-a`: reducer `ptr-m` with its extra bluish vertex removed. -/
theorem containsPositiveDcA
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .bluish)
    (hd : C.color d = .blue) (he : C.color e = .blue)
    (haDegree : vertexDegree G a = 2)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbe : G.Adj b e) (hde : G.Adj d e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d)
    (hn : [a, b, c, d, e].Nodup) : ContainsPositiveTailReducer C := by
  -- This is the extra ambient requirement distinguishing `ptr-dc-a` from
  -- an arbitrary five-vertex induced copy.  In particular, `a` has no
  -- unlisted third neighbor on the opposite side of the cut.
  refine ⟨positiveTailReducer .dcA, ⟨.dcA, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .dcA).occursInduced_of_embedding_with_degrees C
    ([a, b, c, d, e].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .dcA).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 2), (1, 4), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .dcA).color =
        ([.reddish, .red, .bluish, .blue, .blue] : List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he]
  · intro x y hne hnon hauto
    have hp := positiveDcA_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact hab h.symm)
      | (intro h; exact hae h.symm)
      | (intro h; exact hbd h.symm)
  · intro x d hdegree
    fin_cases x
    · change (some 2 : Option Nat) = some d at hdegree
      injection hdegree with hd
      simpa [hd] using haDegree
    · change (none : Option Nat) = some d at hdegree
      contradiction
    · change (none : Option Nat) = some d at hdegree
      contradiction
    · change (none : Option Nat) = some d at hdegree
      contradiction
    · change (none : Option Nat) = some d at hdegree
      contradiction

/-- Reducer `l+`, in catalog order. -/
theorem containsPositiveL
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hac : G.Adj a c) (had : G.Adj a d) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbe : G.Adj b e) (hef : G.Adj e f)
    (hab : ¬ G.Adj a b) (haf : ¬ G.Adj a f)
    (hbc : ¬ G.Adj b c) (hbf : ¬ G.Adj b f)
    (hn : [a, b, c, d, e, f].Nodup) : ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .l, ⟨.l, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .l).occursInduced_of_embedding C
    ([a, b, c, d, e, f].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .l).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (0, 4), (1, 3), (1, 4), (4, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .l).color =
        ([.reddish, .red, .bluish, .bluish, .blue, .blue] : List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf]
  · intro x y hne hnon hauto
    have hp := positiveL_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact hab h.symm)
      | (intro h; exact haf h.symm)
      | (intro h; exact hbc h.symm)
      | (intro h; exact hbf h.symm)

/-- Reducer `g+`, in catalog order. -/
theorem containsPositiveG
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hab : ¬ G.Adj a b) (hae : ¬ G.Adj a e)
    (hbc : ¬ G.Adj b c) (hn : [a, b, c, d, e].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .g, ⟨.g, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .g).occursInduced_of_embedding C
    ([a, b, c, d, e].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .g).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 2), (0, 3), (1, 3), (1, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .g).color =
        ([.red, .red, .bluish, .bluish, .bluish] : List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he]
  · intro x y hne hnon hauto
    have hp := positiveG_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact hab h.symm)
      | (intro h; exact hae h.symm)
      | (intro h; exact hbc h.symm)

/-- Reducer `u+`, with its four generated boundary nonedges exposed. -/
theorem containsPositiveU
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hg : C.color g = .bluish) (hh : C.color h = .blue)
    (hi : C.color i = .blue) (hj : C.color j = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (hah : G.Adj a h)
    (hbc : G.Adj b c) (hbf : G.Adj b f) (hbg : G.Adj b g)
    (hch : G.Adj c h) (hcj : G.Adj c j) (hhi : G.Adj h i)
    (haf : ¬ G.Adj a f) (hag : ¬ G.Adj a g)
    (hai : ¬ G.Adj a i) (haj : ¬ G.Adj a j)
    (hn : [a, b, c, d, e, f, g, h, i, j].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .u, ⟨.u, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .u).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .u).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 3), (0, 4), (0, 7), (1, 2), (1, 5),
       (1, 6), (2, 7), (2, 9), (7, 8)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .u).color =
        ([.reddish, .red, .red, .bluish, .bluish, .bluish,
          .bluish, .blue, .blue, .bluish] : List Color).get := by
      native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj]
  · intro x y hne hnon hauto
    have hp := positiveU_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals simp
    all_goals first
      | assumption
      | (intro h; exact haf h.symm)
      | (intro h; exact hag h.symm)
      | (intro h; exact hai h.symm)
      | (intro h; exact haj h.symm)

/-- Reducer `p+`, in catalog order. -/
theorem containsPositiveP
    (C : GoodColoring G) {a b c d e f g h : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hg : C.color g = .bluish) (hh : C.color h = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (haf : G.Adj a f)
    (hbe : G.Adj b e) (hbg : G.Adj b g)
    (hcf : G.Adj c f) (hch : G.Adj c h) (hef : G.Adj e f)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (hag : ¬ G.Adj a g) (hah : ¬ G.Adj a h)
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d)
    (hbh : ¬ G.Adj b h) (hcd : ¬ G.Adj c d)
    (hcg : ¬ G.Adj c g)
    (hn : [a, b, c, d, e, f, g, h].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .p, ⟨.p, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .p).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .p).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 3), (0, 4), (0, 5), (1, 4),
       (1, 6), (2, 5), (2, 7), (4, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .p).color =
        ([.reddish, .red, .red, .bluish, .blue, .blue,
          .bluish, .bluish] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh]
  · intro x y hne hnon hauto
    have hp := positiveP_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (h | h | h | h | h | h | h | h | h) |
      (h | h | h | h | h | h | h | h | h)
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals first
      | exact hab
      | exact hac
      | exact hag
      | exact hah
      | exact hbc
      | exact hbd
      | exact hbh
      | exact hcd
      | exact hcg
      | exact fun h => hab h.symm
      | exact fun h => hac h.symm
      | exact fun h => hag h.symm
      | exact fun h => hah h.symm
      | exact fun h => hbc h.symm
      | exact fun h => hbd h.symm
      | exact fun h => hbh h.symm
      | exact fun h => hcd h.symm
      | exact fun h => hcg h.symm

/-- The new reducer `r+`, inserted before the former `r+` in the catalog. -/
theorem containsPositiveR
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbd : G.Adj b d) (hbf : G.Adj b f)
    (hcg : G.Adj c g) (hci : G.Adj c i)
    (hef : G.Adj e f) (hgh : G.Adj g h)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (haf : ¬ G.Adj a f) (hah : ¬ G.Adj a h)
    (hai : ¬ G.Adj a i) (hbc : ¬ G.Adj b c)
    (hbe : ¬ G.Adj b e) (hbh : ¬ G.Adj b h)
    (hbi : ¬ G.Adj b i) (hcd : ¬ G.Adj c d)
    (hce : ¬ G.Adj c e) (hcf : ¬ G.Adj c f)
    (hch : ¬ G.Adj c h)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .r, ⟨.r, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .r).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .r).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 3), (0, 4), (0, 6), (1, 3), (1, 5),
       (2, 6), (2, 8), (4, 5), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .r).color =
        ([.reddish, .red, .red, .bluish, .blue, .blue,
          .blue, .blue, .bluish] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi]
  · intro x y hne hnon hauto
    have hp := positiveR_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (h | h | h | h | h | h | h | h | h | h | h | h | h) |
      (h | h | h | h | h | h | h | h | h | h | h | h | h)
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals first
      | exact hab | exact hac | exact haf | exact hah | exact hai
      | exact hbc | exact hbe | exact hbh | exact hbi
      | exact hcd | exact hce | exact hcf | exact hch
      | exact fun h => hab h.symm | exact fun h => hac h.symm
      | exact fun h => haf h.symm | exact fun h => hah h.symm
      | exact fun h => hai h.symm | exact fun h => hbc h.symm
      | exact fun h => hbe h.symm | exact fun h => hbh h.symm
      | exact fun h => hbi h.symm | exact fun h => hcd h.symm
      | exact fun h => hce h.symm | exact fun h => hcf h.symm
      | exact fun h => hch h.symm

/-- Reducer `s+` (the former `r+`), in catalog order. -/
theorem containsPositiveS
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbd : G.Adj b d) (hbf : G.Adj b f)
    (hch : G.Adj c h) (hci : G.Adj c i)
    (hef : G.Adj e f) (hgh : G.Adj g h)
    (hab : ¬ G.Adj a b) (hac : ¬ G.Adj a c)
    (haf : ¬ G.Adj a f) (hah : ¬ G.Adj a h)
    (hai : ¬ G.Adj a i) (hbc : ¬ G.Adj b c)
    (hbe : ¬ G.Adj b e) (hbg : ¬ G.Adj b g)
    (hbh : ¬ G.Adj b h) (hbi : ¬ G.Adj b i)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e)
    (hcf : ¬ G.Adj c f) (hcg : ¬ G.Adj c g)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .s, ⟨.s, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .s).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .s).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈
      [(0, 3), (0, 4), (0, 6), (1, 3), (1, 5),
       (2, 7), (2, 8), (4, 5), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .s).color =
        ([.reddish, .red, .red, .bluish, .blue, .blue,
          .blue, .blue, .bluish] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi]
  · intro x y hne hnon hauto
    have hp := positiveS_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
      (h | h | h | h | h | h | h | h | h | h | h | h | h | h) |
      (h | h | h | h | h | h | h | h | h | h | h | h | h | h)
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals first
      | exact hab | exact hac | exact haf | exact hah | exact hai
      | exact hbc | exact hbe | exact hbg | exact hbh | exact hbi
      | exact hcd | exact hce | exact hcf | exact hcg
      | exact fun h => hab h.symm | exact fun h => hac h.symm
      | exact fun h => haf h.symm | exact fun h => hah h.symm
      | exact fun h => hai h.symm | exact fun h => hbc h.symm
      | exact fun h => hbe h.symm | exact fun h => hbg h.symm
      | exact fun h => hbh h.symm | exact fun h => hbi h.symm
      | exact fun h => hcd h.symm | exact fun h => hce h.symm
      | exact fun h => hcf h.symm | exact fun h => hcg h.symm

/-- Reducer `o+`; its only non-automatic boundary nonedge is `a-g`. -/
theorem containsPositiveO
    (C : GoodColoring G) {a b c d e f g : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .blue)
    (he : C.color e = .blue) (hf : C.color f = .bluish)
    (hg : C.color g = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (haf : G.Adj a f)
    (hbc : G.Adj b c) (hbe : G.Adj b e) (hbg : G.Adj b g)
    (hcf : G.Adj c f) (hcg : G.Adj c g) (hde : G.Adj d e)
    (hag : ¬ G.Adj a g) (hn : [a, b, c, d, e, f, g].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .o, ⟨.o, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .o).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .o).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 5), (1, 2), (1, 4),
      (1, 6), (2, 5), (2, 6), (3, 4)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .o).color =
        ([.reddish, .red, .red, .blue, .blue, .bluish, .bluish] :
          List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg]
  · intro x y hne hnon hauto
    have hp := positiveO_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hag
    · exact fun h => hag h.symm

/-- Reducer `q+`; its two non-automatic boundary nonedges are exposed. -/
theorem containsPositiveQ
    (C : GoodColoring G) {a b c d e f g h : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .blue) (hf : C.color f = .blue)
    (hg : C.color g = .bluish) (hh : C.color h = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (haf : G.Adj a f)
    (hbc : G.Adj b c) (hbf : G.Adj b f) (hbg : G.Adj b g)
    (hcg : G.Adj c g) (hch : G.Adj c h) (hef : G.Adj e f)
    (hag : ¬ G.Adj a g) (hah : ¬ G.Adj a h)
    (hn : [a, b, c, d, e, f, g, h].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .q, ⟨.q, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .q).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .q).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 5), (1, 2), (1, 5),
      (1, 6), (2, 6), (2, 7), (4, 5)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .q).color =
        ([.reddish, .red, .red, .bluish, .blue, .blue,
          .bluish, .bluish] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh]
  · intro x y hne hnon hauto
    have hp := positiveQ_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hag | exact hah
      | exact fun h => hag h.symm | exact fun h => hah h.symm

/-- Reducer `t+` (the old `s+` before insertion of the new `r+`). -/
theorem containsPositiveT
    (C : GoodColoring G) {a b c d e f g h i : V}
    (ha : C.color a = .reddish) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .blue)
    (hg : C.color g = .blue) (hh : C.color h = .bluish)
    (hi : C.color i = .bluish)
    (had : G.Adj a d) (hae : G.Adj a e) (hag : G.Adj a g)
    (hbc : G.Adj b c) (hbg : G.Adj b g) (hbh : G.Adj b h)
    (hch : G.Adj c h) (hci : G.Adj c i) (hfg : G.Adj f g)
    (haf : ¬ G.Adj a f) (hah : ¬ G.Adj a h) (hai : ¬ G.Adj a i)
    (hn : [a, b, c, d, e, f, g, h, i].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .t, ⟨.t, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .t).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .t).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 6), (1, 2), (1, 6),
      (1, 7), (2, 7), (2, 8), (5, 6)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .t).color =
        ([.reddish, .red, .red, .bluish, .bluish, .blue,
          .blue, .bluish, .bluish] : List Color).get := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi]
  · intro x y hne hnon hauto
    have hp := positiveT_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact haf | exact hah | exact hai
      | exact fun h => haf h.symm | exact fun h => hah h.symm
      | exact fun h => hai h.symm

end Subcubic
