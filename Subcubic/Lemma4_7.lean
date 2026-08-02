import Subcubic.Lemma4_5
import Mathlib.Tactic.FinCases

/-!
# Lemma 4.7

The displayed configuration is the induced cycle
`a-b-c-d-e-f-g-h-a`.  Its red edges are `ab`, `ef`, and its blue edges are
`cd`, `gh`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The eight displayed vertices, in order, induce exactly a cycle. -/
def FormsInducedCycle8 (G : SimpleGraph V)
    (a b c d e f g h : V) : Prop :=
  let p : Fin 8 → V := ![a, b, c, d, e, f, g, h]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y ↔ G.Adj (p x) (p y)

private theorem contains_cutEnhancerB_swapped
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .bluish) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .red)
    (he : C.color e = .blue)
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
  refine ⟨cutEnhancer .b, ⟨.b, rfl⟩, Or.inr ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [ColoredPattern.swapSides, cutEnhancer, graphOfEdges, G.adj_comm,
        hab, had, hbc, hde, hac, hae, hbd, hbe, hcd, hce]
  · intro x
    fin_cases x <;>
      simp [ColoredPattern.swapSides, cutEnhancer, Color.swap,
        ha, hb, hc, hd, he]

private theorem contains_positiveC
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbe : G.Adj b e) (hcd : G.Adj c d)
    (hab : ¬ G.Adj a b) (had : ¬ G.Adj a d)
    (hbc : ¬ G.Adj b c) :
    ContainsPositiveTailReducer C := by
  have hce : ¬ G.Adj c e := fun h =>
    C.bluish_not_adj_blueSide he (Or.inl hc) h.symm
  have hde : ¬ G.Adj d e := fun h =>
    C.bluish_not_adj_blueSide he (Or.inl hd) h.symm
  have hn : [a, b, c, d, e].Nodup := by
    have hae_ne := hae.ne
    have hbe_ne := hbe.ne
    have hac_ne := hac.ne
    have hbd_ne := hbd.ne
    have hcd_ne := hcd.ne
    have hab_ne : a ≠ b := by intro h; subst b; simp_all
    have had_ne : a ≠ d := by intro h; subst d; simp_all
    have hbc_ne : b ≠ c := by intro h; subst c; simp_all
    have hce_ne : c ≠ e := by intro h; subst e; simp_all
    have hde_ne : d ≠ e := by intro h; subst e; simp_all
    simp [hab_ne, hac_ne, had_ne, hae_ne, hbc_ne, hbd_ne, hbe_ne,
      hcd_ne, hce_ne, hde_ne]
  refine ⟨positiveTailReducer .c, ⟨.c, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_⟩
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

private theorem contains_positiveV
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .red)
    (he : C.color e = .bluish)
    (hf : C.color f = .blue) (hg : C.color g = .blue)
    (hh : C.color h = .blue) (hi : C.color i = .blue)
    (hj : C.color j = .bluish)
    (hab : G.Adj a b) (hae : G.Adj a e) (hai : G.Adj a i)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : G.Adj c d) (hcg : G.Adj c g) (hcj : G.Adj c j)
    (hdh : G.Adj d h) (hdj : G.Adj d j)
    (hfg : G.Adj f g) (hhi : G.Adj h i)
    (hn : [a, b, c, d, e, f, g, h, i, j].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .v, ⟨.v, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .v).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .v).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    change ∀ edge : Fin 10 × Fin 10, edge ∈
      [(0, 1), (0, 4), (0, 8), (1, 4), (1, 5), (2, 3),
       (2, 6), (2, 9), (3, 7), (3, 9), (5, 6), (7, 8)] →
      G.Adj ([a, b, c, d, e, f, g, h, i, j].get edge.1)
        ([a, b, c, d, e, f, g, h, i, j].get edge.2)
    intro edge hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .v).color =
        ![.red, .red, .red, .red, .bluish, .blue,
          .blue, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj] <;>
      native_decide
  · intro x y hne hnon hnot
    exact (hnot (positiveV_automaticNonedges x y hne hnon)).elim

private theorem contains_positiveW
    (C : GoodColoring G) {a b c d e f g h i j k : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .red)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .blue) (hj : C.color j = .blue)
    (hk : C.color k = .bluish)
    (hab : G.Adj a b) (hae : G.Adj a e) (haj : G.Adj a j)
    (hbf : G.Adj b f) (hbg : G.Adj b g)
    (hcd : G.Adj c d) (hch : G.Adj c h) (hck : G.Adj c k)
    (hdi : G.Adj d i) (hdk : G.Adj d k)
    (hgh : G.Adj g h) (hij : G.Adj i j)
    (hn : [a, b, c, d, e, f, g, h, i, j, k].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .w, ⟨.w, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .w).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j, k].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .w).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    change ∀ edge : Fin 11 × Fin 11, edge ∈
      [(0, 1), (0, 4), (0, 9), (1, 5), (1, 6), (2, 3),
       (2, 7), (2, 10), (3, 8), (3, 10), (6, 7), (8, 9)] →
      G.Adj ([a, b, c, d, e, f, g, h, i, j, k].get edge.1)
        ([a, b, c, d, e, f, g, h, i, j, k].get edge.2)
    intro edge hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .w).color =
        ![.red, .red, .red, .red, .bluish, .bluish,
          .blue, .blue, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk] <;>
      native_decide
  · intro x y hne hnon hnot
    exact (hnot (positiveW_automaticNonedges x y hne hnon)).elim

private theorem contains_positiveY
    (C : GoodColoring G) {a b c d e f g h i j k l : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .red) (hd : C.color d = .red)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .blue) (hj : C.color j = .blue)
    (hk : C.color k = .bluish) (hl : C.color l = .bluish)
    (hab : G.Adj a b) (hae : G.Adj a e) (haj : G.Adj a j)
    (hbf : G.Adj b f) (hbg : G.Adj b g)
    (hcd : G.Adj c d) (hch : G.Adj c h) (hcl : G.Adj c l)
    (hdi : G.Adj d i) (hdk : G.Adj d k)
    (hgh : G.Adj g h) (hij : G.Adj i j)
    (hn : [a, b, c, d, e, f, g, h, i, j, k, l].Nodup) :
    ContainsPositiveTailReducer C := by
  refine ⟨positiveTailReducer .y, ⟨.y, rfl⟩, Or.inl ?_⟩
  apply (positiveTailReducer .y).occursInduced_of_embedding C
    ([a, b, c, d, e, f, g, h, i, j, k, l].get) hn.injective_get
  · intro x y hxy
    apply (positiveTailReducerData .y).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [positiveTailReducerData]
    change ∀ edge : Fin 12 × Fin 12, edge ∈
      [(0, 1), (0, 4), (0, 9), (1, 5), (1, 6), (2, 3),
       (2, 7), (2, 11), (3, 8), (3, 10), (6, 7), (8, 9)] →
      G.Adj ([a, b, c, d, e, f, g, h, i, j, k, l].get edge.1)
        ([a, b, c, d, e, f, g, h, i, j, k, l].get edge.2)
    intro edge hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals simp
    all_goals assumption
  · intro x
    have hcolors : (positiveTailReducer .y).color =
        ![.red, .red, .red, .red, .bluish, .bluish,
          .blue, .blue, .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;>
      simp [ha, hb, hc, hd, he, hf, hg, hh, hi, hj, hk, hl] <;>
      native_decide
  · intro x y hne hnon hnot
    exact (hnot (positiveY_automaticNonedges x y hne hnon)).elim

/-- **Lemma 4.7.** An induced eight-cycle whose colors occur in two red
edges and two blue edges contains a positive tail reducer or a cut enhancer. -/
theorem lemma4_7
    (C : GoodColoring G) {a b c d e f g h : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hcycleNodup : [a, b, c, d, e, f, g, h].Nodup := by
    simpa using List.nodup_ofFn_ofInjective hinj
  have hcycleDistinct := hcycleNodup
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil]
    at hcycleDistinct
  have cycle_vertices_ne {x y : Fin 8} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h] x) ≠
        (![a, b, c, d, e, f, g, h] y) := hinj.ne hxy
  have cycle_nonedge (x y : Fin 8)
      (hxy : ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) :=
    fun hxyG => hxy ((hedge x y).mpr hxyG)
  have hab : G.Adj a b := (hedge 0 1).mp (by native_decide)
  have hbc : G.Adj b c := (hedge 1 2).mp (by native_decide)
  have hcd : G.Adj c d := (hedge 2 3).mp (by native_decide)
  have hde : G.Adj d e := (hedge 3 4).mp (by native_decide)
  have hef : G.Adj e f := (hedge 4 5).mp (by native_decide)
  have hfg : G.Adj f g := (hedge 5 6).mp (by native_decide)
  have hgh : G.Adj g h := (hedge 6 7).mp (by native_decide)
  have hha : G.Adj h a := (hedge 7 0).mp (by native_decide)
  obtain ⟨p, hap, hpb, hph⟩ :=
    C.exists_third_neighbor (Or.inl ha)
      (cycle_vertices_ne (x := (1 : Fin 8)) (y := 7) (by decide))
  have hpside := C.other_neighbor_of_red_is_blueSide ha hb hab hap hpb
  have hag : ¬ G.Adj a g := by
    simpa using cycle_nonedge 0 6 (by native_decide)
  have hpg : p ≠ g := by intro hp; subst p; exact hag hap
  rcases lemma3_3 C ha hh hg hpside hha.symm hap hgh.symm
      hph.symm hpg.symm with hp | hce
  · obtain ⟨q, hbq, hqa, hqc⟩ :=
      C.exists_third_neighbor (Or.inl hb)
        (cycle_vertices_ne (x := (0 : Fin 8)) (y := 2) (by decide))
    have hqside := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbq hqa
    have hbd : ¬ G.Adj b d := by
      simpa using cycle_nonedge 1 3 (by native_decide)
    have hqd : q ≠ d := by intro hq; subst q; exact hbd hbq
    rcases lemma3_3 C hb hc hd hqside hbc hbq hcd
        hqc.symm hqd.symm with hq | hce
    · obtain ⟨r, her, hrf, hrd⟩ :=
        C.exists_third_neighbor (Or.inl he)
          (cycle_vertices_ne (x := (5 : Fin 8)) (y := 3) (by decide))
      have hrside := C.other_neighbor_of_red_is_blueSide he hf hef her hrf
      have hec : ¬ G.Adj e c := by
        simpa using cycle_nonedge 4 2 (by native_decide)
      have hrc : r ≠ c := by intro hr; subst r; exact hec her
      rcases lemma3_3 C he hd hc hrside hde.symm her hcd.symm
          hrd.symm hrc.symm with hr | hce
      · obtain ⟨s, hfs, hse, hsg⟩ :=
          C.exists_third_neighbor (Or.inl hf)
            (cycle_vertices_ne (x := (4 : Fin 8)) (y := 6) (by decide))
        have hsside := C.other_neighbor_of_red_is_blueSide hf he hef.symm hfs hse
        have hfh : ¬ G.Adj f h := by
          simpa using cycle_nonedge 5 7 (by native_decide)
        have hsh : s ≠ h := by intro hs; subst s; exact hfh hfs
        rcases lemma3_3 C hf hg hh hsside hfg hfs hgh
            hsg.symm hsh.symm with hs | hce
        · have bluish_not_mem_cycle {z : V} (hz : C.color z = .bluish) :
              z ∉ [a, b, c, d, e, f, g, h] := by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            exact ⟨
              fun hza => Color.noConfusion (ha.symm.trans (hza ▸ hz)),
              fun hzb => Color.noConfusion (hb.symm.trans (hzb ▸ hz)),
              fun hzc => Color.noConfusion (hc.symm.trans (hzc ▸ hz)),
              fun hzd => Color.noConfusion (hd.symm.trans (hzd ▸ hz)),
              fun hze => Color.noConfusion (he.symm.trans (hze ▸ hz)),
              fun hzf => Color.noConfusion (hf.symm.trans (hzf ▸ hz)),
              fun hzg => Color.noConfusion (hg.symm.trans (hzg ▸ hz)),
              fun hzh => Color.noConfusion (hh.symm.trans (hzh ▸ hz))⟩
          have hpout := bluish_not_mem_cycle hp
          have hqout := bluish_not_mem_cycle hq
          have hrout := bluish_not_mem_cycle hr
          have hsout := bluish_not_mem_cycle hs
          by_cases hpr : p = r
          · subst r
            have hae : ¬ G.Adj a e := by
              simpa using cycle_nonedge 0 4 (by native_decide)
            have had : ¬ G.Adj a d := by
              simpa using cycle_nonedge 0 3 (by native_decide)
            have hhe : ¬ G.Adj h e := by
              simpa using cycle_nonedge 7 4 (by native_decide)
            have hhd : ¬ G.Adj h d := by
              simpa using cycle_nonedge 7 3 (by native_decide)
            exact Or.inr (contains_cutEnhancerB_swapped C hp ha hh he hd
              hap.symm her.symm hha.symm hde.symm
              (C.bluish_not_adj_blueSide hp (Or.inl hh))
              (C.bluish_not_adj_blueSide hp (Or.inl hd))
              hae had hhe hhd)
          · by_cases hqs : q = s
            · subst s
              have hbf : ¬ G.Adj b f := by
                simpa using cycle_nonedge 1 5 (by native_decide)
              have hbg : ¬ G.Adj b g := by
                simpa using cycle_nonedge 1 6 (by native_decide)
              have hcf : ¬ G.Adj c f := by
                simpa using cycle_nonedge 2 5 (by native_decide)
              have hcg : ¬ G.Adj c g := by
                simpa using cycle_nonedge 2 6 (by native_decide)
              exact Or.inr (contains_cutEnhancerB_swapped C hq hb hc hf hg
                hbq.symm hfs.symm hbc hfg
                (C.bluish_not_adj_blueSide hq (Or.inl hc))
                (C.bluish_not_adj_blueSide hq (Or.inl hg))
                hbf hbg hcf hcg)
            · by_cases hqr : q = r
              · subst r
                have hbe : ¬ G.Adj b e := by
                  simpa using cycle_nonedge 1 4 (by native_decide)
                exact Or.inl (contains_positiveC C hb he hc hd hq
                  hbc hbq hde.symm her hcd hbe hbd hec)
              · by_cases hps : p = s
                · subst s
                  have haf : ¬ G.Adj a f := by
                    simpa using cycle_nonedge 0 5 (by native_decide)
                  exact Or.inl (contains_positiveC C ha hf hh hg hp
                    hha.symm hap hfg hfs hgh.symm haf hag hfh)
                · by_cases hpq : p = q
                  · subst q
                    by_cases hrs : r = s
                    · subst s
                      apply Or.inl
                      apply contains_positiveV C ha hb he hf hp hc hd hg hh hr
                        hab hap hha.symm hbq hbc hef hde.symm her hfg hfs hcd hgh
                      simp only [List.nodup_cons, List.mem_cons,
                        not_or, List.nodup_nil] at hcycleDistinct hpout hrout ⊢
                      grind
                    · apply Or.inl
                      apply contains_positiveW C he hf ha hb hr hs hg hh hc hd hp
                        hef her hde.symm hfs hfg hab hha.symm hap hbc hbq hgh hcd
                      simp only [List.nodup_cons, List.mem_cons,
                        not_or, List.nodup_nil] at hcycleDistinct hpout hrout hsout ⊢
                      grind
                  · by_cases hrs : r = s
                    · subst s
                      apply Or.inl
                      apply contains_positiveW C ha hb he hf hp hq hc hd hg hh hr
                        hab hap hha.symm hbq hbc hef hde.symm her hfg hfs hcd hgh
                      simp only [List.nodup_cons, List.mem_cons,
                        not_or, List.nodup_nil] at hcycleDistinct hpout hqout hrout ⊢
                      grind
                    · apply Or.inl
                      apply contains_positiveY C ha hb he hf hp hq hc hd hg hh hs hr
                        hab hap hha.symm hbq hbc hef hde.symm her hfg hfs hcd hgh
                      simp only [List.nodup_cons, List.mem_cons,
                        not_or, List.nodup_nil] at hcycleDistinct hpout hqout hrout hsout ⊢
                      grind
        · exact Or.inr hce
      · exact Or.inr hce
    · exact Or.inr hce
  · exact Or.inr hce

end Subcubic
