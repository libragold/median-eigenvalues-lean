import Subcubic.TailReducers
import Subcubic.Lemma3_3
import Mathlib.Tactic.FinCases

/-!
# Lemma 4.2

The proof handles all cases of four, three, and two crossing edges. Reusable
facts about good colorings live in `Subcubic.ColoringLemmas`.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem contains_positiveA
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) :
    ContainsPositiveTailReducer C := by
  have hab_ne : a ≠ b := hab.ne
  have hcd_ne : c ≠ d := hcd.ne
  have hac_ne : a ≠ c := by intro h; subst c; simp_all
  have had_ne : a ≠ d := by intro h; subst d; simp_all
  have hbc_ne : b ≠ c := by intro h; subst c; simp_all
  have hbd_ne : b ≠ d := by intro h; subst d; simp_all
  have hn : [a, b, c, d].Nodup := by
    simp [hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd_ne]
  refine ⟨positiveTailReducer .a, ⟨.a, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d].get, hn.injective_get, ?_, ?_⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hab, hcd, hac, had, hbc, hbd]
  · intro x
    have hcolors : (positiveTailReducer .a).color =
        ![.red, .red, .blue, .blue] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide

/-- The canonical three-crossing-edge case: `ac`, `ad`, and `bd` are
present, while `bc` is absent. -/
private theorem three_crossing_edges
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbd : G.Adj b d) (hbc : ¬ G.Adj b c) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  have had_vertices : a ≠ d := by intro h; subst d; simp_all
  obtain ⟨e, hbe, hea, hed⟩ :=
    C.exists_third_neighbor (Or.inl hb) had_vertices
  have he_side : C.color e = .blue ∨ C.color e = .bluish :=
    C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbe hea
  have hde : d ≠ e := hed.symm
  have hce : c ≠ e := by
    intro h
    subst e
    exact hbc hbe
  rcases lemma3_3 C hb hd hc he_side hbd hbe hcd.symm hde hce with he | henhancer
  · left
    have hab_ne : a ≠ b := hab.ne
    have hcd_ne : c ≠ d := hcd.ne
    have hac_ne : a ≠ c := by intro h; subst c; simp_all
    have hbc_ne : b ≠ c := by intro h; subst c; simp_all
    have hbd_ne : b ≠ d := by intro h; subst d; simp_all
    have heb : e ≠ b := hbe.ne.symm
    have hae : ¬ G.Adj a e :=
      C.not_adj_fourth_neighbor (Or.inl ha) hab hac had
        hbc_ne hbd_ne hcd_ne heb hce.symm hed
    have hce_nonedge : ¬ G.Adj c e := by
      intro h
      exact C.bluish_not_adj_blueSide he (Or.inl hc) h.symm
    have hde_nonedge : ¬ G.Adj d e := by
      intro h
      exact C.bluish_not_adj_blueSide he (Or.inl hd) h.symm
    have hae_vertices : a ≠ e := hea.symm
    have hbe_vertices : b ≠ e := heb.symm
    have hn : [a, b, c, d, e].Nodup := by
      simp [hab_ne, hac_ne, had_vertices, hae_vertices, hbc_ne, hbd_ne, hbe_vertices,
        hcd_ne, hce, hde]
    refine ⟨positiveTailReducer .d, ⟨.d, rfl⟩, Or.inl ?_⟩
    refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_⟩
    · intro x y
      fin_cases x <;> fin_cases y <;>
        simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
          graphOfEdges, G.adj_comm, hab, hcd, hac, had, hbd, hbc, hbe,
          hae, hce_nonedge, hde_nonedge]
    · intro x
      have hcolors : (positiveTailReducer .d).color =
          ![.red, .red, .blue, .blue, .bluish] := by native_decide
      rw [hcolors]
      fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide
  · exact Or.inr henhancer

/-- Canonical matching case: the two crossing edges are `ac` and `bd`. -/
private theorem two_crossing_matching
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (hbd : G.Adj b d)
    (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  have hbc_vertices : b ≠ c := by intro h; subst c; simp_all
  obtain ⟨x, hax, hxb, hxc⟩ := C.exists_third_neighbor (Or.inl ha) hbc_vertices
  have hxside := C.other_neighbor_of_red_is_blueSide ha hb hab hax hxb
  have hdx : d ≠ x := by
    intro h
    subst x
    exact had hax
  rcases lemma3_3 C ha hc hd hxside hac hax hcd hxc.symm hdx with
      hx | henhancer
  · have had_vertices : a ≠ d := by intro h; subst d; simp_all
    obtain ⟨y, hby, hya, hyd⟩ := C.exists_third_neighbor (Or.inl hb) had_vertices
    have hyside := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hby hya
    have hcy : c ≠ y := by
      intro h
      subst y
      exact hbc hby
    rcases lemma3_3 C hb hd hc hyside hbd hby hcd.symm hyd.symm hcy with
        hy | henhancer
    · left
      have hab_ne : a ≠ b := hab.ne
      have hcd_ne : c ≠ d := hcd.ne
      have hac_ne : a ≠ c := hac.ne
      have hbd_ne : b ≠ d := hbd.ne
      have hxa : x ≠ a := hax.ne.symm
      have hxc' : x ≠ c := hxc
      have hxd : x ≠ d := hdx.symm
      have hya' : y ≠ a := hya
      have hyb : y ≠ b := hby.ne.symm
      have hyc : y ≠ c := hcy.symm
      have hyd' : y ≠ d := hyd
      have hxc_nonedge : ¬ G.Adj x c :=
        C.bluish_not_adj_blueSide hx (Or.inl hc)
      have hxd_nonedge : ¬ G.Adj x d :=
        C.bluish_not_adj_blueSide hx (Or.inl hd)
      have hyc_nonedge : ¬ G.Adj y c :=
        C.bluish_not_adj_blueSide hy (Or.inl hc)
      have hyd_nonedge : ¬ G.Adj y d :=
        C.bluish_not_adj_blueSide hy (Or.inl hd)
      have hcx_nonedge : ¬ G.Adj c x := fun h => hxc_nonedge h.symm
      have hdx_nonedge : ¬ G.Adj d x := fun h => hxd_nonedge h.symm
      have hcy_nonedge : ¬ G.Adj c y := fun h => hyc_nonedge h.symm
      have hdy_nonedge : ¬ G.Adj d y := fun h => hyd_nonedge h.symm
      by_cases hxy : x = y
      · subst y
        have hax_vertices : a ≠ x := hxa.symm
        have hbx_vertices : b ≠ x := hyb.symm
        have hcx_vertices : c ≠ x := hxc'.symm
        have hdx_vertices : d ≠ x := hxd.symm
        have hn : [a, b, c, d, x].Nodup := by
          simp [hab_ne, hac_ne, had_vertices, hax_vertices, hbc_vertices, hbd_ne,
            hbx_vertices, hcd_ne, hcx_vertices, hdx_vertices]
        refine ⟨positiveTailReducer .f, ⟨.f, rfl⟩, Or.inl ?_⟩
        refine ⟨[a, b, c, d, x].get, hn.injective_get, ?_, ?_⟩
        · intro p q
          fin_cases p <;> fin_cases q <;>
            simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
              graphOfEdges, G.adj_comm, hab, hcd, hac, hbd, hax, hby,
              had, hbc, hcx_nonedge, hdx_nonedge]
        · intro p
          have hcolors : (positiveTailReducer .f).color =
              ![.red, .red, .blue, .blue, .bluish] := by native_decide
          rw [hcolors]
          fin_cases p <;> simp [ha, hb, hc, hd, hx] <;> native_decide
      · have hxy_nonedge : ¬ G.Adj x y :=
          C.bluish_not_adj_blueSide hx (Or.inr hy)
        have hxb_ne : x ≠ b := by intro h; subst x; simp_all
        have hay : ¬ G.Adj a y :=
          C.not_adj_fourth_neighbor (Or.inl ha) hab hac hax
            hbc_vertices hxb_ne.symm hxc.symm hyb hyc (Ne.symm hxy)
        have hbx : ¬ G.Adj b x :=
          C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbd hby
            had_vertices hya.symm hyd.symm hxa hxd hxy
        have hya_vertices : a ≠ y := hya.symm
        have hxb_vertices : b ≠ x := hxb_ne.symm
        have hby_vertices : b ≠ y := hyb.symm
        have hcy_vertices : c ≠ y := hcy
        have hdy_vertices : d ≠ y := hyd.symm
        have hn : [a, b, x, c, d, y].Nodup := by
          simp [hab_ne, hxa.symm, hac_ne, had_vertices, hya_vertices,
            hxb_vertices, hxc', hxd, hxy, hbc_vertices, hbd_ne,
            hby_vertices, hcd_ne, hcy_vertices, hdy_vertices]
        refine ⟨positiveTailReducer .i, ⟨.i, rfl⟩, Or.inl ?_⟩
        refine ⟨[a, b, x, c, d, y].get, hn.injective_get, ?_, ?_⟩
        · intro p q
          fin_cases p <;> fin_cases q <;>
            simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
              graphOfEdges, G.adj_comm, hab, hcd, hac, hbd, hax, hby,
              had, hbc, hay, hbx, hcx_nonedge, hdx_nonedge,
              hcy_nonedge, hdy_nonedge, hxy_nonedge]
        · intro p
          have hcolors : (positiveTailReducer .i).color =
              ![.red, .red, .bluish, .blue, .blue, .bluish] := by native_decide
          rw [hcolors]
          fin_cases p <;> simp [ha, hb, hc, hd, hx, hy] <;> native_decide
    · exact Or.inr henhancer
  · exact Or.inr henhancer

/-- Canonical adjacent case: the two crossing edges are `ac` and `ad`. -/
private theorem two_crossing_adjacent
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  have had_vertices : a ≠ d := by intro h; subst d; simp_all
  obtain ⟨x, hcx, hxd, hxa⟩ := C.exists_third_neighbor (Or.inr hc) had_vertices.symm
  have hxside := C.other_neighbor_of_blue_is_redSide hc hd hcd hcx hxd
  have hbx : b ≠ x := by
    intro h
    subst x
    exact hbc hcx.symm
  rcases lemma3_3_reversed C hc ha hb hxside hac.symm hcx hab hxa.symm hbx with
      hx | henhancer
  · have hac_vertices : a ≠ c := by intro h; subst c; simp_all
    obtain ⟨y, hdy, hyc, hya⟩ := C.exists_third_neighbor (Or.inr hd) hac_vertices.symm
    have hyside := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdy hyc
    have hby : b ≠ y := by
      intro h
      subst y
      exact hbd hdy.symm
    rcases lemma3_3_reversed C hd ha hb hyside had.symm hdy hab hya.symm hby with
        hy | henhancer
    · left
      have hab_ne : a ≠ b := hab.ne
      have hcd_ne : c ≠ d := hcd.ne
      have hcx_ne : c ≠ x := hcx.ne
      have hdy_ne : d ≠ y := hdy.ne
      have hxa' : x ≠ a := hxa
      have hxb' : x ≠ b := hbx.symm
      have hxd' : x ≠ d := hxd
      have hya' : y ≠ a := hya
      have hyb' : y ≠ b := hby.symm
      have hyc' : y ≠ c := hyc
      have hxa_nonedge : ¬ G.Adj x a :=
        C.reddish_not_adj_redSide hx (Or.inl ha)
      have hxb_nonedge : ¬ G.Adj x b :=
        C.reddish_not_adj_redSide hx (Or.inl hb)
      have hya_nonedge : ¬ G.Adj y a :=
        C.reddish_not_adj_redSide hy (Or.inl ha)
      have hyb_nonedge : ¬ G.Adj y b :=
        C.reddish_not_adj_redSide hy (Or.inl hb)
      have hax_nonedge : ¬ G.Adj a x := fun h => hxa_nonedge h.symm
      have hbx_nonedge : ¬ G.Adj b x := fun h => hxb_nonedge h.symm
      have hay_nonedge : ¬ G.Adj a y := fun h => hya_nonedge h.symm
      have hby_nonedge : ¬ G.Adj b y := fun h => hyb_nonedge h.symm
      have hcb_vertices : c ≠ b := by intro h; subst b; simp_all
      have hdb_vertices : d ≠ b := by intro h; subst b; simp_all
      by_cases hxy : x = y
      · subst y
        have hca_vertices : c ≠ a := hac_vertices.symm
        have hda_vertices : d ≠ a := had_vertices.symm
        have hdx_vertices : d ≠ x := hxd'.symm
        have hax_vertices : a ≠ x := hxa'.symm
        have hbx_vertices : b ≠ x := hxb'.symm
        have hn : [c, d, a, b, x].Nodup := by
          simp [hcd_ne, hca_vertices, hcb_vertices, hcx_ne, hda_vertices,
            hdb_vertices, hdx_vertices, hab_ne, hax_vertices, hbx_vertices]
        refine ⟨positiveTailReducer .e, ⟨.e, rfl⟩, Or.inr ?_⟩
        refine ⟨[c, d, a, b, x].get, hn.injective_get, ?_, ?_⟩
        · intro p q
          fin_cases p <;> fin_cases q <;>
            simp [ColoredPattern.swapSides, positiveTailReducer,
              positiveTailReducerData, PatternData.toPattern, graphOfEdges,
              G.adj_comm, hab, hcd, hac, had, hcx, hdy, hbc, hbd,
              hax_nonedge, hbx_nonedge]
        · intro p
          have hcolors : (positiveTailReducer .e).swapSides.color =
              ![.blue, .blue, .red, .red, .reddish] := by native_decide
          rw [hcolors]
          fin_cases p <;> simp [ha, hb, hc, hd, hx] <;> native_decide
      · have hxy_nonedge : ¬ G.Adj x y :=
          C.reddish_not_adj_redSide hx (Or.inr hy)
        have hcy : ¬ G.Adj c y :=
          C.not_adj_fourth_neighbor (Or.inr hc) hcd hac.symm hcx
            had_vertices.symm hxd.symm hxa.symm hdy.ne.symm hya (Ne.symm hxy)
        have hdx : ¬ G.Adj d x :=
          C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm had.symm hdy
            hac_vertices.symm hyc.symm hya.symm hcx.ne.symm hxa hxy
        have hca_vertices : c ≠ a := hac_vertices.symm
        have hcy_vertices : c ≠ y := hyc.symm
        have hdx_vertices : d ≠ x := hxd'.symm
        have hda_vertices : d ≠ a := had_vertices.symm
        have hay_vertices : a ≠ y := hya'.symm
        have hby_vertices : b ≠ y := hyb'.symm
        have hn : [c, d, x, a, b, y].Nodup := by
          simp [hcd_ne, hcx_ne, hca_vertices, hcb_vertices, hcy_vertices,
            hdx_vertices, hda_vertices, hdb_vertices, hdy_ne, hxy,
            hxa', hxb', hay_vertices, hby_vertices, hab_ne]
        refine ⟨positiveTailReducer .j, ⟨.j, rfl⟩, Or.inr ?_⟩
        refine ⟨[c, d, x, a, b, y].get, hn.injective_get, ?_, ?_⟩
        · intro p q
          fin_cases p <;> fin_cases q <;>
            simp [ColoredPattern.swapSides, positiveTailReducer,
              positiveTailReducerData, PatternData.toPattern, graphOfEdges,
              G.adj_comm, hab, hcd, hac, had, hcx, hdy, hbc, hbd,
              hcy, hdx, hax_nonedge, hbx_nonedge, hay_nonedge,
              hby_nonedge, hxy_nonedge]
        · intro p
          have hcolors : (positiveTailReducer .j).swapSides.color =
              ![.blue, .blue, .reddish, .red, .red, .reddish] := by native_decide
          rw [hcolors]
          fin_cases p <;> simp [ha, hb, hc, hd, hx, hy] <;> native_decide
    · exact Or.inr henhancer
  · exact Or.inr henhancer

/-- The remaining case of exactly two crossing edges. -/
private theorem two_crossing_edges
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hcount : fourVertexCrossEdgeCount G a b c d = 2) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  by_cases hac : G.Adj a c <;>
  by_cases had : G.Adj a d <;>
  by_cases hbc : G.Adj b c <;>
  by_cases hbd : G.Adj b d
  all_goals simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd] at hcount
  · exact two_crossing_adjacent C ha hb hc hd hab hcd hac had hbc hbd
  · have hc' : C.swapSides.color c = .red := by simp [hc]
    have hd' : C.swapSides.color d = .red := by simp [hd]
    have ha' : C.swapSides.color a = .blue := by simp [ha]
    have hb' : C.swapSides.color b = .blue := by simp [hb]
    have hda : ¬ G.Adj d a := fun h => had h.symm
    have hdb : ¬ G.Adj d b := fun h => hbd h.symm
    rcases two_crossing_adjacent C.swapSides hc' hd' ha' hb' hcd hab
        hac.symm hbc.symm hda hdb with hptr | henhancer
    · exact Or.inl ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptr)
    · exact Or.inr ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 henhancer)
  · exact two_crossing_matching C ha hb hc hd hab hcd hac hbd had hbc
  · exact two_crossing_matching C ha hb hd hc hab hcd.symm had hbc hac hbd
  · have hd' : C.swapSides.color d = .red := by simp [hd]
    have hc' : C.swapSides.color c = .red := by simp [hc]
    have ha' : C.swapSides.color a = .blue := by simp [ha]
    have hb' : C.swapSides.color b = .blue := by simp [hb]
    have hca : ¬ G.Adj c a := fun h => hac h.symm
    have hcb : ¬ G.Adj c b := fun h => hbc h.symm
    rcases two_crossing_adjacent C.swapSides hd' hc' ha' hb' hcd.symm hab
        had.symm hbd.symm hca hcb with hptr | henhancer
    · exact Or.inl ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptr)
    · exact Or.inr ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 henhancer)
  · exact two_crossing_adjacent C hb ha hc hd hab.symm hcd hbc hbd hac had

/-- **Lemma 4.2.** If a red edge `ab` and a blue edge `cd` have at least two
edges between their endpoint pairs, then there is an induced positive tail
reducer or an induced cut enhancer (in either side orientation). -/
theorem redEdge_blueEdge_multipleEdges
    (C : GoodColoring G) (a b c d : V)
    (hab : G.Adj a b) (ha : C.color a = .red) (hb : C.color b = .red)
    (hcd : G.Adj c d) (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hmulti : 2 ≤ fourVertexCrossEdgeCount G a b c d) :
    ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  by_cases hac : G.Adj a c <;>
  by_cases had : G.Adj a d <;>
  by_cases hbc : G.Adj b c <;>
  by_cases hbd : G.Adj b d
  all_goals simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd] at hmulti
  · exact Or.inl (contains_positiveA C ha hb hc hd hab hcd hac had hbc hbd)
  · exact three_crossing_edges C ha hb hd hc hab hcd.symm had hac hbc hbd
  · exact three_crossing_edges C ha hb hc hd hab hcd hac had hbd hbc
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]
  · exact three_crossing_edges C hb ha hd hc hab.symm hcd.symm hbd hbc hac had
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]
  · exact three_crossing_edges C hb ha hc hd hab.symm hcd hbc hbd had hac
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]
  · apply two_crossing_edges C ha hb hc hd hab hcd
    simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd]

end Subcubic
