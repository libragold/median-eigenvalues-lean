import Subcubic.Lemma4_3
import Mathlib.Tactic.FinCases

/-!
# Lemma 4.4

The two endpoints of a red edge each have two other neighbors.  When all four
neighbor occurrences are bluish, their overlap has size two, one, or zero;
these cases induce positive tail reducers `b`, `h`, and `k`, respectively.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem contains_positiveB
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : c ≠ d) :
    ContainsPositiveTailReducer C := by
  have hab_ne : a ≠ b := hab.ne
  have hac_ne : a ≠ c := hac.ne
  have had_ne : a ≠ d := had.ne
  have hbc_ne : b ≠ c := hbc.ne
  have hbd_ne : b ≠ d := hbd.ne
  have hcd_nonedge : ¬ G.Adj c d :=
    C.bluish_not_adj_blueSide hc (Or.inr hd)
  have hn : [a, b, c, d].Nodup := by
    simp [hab_ne, hac_ne, had_ne, hbc_ne, hbd_ne, hcd]
  refine ⟨positiveTailReducer .b, ⟨.b, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d].get, hn.injective_get, ?_, ?_, by
    intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hab, hac, had, hbc, hbd,
        hcd_nonedge]
  · intro x
    have hcolors : (positiveTailReducer .b).color =
        ![.red, .red, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd] <;> native_decide

private theorem contains_positiveH
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbd : G.Adj b d) (hbe : G.Adj b e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e) :
    ContainsPositiveTailReducer C := by
  have hab_ne : a ≠ b := hab.ne
  have hac_ne : a ≠ c := hac.ne
  have had_ne : a ≠ d := had.ne
  have hbe_ne : b ≠ e := hbe.ne
  have hbc_ne : b ≠ c := by intro h; subst c; simp_all
  have hbd_ne : b ≠ d := hbd.ne
  have hae_ne : a ≠ e := by intro h; subst e; simp_all
  have hae : ¬ G.Adj a e :=
    C.not_adj_fourth_neighbor (Or.inl ha) hab hac had
      hbc_ne hbd_ne hcd hbe_ne.symm hce.symm hde.symm
  have hbc : ¬ G.Adj b c :=
    C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbd hbe
      had_ne hae_ne hde hac_ne.symm hcd hce
  have hcd_nonedge : ¬ G.Adj c d :=
    C.bluish_not_adj_blueSide hc (Or.inr hd)
  have hce_nonedge : ¬ G.Adj c e :=
    C.bluish_not_adj_blueSide hc (Or.inr he)
  have hde_nonedge : ¬ G.Adj d e :=
    C.bluish_not_adj_blueSide hd (Or.inr he)
  have hn : [a, b, c, d, e].Nodup := by
    simp [hab_ne, hac_ne, had_ne, hae_ne, hbc_ne, hbd_ne, hbe_ne,
      hcd, hce, hde]
  refine ⟨positiveTailReducer .h, ⟨.h, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, by
    intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hab, hac, had, hbd, hbe, hae, hbc,
        hcd_nonedge, hce_nonedge, hde_nonedge]
  · intro x
    have hcolors : (positiveTailReducer .h).color =
        ![.red, .red, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide

private theorem contains_positiveK
    (C : GoodColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : c ≠ d) (hef : e ≠ f)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) :
    ContainsPositiveTailReducer C := by
  have hab_ne : a ≠ b := hab.ne
  have hac_ne : a ≠ c := hac.ne
  have had_ne : a ≠ d := had.ne
  have hae_ne : a ≠ e := by intro h; subst e; simp_all
  have haf_ne : a ≠ f := by intro h; subst f; simp_all
  have hbc_ne : b ≠ c := by intro h; subst c; simp_all
  have hbd_ne : b ≠ d := by intro h; subst d; simp_all
  have hbe_ne : b ≠ e := hbe.ne
  have hbf_ne : b ≠ f := hbf.ne
  have hae : ¬ G.Adj a e :=
    C.not_adj_fourth_neighbor (Or.inl ha) hab hac had
      hbc_ne hbd_ne hcd hbe_ne.symm hce.symm hde.symm
  have haf : ¬ G.Adj a f :=
    C.not_adj_fourth_neighbor (Or.inl ha) hab hac had
      hbc_ne hbd_ne hcd hbf_ne.symm hcf.symm hdf.symm
  have hbc : ¬ G.Adj b c :=
    C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbe hbf
      hae_ne haf_ne hef hac_ne.symm hce hcf
  have hbd : ¬ G.Adj b d :=
    C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbe hbf
      hae_ne haf_ne hef had_ne.symm hde hdf
  have hcd_nonedge : ¬ G.Adj c d :=
    C.bluish_not_adj_blueSide hc (Or.inr hd)
  have hce_nonedge : ¬ G.Adj c e :=
    C.bluish_not_adj_blueSide hc (Or.inr he)
  have hcf_nonedge : ¬ G.Adj c f :=
    C.bluish_not_adj_blueSide hc (Or.inr hf)
  have hde_nonedge : ¬ G.Adj d e :=
    C.bluish_not_adj_blueSide hd (Or.inr he)
  have hdf_nonedge : ¬ G.Adj d f :=
    C.bluish_not_adj_blueSide hd (Or.inr hf)
  have hef_nonedge : ¬ G.Adj e f :=
    C.bluish_not_adj_blueSide he (Or.inr hf)
  have hn : [a, b, c, d, e, f].Nodup := by
    simp [hab_ne, hac_ne, had_ne, hae_ne, haf_ne, hbc_ne, hbd_ne,
      hbe_ne, hbf_ne, hcd, hce, hcf, hde, hdf, hef]
  refine ⟨positiveTailReducer .k, ⟨.k, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e, f].get, hn.injective_get, ?_, ?_, by
    intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hab, hac, had, hbe, hbf, hae, haf,
        hbc, hbd, hcd_nonedge, hce_nonedge, hcf_nonedge, hde_nonedge,
        hdf_nonedge, hef_nonedge]
  · intro x
    have hcolors : (positiveTailReducer .k).color =
        ![.red, .red, .bluish, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he, hf] <;> native_decide

/-- **Lemma 4.4.** Let `ab` be a red edge. If every neighbor of either
endpoint other than its mate on `ab` is bluish, then the graph contains a
positive tail reducer. -/
theorem lemma4_4
    (C : GoodColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (haDegree : vertexDegree G a = 3)
    (hbDegree : vertexDegree G b = 3)
    (ha_other : ∀ v, G.Adj a v → v ≠ b → C.color v = .bluish)
    (hb_other : ∀ v, G.Adj b v → v ≠ a → C.color v = .bluish) :
    ContainsPositiveTailReducer C := by
  obtain ⟨c, d, hac, had, hcb, hdb, hcd⟩ :=
    C.exists_two_other_neighbors haDegree hab
  obtain ⟨e, f, hbe, hbf, hea, hfa, hef⟩ :=
    C.exists_two_other_neighbors hbDegree hab.symm
  have hc := ha_other c hac hcb
  have hd := ha_other d had hdb
  have he := hb_other e hbe hea
  have hf := hb_other f hbf hfa
  by_cases hce : c = e
  · subst e
    by_cases hdf : d = f
    · subst f
      exact contains_positiveB C ha hb hc hd hab hac had hbe hbf hcd
    · exact contains_positiveH C ha hb hd hc hf hab had hac hbe hbf
        hcd.symm hdf hef
  · by_cases hcf : c = f
    · subst f
      by_cases hde : d = e
      · subst e
        exact contains_positiveB C ha hb hc hd hab hac had hbf hbe hcd
      · exact contains_positiveH C ha hb hd hc he hab had hac hbf hbe
          hcd.symm hde hce
    · by_cases hde : d = e
      · subst e
        exact contains_positiveH C ha hb hc hd hf hab hac had hbe hbf
          hcd hcf hef
      · by_cases hdf : d = f
        · subst f
          exact contains_positiveH C ha hb hc hd he hab hac had hbf hbe
            hcd hce hde
        · exact contains_positiveK C ha hb hc hd he hf hab hac had hbe hbf
            hcd hef hce hcf hde hdf

end Subcubic
