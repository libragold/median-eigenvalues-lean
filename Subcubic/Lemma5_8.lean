import Subcubic.Lemma5_8.Case2_2
import Subcubic.Lemma5_6

/-!
# Lemma 5.8

The negative-tail analogue of Lemma 4.7. Distance bounds are omitted.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem color_ne {C : MatchingCutColoring G} {x y : V} {cx cy : Color}
    (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
  intro h
  subst y
  simp_all

omit [Fintype V] in
private theorem FormsInducedCycle8.rotate2
    {a b c d e f g h : V} (hc : FormsInducedCycle8 G a b c d e f g h) :
    FormsInducedCycle8 G c d e f g h a b := by
  classical
  dsimp [FormsInducedCycle8] at hc ⊢
  rcases hc with ⟨hinj, hedge⟩
  let ι : Fin 8 → Fin 8 := ![2, 3, 4, 5, 6, 7, 0, 1]
  have hι : Function.Injective ι := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ι]
  have hmap (x : Fin 8) :
      ![c, d, e, f, g, h, a, b] x = ![a, b, c, d, e, f, g, h] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy; apply hι; apply hinj; simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

omit [Fintype V] in
private theorem FormsInducedCycle8.path6
    {a b c d e f g h : V} (hc : FormsInducedCycle8 G a b c d e f g h) :
    FormsInducedPath6 G a b c d e f := by
  classical
  dsimp [FormsInducedCycle8, FormsInducedPath6] at hc ⊢
  rcases hc with ⟨hinj, hedge⟩
  let ι : Fin 6 → Fin 8 := fun x => ⟨x, by omega⟩
  have hι : Function.Injective ι := by
    intro x y hxy; exact Fin.ext (by simpa [ι] using congrArg Fin.val hxy)
  have hmap (x : Fin 6) :
      ![a, b, c, d, e, f] x = ![a, b, c, d, e, f, g, h] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy; apply hι; apply hinj; simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

private theorem current_of_swap_result (C : MatchingCutColoring G)
    (h : ContainsNegativeTailReducer C.swapSides ∨ ContainsCutEnhancer C.swapSides) :
    HasReachableNegativeReduction C := by
  apply HasReachableNegativeReduction.of_swapSides C
  rcases h with hn | hc
  · exact HasReachableNegativeReduction.of_current_ntr C.swapSides hn
  · exact HasReachableNegativeReduction.of_current_ce C.swapSides hc

/-- **Lemma 5.8.** The alternating induced eight-cycle has a reachable
negative tail reducer or cut enhancer. -/
theorem lemma5_8
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  have h0 := hcycle
  dsimp [FormsInducedCycle8] at h0
  rcases h0 with ⟨hinj, hedge⟩
  have hv {x y : Fin 8} (hxy : x ≠ y) :
      (![a,b,c,d,e,f,g,h] x) ≠ (![a,b,c,d,e,f,g,h] y) := hinj.ne hxy
  have edge (x y : Fin 8) (q : (graphOfEdges
      [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]).Adj x y) :
      G.Adj (![a,b,c,d,e,f,g,h] x) (![a,b,c,d,e,f,g,h] y) := (hedge x y).mp q
  have nonedge (x y : Fin 8) (q : ¬ (graphOfEdges
      [(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,0)]).Adj x y) :
      ¬ G.Adj (![a,b,c,d,e,f,g,h] x) (![a,b,c,d,e,f,g,h] y) :=
    fun hxy => q ((hedge x y).mpr hxy)
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hfg : G.Adj f g := edge 5 6 (by native_decide)
  have hgh : G.Adj g h := edge 6 7 (by native_decide)
  have hha : G.Adj h a := edge 7 0 (by native_decide)
  have doneCE (q : ContainsCutEnhancer C) :=
    HasReachableNegativeReduction.of_current_ce C q
  have doneNTR (q : ContainsNegativeTailReducer C) :=
    HasReachableNegativeReduction.of_current_ntr C q
  obtain ⟨p, hap, hpb, hph⟩ := C.exists_third_neighbor (degree_of_color (Or.inl ha))
    (hv (x := (1 : Fin 8)) (y := 7) (by decide))
  have hpSide := C.other_neighbor_of_red_is_blueSide ha hb hab hap hpb
  rcases lemma3_3 C ha hh hg hpSide hha.symm hap hgh.symm hph.symm
      (by intro q; subst p; exact (nonedge 0 6 (by native_decide)) hap) with hp | hce
  · obtain ⟨q, hbq, hqa, hqc⟩ := C.exists_third_neighbor (degree_of_color (Or.inl hb))
      (hv (x := (0 : Fin 8)) (y := 2) (by decide))
    have hqSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbq hqa
    rcases lemma3_3 C hb hc hd hqSide hbc hbq hcd hqc.symm
        (by intro z; subst q; exact (nonedge 1 3 (by native_decide)) hbq) with hq | hce
    · obtain ⟨r, her, hrf, hrd⟩ := C.exists_third_neighbor (degree_of_color (Or.inl he))
        (hv (x := (5 : Fin 8)) (y := 3) (by decide))
      have hrSide := C.other_neighbor_of_red_is_blueSide he hf hef her hrf
      rcases lemma3_3 C he hd hc hrSide hde.symm her hcd.symm hrd.symm
          (by intro z; subst r; exact (nonedge 4 2 (by native_decide)) her) with hr | hce
      · obtain ⟨s, hfs, hse, hsg⟩ := C.exists_third_neighbor (degree_of_color (Or.inl hf))
          (hv (x := (4 : Fin 8)) (y := 6) (by decide))
        have hsSide := C.other_neighbor_of_red_is_blueSide hf he hef.symm hfs hse
        rcases lemma3_3 C hf hg hh hsSide hfg hfs hgh hsg.symm
            (by intro z; subst s; exact (nonedge 5 7 (by native_decide)) hfs) with hs | hce
        · by_cases hpr : p = r
          · subst r
            have hceSwap := containsCutEnhancerB_of C.swapSides
              (by simp [hp]) (by simp [ha]) (by simp [hh]) (by simp [he]) (by simp [hd])
              hap.symm her.symm hha.symm hde.symm
              (C.bluish_not_adj_blueSide hp (Or.inl hh))
              (C.bluish_not_adj_blueSide hp (Or.inl hd))
              (by simpa using nonedge 0 4 (by native_decide))
              (by simpa using nonedge 0 3 (by native_decide))
              (by simpa using nonedge 7 4 (by native_decide))
              (by simpa using nonedge 7 3 (by native_decide))
            exact doneCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
          · by_cases hqs : q = s
            · subst s
              have hceSwap := containsCutEnhancerB_of C.swapSides
                (by simp [hq]) (by simp [hb]) (by simp [hc]) (by simp [hf]) (by simp [hg])
                hbq.symm hfs.symm hbc hfg
                (C.bluish_not_adj_blueSide hq (Or.inl hc))
                (C.bluish_not_adj_blueSide hq (Or.inl hg))
                (by simpa using nonedge 1 5 (by native_decide))
                (by simpa using nonedge 1 6 (by native_decide))
                (by simpa using nonedge 2 5 (by native_decide))
                (by simpa using nonedge 2 6 (by native_decide))
              exact doneCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
            · by_cases hqr : q = r
              · subst r
                rcases lemma5_6 C hcycle.path6 ha hb hc hd he hf with hnone | hfound
                · exact (hnone ⟨q, hbq, her⟩).elim
                · exact hfound
              · by_cases hps : p = s
                · subst s
                  rcases lemma5_6 C (hcycle.rotate2.rotate2.path6)
                    he hf hg hh ha hb with hnone | hfound
                  · exact (hnone ⟨p, hfs, hap⟩).elim
                  · exact hfound
                · obtain ⟨u, hcu, hub, hud⟩ := C.exists_third_neighbor (degree_of_color (Or.inr hc))
                    (hv (x := (1 : Fin 8)) (y := 3) (by decide))
                  have huSide := C.other_neighbor_of_blue_is_redSide hc hd hcd hcu hud
                  rcases lemma3_3_reversed C hc hb ha huSide hbc.symm hcu hab.symm
                      hub.symm (by intro z; subst u; exact (nonedge 2 0 (by native_decide)) hcu)
                      with hu | hce
                  · obtain ⟨v, hdv, hvc, hve⟩ := C.exists_third_neighbor (degree_of_color (Or.inr hd))
                        (hv (x := (2 : Fin 8)) (y := 4) (by decide))
                    have hvSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdv hvc
                    rcases lemma3_3_reversed C hd he hf hvSide hde hdv hef
                        hve.symm (by intro z; subst v; exact (nonedge 3 5 (by native_decide)) hdv)
                        with hvColor | hce
                    · obtain ⟨w, hgw, hwf, hwh⟩ := C.exists_third_neighbor (degree_of_color (Or.inr hg))
                          (hv (x := (5 : Fin 8)) (y := 7) (by decide))
                      have hwSide := C.other_neighbor_of_blue_is_redSide hg hh hgh hgw hwh
                      rcases lemma3_3_reversed C hg hf he hwSide hfg.symm hgw hef.symm
                          hwf.symm (by intro z; subst w; exact (nonedge 6 4 (by native_decide)) hgw)
                          with hw | hce
                      · obtain ⟨x, hhx, hxg, hxa⟩ := C.exists_third_neighbor (degree_of_color (Or.inr hh))
                            (hv (x := (6 : Fin 8)) (y := 0) (by decide))
                        have hxSide := C.other_neighbor_of_blue_is_redSide hh hg hgh.symm hhx hxg
                        rcases lemma3_3_reversed C hh ha hb hxSide hha hhx hab
                            hxa.symm (by intro z; subst x; exact (nonedge 7 1 (by native_decide)) hhx)
                            with hx | hce
                        · by_cases huw : u = w
                          · subst w
                            exact doneCE (containsCutEnhancerB_of C hu hc hb hg hf
                              hcu.symm hgw.symm hbc.symm hfg.symm
                              (C.reddish_not_adj_redSide hu (Or.inl hb))
                              (C.reddish_not_adj_redSide hu (Or.inl hf))
                              (by simpa using nonedge 2 6 (by native_decide))
                              (by simpa using nonedge 2 5 (by native_decide))
                              (by simpa using nonedge 1 6 (by native_decide))
                              (by simpa using nonedge 1 5 (by native_decide)))
                          · by_cases hvx : v = x
                            · subst x
                              exact doneCE (containsCutEnhancerB_of C hvColor hd he hh ha
                                hdv.symm hhx.symm hde hha
                                (C.reddish_not_adj_redSide hvColor (Or.inl he))
                                (C.reddish_not_adj_redSide hvColor (Or.inl ha))
                                (by simpa using nonedge 3 7 (by native_decide))
                                (by simpa using nonedge 3 0 (by native_decide))
                                (by simpa using nonedge 4 7 (by native_decide))
                                (by simpa using nonedge 4 0 (by native_decide)))
                            · by_cases hvw : v = w
                              · subst w
                                rcases lemma5_6 C.swapSides hcycle.rotate2.path6
                                  (by simp [hc]) (by simp [hd]) (by simp [he]) (by simp [hf])
                                  (by simp [hg]) (by simp [hh]) with hnone | hfound
                                · exact (hnone ⟨v, hdv, hgw⟩).elim
                                · exact HasReachableNegativeReduction.of_swapSides C hfound
                              · by_cases hux : u = x
                                · subst x
                                  rcases lemma5_6 C.swapSides
                                    (hcycle.rotate2.rotate2.rotate2.path6)
                                    (by simp [hg]) (by simp [hh]) (by simp [ha]) (by simp [hb])
                                    (by simp [hc]) (by simp [hd]) with hnone | hfound
                                  · exact (hnone ⟨u, hhx, hcu⟩).elim
                                  · exact HasReachableNegativeReduction.of_swapSides C hfound
                                · by_cases hpq : p = q
                                  · subst q
                                    by_cases hrs : r = s
                                    · subst s
                                      by_cases huv : u = v
                                      · subst v
                                        by_cases hwx : w = x
                                        · subst x
                                          have hkg : ¬ G.Adj u g := by
                                            intro hug
                                            exact (not_adj_fourth_neighbor_of_degree_three
                                              (degree_of_color (Or.inr hg)) hfg.symm hgh hgw
                                              (color_ne hf hh (by decide))
                                              (color_ne hf hw (by decide))
                                              (color_ne hh hw (by decide))
                                              (color_ne hu hf (by decide))
                                              (color_ne hu hh (by decide)) huw) hug.symm
                                          have hkh : ¬ G.Adj u h := by
                                            intro huh
                                            exact (not_adj_fourth_neighbor_of_degree_three
                                              (degree_of_color (Or.inr hh)) hgh.symm hha hhx
                                              (color_ne hg ha (by decide))
                                              (color_ne hg hw (by decide))
                                              (color_ne ha hw (by decide))
                                              (color_ne hu hg (by decide))
                                              (color_ne hu ha (by decide)) hux) huh.symm
                                          exact lemma5_8_case2_2 C hcycle ha hb hc hd he hf hg hh hp hr hu
                                            hap hbq her hfs hcu hdv hkg hkh hpr
                                        · have hnSwap := lemma5_8_case2_1 C.swapSides hcycle.rotate2
                                              (by simp [hc]) (by simp [hd]) (by simp [he]) (by simp [hf])
                                              (by simp [hg]) (by simp [hh]) (by simp [ha]) (by simp [hb])
                                              (by simp [hu]) (by simp [hu]) (by simp [hw]) (by simp [hx])
                                              hcu hdv hgw hhx huw hvx hvw hux (Or.inr hwx)
                                          exact current_of_swap_result C (Or.inl hnSwap)
                                      · have hnSwap := lemma5_8_case2_1 C.swapSides hcycle.rotate2
                                            (by simp [hc]) (by simp [hd]) (by simp [he]) (by simp [hf])
                                            (by simp [hg]) (by simp [hh]) (by simp [ha]) (by simp [hb])
                                            (by simp [hu]) (by simp [hvColor]) (by simp [hw]) (by simp [hx])
                                            hcu hdv hgw hhx huw hvx hvw hux (Or.inl huv)
                                        exact current_of_swap_result C (Or.inl hnSwap)
                                    · exact doneNTR (lemma5_8_case2_1 C hcycle ha hb hc hd he hf hg hh
                                          hp hp hr hs hap hbq her hfs hpr hqs hqr hps (Or.inr hrs))
                                  · exact doneNTR (lemma5_8_case2_1 C hcycle ha hb hc hd he hf hg hh
                                        hp hq hr hs hap hbq her hfs hpr hqs hqr hps (Or.inl hpq))
                        · exact doneCE hce
                      · exact doneCE hce
                    · exact doneCE hce
                  · exact doneCE hce
        · exact doneCE hce
      · exact doneCE hce
    · exact doneCE hce
  · exact doneCE hce

end Subcubic
