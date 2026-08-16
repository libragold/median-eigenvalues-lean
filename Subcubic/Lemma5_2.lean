import Subcubic.NegativeTailReducerWitnesses
import Subcubic.Lemma3_7
import Subcubic.NegativeReduction

/-!
# Lemma 5.2

This is the negative-tail analogue of Lemma 4.2.  The two crossing edges
either share an endpoint, immediately giving `ntr-a`, or form a matching.
The matching case follows the corresponding reducers in `tail_reducers.cvs`.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem color_ne {C : MatchingCutColoring G} {x y : V} {cx cy : Color}
    (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
  intro h
  subst y
  simp_all

/-- Two crossings sharing their red endpoint give reducer `ntr-a`. -/
private theorem shared_red_endpoint
    (C : MatchingCutColoring G) {a c d : V}
    (ha : C.color a = .red) (hc : C.color c = .blue)
    (hd : C.color d = .blue) (hcd : G.Adj c d)
    (hac : G.Adj a c) (had : G.Adj a d) :
    ContainsNegativeTailReducer C := by
  have hn : [a, c, d].Nodup := by
    simp [hcd.ne, color_ne ha hc (by decide), color_ne ha hd (by decide)]
  exact containsNegativeA C ha hc hd hac had hcd hn

/-- In a crossing matching, the third neighbor of `b` is not
also adjacent to `a`. -/
private theorem matching_open
    (C : MatchingCutColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .bluish)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (hbd : G.Adj b d)
    (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c)
    (hbe : G.Adj b e) (hea : ¬ G.Adj e a)
    (heaV : e ≠ a) (hedV : e ≠ d) :
    ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C := by
  by_contra hno
  apply hno
  have haDegree : vertexDegree G a = 3 := by
    rcases lemma3_6_negative C (Or.inl ha) with hdegree | hfound
    · exact hdegree
    · exact (hno hfound).elim
  have hbcV : b ≠ c := by intro h; subst c; simp_all
  obtain ⟨f, haf, hfb, hfc⟩ :=
    C.exists_third_neighbor haDegree hbcV
  have hfSide := C.other_neighbor_of_red_is_blueSide ha hb hab haf hfb
  have hfdV : d ≠ f := by
    intro h
    subst f
    exact had haf
  rcases lemma3_3 C ha hc hd hfSide hac haf hcd hfc.symm hfdV with
      hf | hce
  · left
    have hfe : f ≠ e := by
      intro h
      subst f
      exact hea haf.symm
    have hceV : c ≠ e := by
      intro h
      subst e
      exact hbc hbe
    have hn : [a, b, f, c, d, e].Nodup := by
      simp [hab.ne, haf.ne, hfb.symm, hcd.ne, hfc, hfdV.symm, hfe,
        heaV.symm, hbe.ne, hceV, hedV.symm,
        color_ne ha hc (by decide), color_ne ha hd (by decide),
        color_ne hb hc (by decide), color_ne hb hd (by decide)]
    exact containsNegativeF C ha hb hf hc hd he
      hab haf hac hbd hbe hcd hn
  · exact Or.inr hce

/-- The canonical matching case: the crossing edges are `ac` and `bd`. -/
private theorem crossing_matching
    (C : MatchingCutColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : G.Adj a c) (hbd : G.Adj b d)
    (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c)
    (hNoReach : ¬ HasReachableNegativeReduction C) :
    ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C := by
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hNoReach (.of_current_ntr C hntr)).elim
    · exact (hNoReach (.of_current_ce C hce)).elim
  have hadV : a ≠ d := color_ne ha hd (by decide)
  obtain ⟨e, hbe, heaV, hedV⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inl hb)) hadV
  have heSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbe heaV
  have hceV : c ≠ e := by
    intro h
    subst e
    exact hbc hbe
  rcases lemma3_3 C hb hd hc heSide hbd hbe hcd.symm hedV.symm hceV with
      he | hce
  · by_cases hea : G.Adj e a
    · have hcbV : c ≠ b := color_ne hc hb (by decide)
      obtain ⟨f, hdf, hfcV, hfbV⟩ :=
        C.exists_third_neighbor (degree_of_color (Or.inr hd)) hcbV
      have hfSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdf hfcV
      have hfaV : a ≠ f := by
        intro h
        subst f
        exact had hdf.symm
      rcases lemma3_3_reversed C hd hb ha hfSide hbd.symm hdf hab.symm
          hfbV.symm hfaV with hf | hce
      · by_cases hfc : G.Adj f c
        · rcases lemma3_7 C.swapSides
            (by simp [hd]) (by simp [hb]) (by simp [he])
            hbd.symm hbe with hedeg | hce
          · by_cases hef : G.Adj e f
            · left
              have hn : [a, b, f, c, d, e].Nodup := by
                simp [hab.ne, hcd.ne, hfcV, hfbV.symm, hfaV,
                  heaV.symm, hbe.ne, hef.ne.symm, hceV, hedV.symm,
                  color_ne ha hc (by decide), color_ne ha hd (by decide),
                  color_ne hb hc (by decide), color_ne hb hd (by decide),
                  color_ne hf hd (by decide)]
              exact containsNegativeK C ha hb hf hc hd he
                hab hac hea.symm hbd hbe hfc hdf.symm hef.symm hcd hn
            · obtain ⟨g, heg, hgb, hga⟩ :=
                exists_third_neighbor_of_degree_three hedeg hab.ne
              have hgSide : C.color g = .red ∨ C.color g = .reddish := by
                rw [← C.mem_redSide_iff]
                by_contra hgmem
                exact (C.bluish_not_adj_blueSide he
                  ((C.not_mem_redSide_iff g).1 hgmem)) heg
              rcases hgSide with hg | hg
              · have hgCorrect := C.color_correct g
                rw [hg] at hgCorrect
                obtain ⟨_, r, hrSide, hgr⟩ := hgCorrect
                have hrCases := (C.mem_redSide_iff r).1 hrSide
                have hr : C.color r = .red := by
                  rcases hrCases with hr | hr
                  · exact hr
                  · exact (C.reddish_not_adj_redSide hr (Or.inl hg)
                      hgr.symm).elim
                have hre : r ≠ e := color_ne hr he (by decide)
                obtain ⟨h, hgh, hhr, hhe⟩ :=
                  C.exists_third_neighbor (degree_of_color (Or.inl hg)) hre
                have hhSide :=
                  C.other_neighbor_of_red_is_blueSide hg hr hgr hgh hhr
                have hgf : g ≠ f := by
                  intro hgf
                  subst g
                  exact hef heg
                have hgc : ¬ G.Adj g c := by
                  apply fun h => (C.not_adj_fourth_neighbor (Or.inr hc)
                    hcd hac.symm hfc.symm
                    (color_ne hd ha (by decide))
                    (color_ne hd hf (by decide))
                    (color_ne ha hf (by decide))
                    (color_ne hg hd (by decide)) hgb hgf) h.symm
                have hgd : ¬ G.Adj g d := by
                  apply fun h => (C.not_adj_fourth_neighbor (Or.inr hd)
                    hcd.symm hbd.symm hdf
                    (color_ne hc hb (by decide))
                    (color_ne hc hf (by decide))
                    (color_ne hb hf (by decide))
                    (color_ne hg hc (by decide)) hga hgf) h.symm
                rcases hhSide with hh | hh
                · right
                  have heh : ¬ G.Adj e h :=
                    C.bluish_not_adj_blueSide he (Or.inl hh)
                  have hed : ¬ G.Adj e d :=
                    C.bluish_not_adj_blueSide he (Or.inl hd)
                  have hbg : ¬ G.Adj b g :=
                    C.redSide_not_adj_second_neighbor
                      (by simp [hb]) (by simp [ha]) (by simp [hg])
                      hab.symm hgb.symm
                  have hdhV : d ≠ h := by
                    intro hdh
                    subst h
                    exact hgd hgh
                  have hbh : ¬ G.Adj b h :=
                    C.not_adj_fourth_neighbor (Or.inl hb)
                      hab.symm hbd hbe
                      (color_ne ha hd (by decide))
                      heaV.symm (color_ne hd he (by decide))
                      (color_ne hh ha (by decide)) hdhV.symm
                      (color_ne hh he (by decide))
                  have hdh : ¬ G.Adj d h :=
                    C.blueSide_not_adj_second_neighbor
                      (by simp [hd]) (by simp [hc]) (by simp [hh])
                      hcd.symm (by
                        intro hch
                        subst h
                        exact hgc hgh)
                  have hceSwap := containsCutEnhancerB_of C.swapSides
                    (by simp [he]) (by simp [hb]) (by simp [hd])
                    (by simp [hg]) (by simp [hh])
                    hbe.symm heg hbd hgh hed heh hbg hbh
                    (fun h => hgd h.symm) hdh
                  exact (containsInducedUpToSwap_swapSides IsCutEnhancer C).1
                    hceSwap
                · left
                  have hn : [a, b, g, c, d, e, h].Nodup := by
                    simp [hab.ne, hgb.symm, hga.symm, hcd.ne, hedV.symm,
                      hhe.symm,
                      color_ne ha hc (by decide), color_ne ha hd (by decide),
                      color_ne ha he (by decide), color_ne ha hh (by decide),
                      color_ne hb hc (by decide), color_ne hb hd (by decide),
                      color_ne hb he (by decide), color_ne hb hh (by decide),
                      color_ne hg hc (by decide), color_ne hg hd (by decide),
                      color_ne hg he (by decide), color_ne hg hh (by decide),
                      color_ne hc he (by decide), color_ne hc hh (by decide),
                      color_ne hd hh (by decide)]
                  exact containsNegativeM C ha hb hg hc hd he hh
                    hab hac hea.symm hbd hbe heg.symm hgh hcd hgc hgd hn
              · left
                have hgf : g ≠ f := by
                  intro hgf
                  subst g
                  exact hef heg
                have hn : [c, d, e, a, b, f, g].Nodup := by
                  simp [hcd.ne, hceV, hab.ne,
                    hfaV, hgf.symm,
                    color_ne hc ha (by decide),
                    color_ne hc hb (by decide), color_ne hc hf (by decide),
                    color_ne hc hg (by decide), color_ne hd he (by decide),
                    color_ne hd ha (by decide), color_ne hd hb (by decide),
                    color_ne hd hf (by decide), color_ne hd hg (by decide),
                    color_ne he ha (by decide), color_ne he hb (by decide),
                    color_ne he hf (by decide), color_ne he hg (by decide),
                    color_ne ha hg (by decide),
                    color_ne hb hf (by decide), color_ne hb hg (by decide)]
                have hntrSwap := containsNegativeO C.swapSides
                  (by simp [hc]) (by simp [hd]) (by simp [he])
                  (by simp [ha]) (by simp [hb]) (by simp [hf])
                  (by simp [hg]) hcd hac.symm hfc.symm hbd.symm hdf hea
                  hbe.symm heg
                  hab hef hn
                exact (containsInducedUpToSwap_swapSides
                  IsNegativeTailReducer C).1 hntrSwap
          · have hnegSwap :=
              HasReachableNegativeReduction.of_lemma3_6 C.swapSides hce
            exact (hNoReach
              (HasReachableNegativeReduction.of_swapSides C hnegSwap)).elim
        · have hout := matching_open C.swapSides
            (by simp [hc]) (by simp [hd]) (by simp [ha]) (by simp [hb])
            (by simp [hf]) hcd hab hac.symm hbd.symm
            (fun h => hbc h.symm)
            (fun h => had h.symm) hdf hfc hfcV hfbV
          rcases hout with hntr | hce
          · exact Or.inl ((containsInducedUpToSwap_swapSides
              IsNegativeTailReducer C).1 hntr)
          · exact Or.inr ((containsInducedUpToSwap_swapSides
              IsCutEnhancer C).1 hce)
      · exact Or.inr hce
    · exact matching_open C ha hb hc hd he hab hcd hac hbd had hbc
        hbe hea heaV hedV
  · exact Or.inr hce

/-- **Lemma 5.2.** If a red edge and a blue edge have at least two crossing
edges between their endpoint pairs, then a negative tail reducer or cut
enhancer is reachable. -/
theorem lemma5_2
    (C : MatchingCutColoring G) (a b c d : V)
    (hab : G.Adj a b) (ha : C.color a = .red) (hb : C.color b = .red)
    (hcd : G.Adj c d) (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hmulti : 2 ≤ fourVertexCrossEdgeCount G a b c d) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have liftCurrent
      (h : ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C) :
      HasReachableNegativeReduction C := by
    rcases h with hntr | hce
    · exact .of_current_ntr C hntr
    · exact .of_current_ce C hce
  by_cases hac : G.Adj a c <;>
  by_cases had : G.Adj a d <;>
  by_cases hbc : G.Adj b c <;>
  by_cases hbd : G.Adj b d
  all_goals simp [fourVertexCrossEdgeCount, hac, had, hbc, hbd] at hmulti
  · exact .of_current_ntr C (shared_red_endpoint C ha hc hd hcd hac had)
  · exact .of_current_ntr C (shared_red_endpoint C ha hc hd hcd hac had)
  · exact .of_current_ntr C (shared_red_endpoint C ha hc hd hcd hac had)
  · exact .of_current_ntr C (shared_red_endpoint C ha hc hd hcd hac had)
  · exact .of_current_ntr C (shared_red_endpoint C hb hc hd hcd hbc hbd)
  · have hntr := shared_red_endpoint C.swapSides
        (by simp [hc]) (by simp [ha]) (by simp [hb]) hab hac.symm hbc.symm
    exact .of_current_ntr C ((containsInducedUpToSwap_swapSides
      IsNegativeTailReducer C).1 hntr)
  · exact liftCurrent
      (crossing_matching C ha hb hc hd hab hcd hac hbd had hbc hdone)
  · exact .of_current_ntr C (shared_red_endpoint C hb hc hd hcd hbc hbd)
  · exact liftCurrent
      (crossing_matching C ha hb hd hc hab hcd.symm had hbc hac hbd hdone)
  · have hntr := shared_red_endpoint C.swapSides
        (by simp [hd]) (by simp [ha]) (by simp [hb]) hab had.symm hbd.symm
    exact .of_current_ntr C ((containsInducedUpToSwap_swapSides
      IsNegativeTailReducer C).1 hntr)
  · exact .of_current_ntr C (shared_red_endpoint C hb hc hd hcd hbc hbd)

end Subcubic
