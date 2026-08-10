import Subcubic.Lemma5_8.Case2_1
import Subcubic.Lemma5_4
import Subcubic.FlipLemmas

/-!
# Lemma 5.8, Case (2.2)

Both red edges share a bluish third neighbor and, after color symmetry, the
blue edge `cd` shares a reddish third neighbor `k`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem color_ne {C : GoodColoring G} {x y : V} {cx cy : Color}
    (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
  intro h
  subst y
  simp_all

private theorem case2_2_al
    (C : GoodColoring G) {a b c d e f g h i j k l : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .bluish) (hj : C.color j = .bluish)
    (hk : C.color k = .reddish) (hl : C.color l = .bluish)
    (hai : G.Adj a i) (hbi : G.Adj b i)
    (hej : G.Adj e j) (hfj : G.Adj f j)
    (hck : G.Adj c k) (hdk : G.Adj d k) (hkl : G.Adj k l)
    (hki : ¬ G.Adj k i) (hkg : ¬ G.Adj k g)
    (hkh : ¬ G.Adj k h) (hkj : ¬ G.Adj k j) (hij : i ≠ j) :
    ContainsNegativeTailReducer C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hcycleNodup : [a, b, c, d, e, f, g, h].Nodup := by
    simpa using List.nodup_ofFn_ofInjective hinj
  have edge (x y : Fin 8) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := (hedge x y).mp hxy
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have hha := edge 7 0 (by native_decide)
  have outBluish {z : V} (hz : C.color z = .bluish) :
      z ∉ [a, b, c, d, e, f, g, h] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨color_ne hz ha (by decide), color_ne hz hb (by decide),
      color_ne hz hc (by decide), color_ne hz hd (by decide),
      color_ne hz he (by decide), color_ne hz hf (by decide),
      color_ne hz hg (by decide), color_ne hz hh (by decide)⟩
  have hiout := outBluish hi
  have hjout := outBluish hj
  have hkout : k ∉ [a, b, c, d, e, f, g, h] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨color_ne hk ha (by decide), color_ne hk hb (by decide),
      color_ne hk hc (by decide), color_ne hk hd (by decide),
      color_ne hk he (by decide), color_ne hk hf (by decide),
      color_ne hk hg (by decide), color_ne hk hh (by decide)⟩
  have hlout := outBluish hl
  apply containsNegativeAm C hk ha hb he hf hl hi hc hd hg hh hj
    hkl hck.symm hdk.symm hab hai hha.symm hbi hbc
    hef hde.symm hej hfg hfj hcd hgh
    hki hkg hkh hkj
  simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil]
    at hcycleNodup hiout hjout hkout hlout ⊢
  grind

private theorem case2_2_o_left
    (C : GoodColoring G) {a b c d e f g h i j k : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hi : C.color i = .bluish) (hj : C.color j = .bluish)
    (hk : C.color k = .reddish)
    (hbi : G.Adj b i) (hei : G.Adj e j)
    (hck : G.Adj c k) (hdk : G.Adj d k) (hki : G.Adj k i)
    (hkj : ¬ G.Adj k j) : ContainsNegativeTailReducer C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hcycleNodup : [a, b, c, d, e, f, g, h].Nodup := by
    simpa using List.nodup_ofFn_ofInjective hinj
  have edge (x y : Fin 8) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := (hedge x y).mp hxy
  have nonedge (x y : Fin 8) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := fun hxyG => hxy ((hedge x y).mpr hxyG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hbe : ¬ G.Adj b e := by simpa using nonedge 1 4 (by native_decide)
  have hkb : ¬ G.Adj k b := fun h => C.reddish_not_adj_redSide hk (Or.inl hb) h
  have hke : ¬ G.Adj k e := fun h => C.reddish_not_adj_redSide hk (Or.inl he) h
  have hbj : ¬ G.Adj b j := by
    apply not_adj_fourth_neighbor_of_degree_three (C.red_or_blue_degree b (Or.inl hb))
      hab.symm hbc hbi
    · exact hinj.ne (show (0 : Fin 8) ≠ 2 by decide)
    · exact color_ne ha hi (by decide)
    · exact color_ne hc hi (by decide)
    · exact color_ne hj ha (by decide)
    · exact color_ne hj hc (by decide)
    · intro h
      subst j
      exact hkj hki
  have hei' : ¬ G.Adj e i := by
    apply not_adj_fourth_neighbor_of_degree_three (C.red_or_blue_degree e (Or.inl he))
      hde.symm hef hei
    · exact hinj.ne (show (3 : Fin 8) ≠ 5 by decide)
    · exact color_ne hd hj (by decide)
    · exact color_ne hf hj (by decide)
    · exact color_ne hi hd (by decide)
    · exact color_ne hi hf (by decide)
    · intro h
      subst j
      exact hkj hki
  have hbeV : b ≠ e := hinj.ne (show (1 : Fin 8) ≠ 4 by decide)
  have hcdV : c ≠ d := hinj.ne (show (2 : Fin 8) ≠ 3 by decide)
  have hijV : i ≠ j := by intro h; subst j; exact hkj hki
  have hn : [k, b, e, i, c, d, j].Nodup := by
    simp [color_ne hk hb (by decide), color_ne hk he (by decide),
      color_ne hk hi (by decide), color_ne hk hc (by decide),
      color_ne hk hd (by decide), color_ne hk hj (by decide),
      color_ne hb hi (by decide), color_ne hb hc (by decide),
      color_ne hb hd (by decide), color_ne hb hj (by decide),
      color_ne he hi (by decide), color_ne he hc (by decide),
      color_ne he hd (by decide), color_ne he hj (by decide),
      color_ne hi hc (by decide), color_ne hi hd (by decide),
      color_ne hc hj (by decide), color_ne hd hj (by decide),
      hbeV, hcdV, hijV]
  exact containsNegativeO C hk hb he hi hc hd hj hki hck.symm hdk.symm hbi hbc
    hde.symm hei hcd hkb hke hkj hbe hbj hei' hn

/-- The CE(b) exclusion used twice in Case (2.2.2.2.2). -/
private theorem red_neighbor_not_shared_or_ce
    (C : GoodColoring G) {rMate r b bMate x y l m o : V}
    (hrMate : C.color rMate = .red) (hr : C.color r = .red)
    (hb : C.color b = .blue) (hbMate : C.color bMate = .blue)
    (hx : C.color x = .bluish) (hl : C.color l = .blue)
    (hy : C.color y = .blue) (hm : C.color m = .blue) (ho : C.color o = .red)
    (hrMateR : G.Adj rMate r) (hrb : G.Adj r b) (hrx : G.Adj r x)
    (hrMateY : G.Adj rMate y) (hrMateX : G.Adj rMate x)
    (hbMateEdge : G.Adj b bMate) (hlm : G.Adj l m)
    (hmo : G.Adj m o) (hbl : bMate ≠ l) (hbl0 : b ≠ l)
    (hmy : m ≠ y) :
    ¬ G.Adj o x ∨ ContainsCutEnhancer C := by
  classical
  by_cases hox : G.Adj o x
  · right
    have hmb : m ≠ b := by
      intro hmb
      subst m
      exact (C.blueSide_not_adj_second_neighbor (by simp [hb])
        (by simp [hbMate]) (by simp [hl]) hbMateEdge hbl) hlm.symm
    have hrm : ¬ G.Adj r m := by
      apply not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree r (Or.inl hr)) hrMateR.symm hrb hrx
      · exact color_ne hrMate hb (by decide)
      · exact color_ne hrMate hx (by decide)
      · exact color_ne hb hx (by decide)
      · exact color_ne hm hrMate (by decide)
      · exact hmb
      · exact color_ne hm hx (by decide)
    have hor : o ≠ r := by intro q; subst o; exact hrm hmo.symm
    have hrMateM : ¬ G.Adj rMate m := by
      apply not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree rMate (Or.inl hrMate)) hrMateR hrMateY hrMateX
      · exact color_ne hr hy (by decide)
      · exact color_ne hr hx (by decide)
      · exact color_ne hy hx (by decide)
      · exact color_ne hm hr (by decide)
      · exact hmy
      · exact color_ne hm hx (by decide)
    have hrMateO : rMate ≠ o := by intro q; subst o; exact hrMateM hmo.symm
    have hro : ¬ G.Adj r o :=
      C.redSide_not_adj_second_neighbor (by simp [hr]) (by simp [hrMate])
        (by simp [ho]) hrMateR.symm hrMateO
    have hob : ¬ G.Adj o b := by
      have hcorrect := C.color_correct o
      rw [ho] at hcorrect
      obtain ⟨_, t, htSide, hot⟩ := hcorrect
      have ht : C.color t = .red := by
        have ht' := (C.mem_redSide_iff t).1 htSide
        rcases ht' with ht | ht
        · exact ht
        · exact (C.reddish_not_adj_redSide ht (Or.inl ho) hot.symm).elim
      apply not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree o (Or.inl ho)) hot hmo.symm hox
      · exact color_ne ht hm (by decide)
      · exact color_ne ht hx (by decide)
      · exact color_ne hm hx (by decide)
      · exact color_ne hb ht (by decide)
      · exact hmb.symm
      · exact color_ne hb hx (by decide)
    have hbMatem : bMate ≠ m := by
      intro q
      subst m
      exact (C.blueSide_not_adj_second_neighbor (by simp [hbMate])
        (by simp [hb]) (by simp [hl]) hbMateEdge.symm hbl0) hlm.symm
    have hbm : ¬ G.Adj b m :=
      C.blueSide_not_adj_second_neighbor (by simp [hb]) (by simp [hbMate])
        (by simp [hm]) hbMateEdge hbMatem
    have hceSwap := containsCutEnhancerB_of C.swapSides
      (by simp [hx]) (by simp [hr]) (by simp [hb]) (by simp [ho]) (by simp [hm])
      hrx.symm hox.symm hrb hmo.symm
      (by exact C.bluish_not_adj_blueSide hx (Or.inl hb))
      (by exact C.bluish_not_adj_blueSide hx (Or.inl hm))
      hro hrm (fun q => hob q.symm) hbm
    exact (containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap
  · exact Or.inl hox

private theorem case2_2_blue
    (C : GoodColoring G) {a b c d e f g h i j k l : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .bluish) (hj : C.color j = .bluish)
    (hk : C.color k = .reddish) (hl : C.color l = .blue)
    (hai : G.Adj a i) (hbi : G.Adj b i)
    (hej : G.Adj e j) (hfj : G.Adj f j)
    (hck : G.Adj c k) (hdk : G.Adj d k) (hkl : G.Adj k l)
    (hlc : l ≠ c) (hldV : l ≠ d)
    (hki : ¬ G.Adj k i) (hkg : ¬ G.Adj k g)
    (hkh : ¬ G.Adj k h) (hkj : ¬ G.Adj k j)
    (hij : i ≠ j) (hkdeg : vertexDegree G k = 3) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hp : FormsInducedCycle8 G a b c d e f g h := ⟨hinj, hedge⟩
  have edge (x y : Fin 8) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hfg : G.Adj f g := edge 5 6 (by native_decide)
  have hgh : G.Adj g h := edge 6 7 (by native_decide)
  have hha : G.Adj h a := edge 7 0 (by native_decide)
  have hlCorrect := C.color_correct l
  rw [hl] at hlCorrect
  obtain ⟨_, m, hmSide, hlm⟩ := hlCorrect
  have hmSide' := (C.not_mem_redSide_iff m).1 hmSide
  have hm : C.color m = .blue := by
    rcases hmSide' with hm | hm
    · exact hm
    · exact (C.bluish_not_adj_blueSide hm (Or.inl hl) hlm.symm).elim
  have hmc : m ≠ c := by
    intro hmc
    subst m
    exact (C.blueSide_not_adj_second_neighbor (by simp [hc]) (by simp [hd])
      (by simp [hl]) hcd hldV.symm) hlm.symm
  have hmd : m ≠ d := by
    intro hmd
    subst m
    exact (C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
      (by simp [hl]) hcd.symm hlc.symm) hlm.symm
  have hkm : ¬ G.Adj k m := by
    apply not_adj_fourth_neighbor_of_degree_three hkdeg hck.symm hdk.symm hkl
    · exact hcd.ne
    · exact hlc.symm
    · exact hldV.symm
    · exact hmc
    · exact hmd
    · exact hlm.ne.symm
  obtain ⟨n, hln, hnk, hnm⟩ :=
    exists_third_neighbor_of_degree_three (C.red_or_blue_degree l (Or.inr hl))
      (color_ne hk hm (by decide))
  have hnSide := C.other_neighbor_of_blue_is_redSide hl hm hlm hln hnm
  rcases hnSide with hn | hn
  · have hld : ¬ G.Adj l d := by
      exact C.blueSide_not_adj_second_neighbor (by simp [hl]) (by simp [hm])
        (by simp [hd]) hlm hmd
    have hle : ¬ G.Adj l e := by
      intro hle
      exact (not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree e (Or.inl he)) hde.symm hef hej
        (hinj.ne (show (3 : Fin 8) ≠ 5 by decide))
        (color_ne hd hj (by decide)) (color_ne hf hj (by decide))
        hldV (color_ne hl hf (by decide))
        (color_ne hl hj (by decide))) hle.symm
    have hnd : ¬ G.Adj n d := by
      intro hnd
      exact (not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree d (Or.inr hd)) hcd.symm hde hdk
        (color_ne hc he (by decide)) (color_ne hc hk (by decide))
        (color_ne he hk (by decide)) (color_ne hn hc (by decide))
        (by intro hne; subst n; exact hle hln) hnk) hnd.symm
    have hlf : ¬ G.Adj l f := by
      intro hlf
      exact (not_adj_fourth_neighbor_of_degree_three
        (C.red_or_blue_degree f (Or.inl hf)) hef.symm hfg hfj
        (color_ne he hg (by decide)) (color_ne he hj (by decide))
        (color_ne hg hj (by decide)) (color_ne hl he (by decide))
        (by intro q; subst l; exact hkg hkl) (color_ne hl hj (by decide))) hlf.symm
    have hne : ¬ G.Adj n e := by
      have hnE : n ≠ e := by intro q; subst n; exact hle hln
      have hnF : n ≠ f := by intro q; subst n; exact hlf hln
      intro hne
      exact (C.redSide_not_adj_second_neighbor (by simp [he]) (by simp [hf])
        (by simp [hn]) hef hnF.symm) hne.symm
    exact HasReachableNegativeReduction.of_current_ce C
      (containsCutEnhancerB_of C hk hl hn hd he hkl hdk.symm hln hde
        (fun q => C.reddish_not_adj_redSide hk (Or.inl hn) q)
        (fun q => C.reddish_not_adj_redSide hk (Or.inl he) q)
        hld hle hnd hne)
  · by_cases hred : ∃ o, C.color o = .red ∧ G.Adj m o
    · obtain ⟨o, ho, hmo⟩ := hred
      have hmg : m ≠ g := by
        intro q
        subst m
        exact (C.blueSide_not_adj_second_neighbor (by simp [hg]) (by simp [hh])
          (by simp [hl]) hgh (by intro q; subst l; exact hkh hkl)) hlm.symm
      have hmh : m ≠ h := by
        intro q
        subst m
        exact (C.blueSide_not_adj_second_neighbor (by simp [hh]) (by simp [hg])
          (by simp [hl]) hgh.symm (by intro q; subst l; exact hkg hkl)) hlm.symm
      rcases red_neighbor_not_shared_or_ce C ha hb hc hd hi hl hh hm ho
          hab hbc hbi hha.symm hai hcd hlm hmo hldV.symm hlc.symm hmh with
        hoi | hce
      · rcases red_neighbor_not_shared_or_ce C he hf hg hh hj hl hd hm ho
            hef hfg hfj hde.symm hej hgh hlm hmo
            (by intro q; subst l; exact hkh hkl)
            (by intro q; subst l; exact hkg hkl) hmd with hoj | hce
        · have hoCorrect := C.color_correct o
          rw [ho] at hoCorrect
          obtain ⟨_, t, htSide, hot⟩ := hoCorrect
          have ht : C.color t = .red := by
            have ht' := (C.mem_redSide_iff t).1 htSide
            rcases ht' with ht | ht
            · exact ht
            · exact (C.reddish_not_adj_redSide ht (Or.inl ho) hot.symm).elim
          rcases exists_flipAt_or_cutEnhancer C ho hm ht hl hot hmo.symm hlm.symm with
            ⟨M, hflip⟩ | hce
          · let D := M.toGoodColoring
            have hoa : o ≠ a := by intro q; subst o; exact hoi hai
            have hob : o ≠ b := by intro q; subst o; exact hoi hbi
            have hoe : o ≠ e := by intro q; subst o; exact hoj hej
            have hof : o ≠ f := by intro q; subst o; exact hoj hfj
            have hma := color_ne hm ha (by decide)
            have hmb := color_ne hm hb (by decide)
            have hme := color_ne hm he (by decide)
            have hmf := color_ne hm hf (by decide)
            have haD : D.color a = .red :=
              red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
                hoa.symm hma.symm hob.symm hmb.symm
            have hbD : D.color b = .red :=
              red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
                hob.symm hmb.symm hoa.symm hma.symm
            have heD : D.color e = .red :=
              red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
                hoe.symm hme.symm hof.symm hmf.symm
            have hfD : D.color f = .red :=
              red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
                hof.symm hmf.symm hoe.symm hme.symm
            have hcD : D.color c = .blue :=
              blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
                (color_ne hc ho (by decide)) hmc.symm (color_ne hd ho (by decide)) hmd.symm
            have hdD : D.color d = .blue :=
              blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
                (color_ne hd ho (by decide)) hmd.symm (color_ne hc ho (by decide)) hmc.symm
            have hgD : D.color g = .blue :=
              blue_of_untouched_blue_edge C hflip (by simp [hg]) (by simp [hh]) hgh
                (color_ne hg ho (by decide)) hmg.symm (color_ne hh ho (by decide)) hmh.symm
            have hhD : D.color h = .blue :=
              blue_of_untouched_blue_edge C hflip (by simp [hh]) (by simp [hg]) hgh.symm
                (color_ne hh ho (by decide)) hmh.symm (color_ne hg ho (by decide)) hmg.symm
            have hiD : D.color i = .bluish :=
              bluish_of_untouched_bluish C hflip hi (fun q => hoi q.symm)
                (color_ne hi ho (by decide)) (color_ne hi hm (by decide))
            have hjD : D.color j = .bluish :=
              bluish_of_untouched_bluish C hflip hj (fun q => hoj q.symm)
                (color_ne hj ho (by decide)) (color_ne hj hm (by decide))
            have hkD : D.color k = .reddish :=
              reddish_of_untouched_reddish C hflip hk hkm
                (color_ne hk ho (by decide)) (color_ne hk hm (by decide))
            have hlo : ¬ G.Adj l o := by
              apply not_adj_fourth_neighbor_of_degree_three
                (C.red_or_blue_degree l (Or.inr hl)) hkl.symm hlm hln
              · exact color_ne hk hm (by decide)
              · exact hnk.symm
              · exact hnm.symm
              · exact color_ne ho hk (by decide)
              · exact color_ne ho hm (by decide)
              · exact color_ne ho hn (by decide)
            have hlD : D.color l = .bluish :=
              bluish_of_blue_loses_flipped_mate C hflip hl hlm hlo
                (color_ne hl ho (by decide)) hlm.ne
            have hntrD := case2_2_al D hp haD hbD hcD hdD heD hfD hgD hhD
              hiD hjD hkD hlD hai hbi hej hfj hck hdk hkl hki hkg hkh hkj hij
            exact HasReachableNegativeReduction.after_flip C hflip
              (HasReachableNegativeReduction.of_current_ntr D hntrD)
          · exact HasReachableNegativeReduction.of_current_ce C hce
        · exact HasReachableNegativeReduction.of_current_ce C hce
      · exact HasReachableNegativeReduction.of_current_ce C hce
    · have hm_other : ∀ z, G.Adj m z → z ≠ l →
          C.swapSides.color z = .bluish := by
        intro z hmz hzl
        have hzSide := C.other_neighbor_of_blue_is_redSide hm hl hlm.symm hmz hzl
        rcases hzSide with hz | hz
        · exact (hred ⟨z, hz, hmz⟩).elim
        · simp [hz]
      have hl_other : ∀ z, G.Adj l z → z ≠ m →
          C.swapSides.color z = .bluish := by
        intro z hlz hzm
        have hz := C.neighbor_eq_of_three_neighbors (Or.inr hl)
          hkl.symm hlm hln (color_ne hk hm (by decide)) hnk.symm hnm.symm hlz
        rcases hz with rfl | rfl | rfl
        · simp [hk]
        · exact (hzm rfl).elim
        · simp [hn]
      exact HasReachableNegativeReduction.of_swapSides C
        (lemma5_4 C.swapSides (by simp [hl]) (by simp [hm]) hlm
          hl_other hm_other)

omit [Fintype V] in
private theorem FormsInducedCycle8.reverseShift
    {a b c d e f g h : V} (hc : FormsInducedCycle8 G a b c d e f g h) :
    FormsInducedCycle8 G f e d c b a h g := by
  classical
  dsimp [FormsInducedCycle8] at hc ⊢
  rcases hc with ⟨hinj, hedge⟩
  let ι : Fin 8 → Fin 8 := ![5, 4, 3, 2, 1, 0, 7, 6]
  have hι : Function.Injective ι := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ι]
  have hmap (x : Fin 8) :
      ![f, e, d, c, b, a, h, g] x = ![a, b, c, d, e, f, g, h] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hι
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

/-- Case (2.2), through the split on the third neighbor of `k`. -/
theorem lemma5_8_case2_2
    (C : GoodColoring G) {a b c d e f g h i j k : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .bluish) (hj : C.color j = .bluish)
    (hk : C.color k = .reddish)
    (hai : G.Adj a i) (hbi : G.Adj b i)
    (hej : G.Adj e j) (hfj : G.Adj f j)
    (hck : G.Adj c k) (hdk : G.Adj d k)
    (hkg : ¬ G.Adj k g) (hkh : ¬ G.Adj k h) (hij : i ≠ j) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hp : FormsInducedCycle8 G a b c d e f g h := ⟨hinj, hedge⟩
  have edge (x y : Fin 8) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hfg : G.Adj f g := edge 5 6 (by native_decide)
  have hgh : G.Adj g h := edge 6 7 (by native_decide)
  have hha : G.Adj h a := edge 7 0 (by native_decide)
  have current_ntr (hntr : ContainsNegativeTailReducer C) :
      HasReachableNegativeReduction C :=
    HasReachableNegativeReduction.of_current_ntr C hntr
  by_cases hki : G.Adj k i
  · exact current_ntr (case2_2_o_left C hp ha hb hc hd he hf hi hj hk
      hbi hej hck hdk hki (by
        intro hkj
        have hdeg := C.subcubic k
        unfold vertexDegree at hdeg
        have hs : ({c, d, i, j} : Set V).ncard = 4 := by
          simp [hcd.ne, color_ne hc hi (by decide), color_ne hc hj (by decide),
            color_ne hd hi (by decide), color_ne hd hj (by decide), hij]
        have hsub : ({c, d, i, j} : Set V) ⊆ G.neighborSet k := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl | rfl | rfl
          · exact hck.symm
          · exact hdk.symm
          · exact hki
          · exact hkj
        have := Set.ncard_le_ncard hsub
        omega))
  · by_cases hkj : G.Adj k j
    · exact current_ntr (case2_2_o_left C hp.reverseShift hf he hd hc hb ha
        hj hi hk hej hbi hdk hck hkj hki)
    · rcases lemma3_5 C hb hc hk hbc hck with hkdeg | hce
      · obtain ⟨l, hkl, hlc, hld⟩ :=
          exists_third_neighbor_of_degree_three hkdeg hcd.ne
        have hlSide : C.color l = .blue ∨ C.color l = .bluish := by
          rw [← C.not_mem_redSide_iff]
          intro hlRed
          exact (C.reddish_not_adj_redSide hk
            ((C.mem_redSide_iff l).1 hlRed) hkl).elim
        rcases hlSide with hl | hl
        · exact case2_2_blue C hp ha hb hc hd he hf hg hh hi hj hk hl
            hai hbi hej hfj hck hdk hkl hlc hld hki hkg hkh hkj hij hkdeg
        · exact current_ntr (case2_2_al C hp ha hb hc hd he hf hg hh hi hj
            hk hl hai hbi hej hfj hck hdk hkl hki hkg hkh hkj hij)
      · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
