import Subcubic.Lemma4_10.SetupI
import Subcubic.Lemma4_6

/-!
# Lemma 4.10, Case (3.2.1)

One of the two neighbors of `i` outside `c,d` is blue.  After flipping
`bc`, the displayed vertices form the alternating path

`e-f-g-b-c-i-j-k`.

Extra edges between consecutive monochromatic blocks invoke Lemma 4.2.
The only possible extra edges between the end blocks invoke Lemma 3.3.
The induced configuration is then handled by Lemma 4.8 if `k` has no red
neighbor, and otherwise by extending through the red mate and using the
subgraph form of Lemma 4.6.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_10_case_3_2_1
    (C : MatchingCutColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma4_10IConfiguration C a b c d e f)
    {j : V} (hj : C.color j = .blue) (hij : G.Adj Q.i j)
    (hjc : j ≠ c) (hjd : j ≠ d) :
    HasReachableReduction C := by
  classical
  by_contra hresult
  have noCurrentCE (hce : ContainsCutEnhancer C) : False :=
    hresult (HasReachableReduction.of_current_ce C hce)
  have degreeC {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hresult (.of_current_ptr C hptr)).elim
    · exact (noCurrentCE hce).elim
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath6 G a b c d e f := ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) := hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    (hedge x y).mp hxy
  have nonedge (x y : Fin 6) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
  have hef : G.Adj e f := by simpa using edge 4 5 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all

  have hjCorrect := C.color_correct j
  rw [hj] at hjCorrect
  obtain ⟨_, k, hkSide, hjk⟩ := hjCorrect
  have hkSide' := (C.not_mem_redSide_iff k).1 hkSide
  have hk : C.color k = .blue := by
    rcases hkSide' with hk | hk
    · exact hk
    · exact (C.bluish_not_adj_blueSide hk (Or.inl hj) hjk.symm).elim
  have hjkV : j ≠ k := hjk.ne
  have hjb : j ≠ b := color_ne hj hb (by decide)
  have hkb : k ≠ b := color_ne hk hb (by decide)
  have hkc : k ≠ c := by
    intro h
    subst k
    have hcj : ¬ G.Adj c j :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hc]) (by simp [hd]) (by simp [hj]) hcd hjd.symm
    exact hcj hjk.symm
  have hdk : d ≠ k := by
    intro h
    subst k
    have hdj : ¬ G.Adj d j :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hd]) (by simp [hc]) (by simp [hj]) hcd.symm hjc.symm
    exact hdj hjk.symm

  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
      (degreeC (Or.inl hb)) (degreeC (Or.inr hc)) hab.symm hbc hcd with
    hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toColoring
    have noD (hout : HasReachableReduction D) : False :=
      hresult (HasReachableReduction.after_flip C hflip hout)

    have heD : D.color e = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
      · exact hv (x := (4 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 2) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 2) (by decide)
    have hfD : D.color f = .red := by
      apply red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
      · exact hv (x := (5 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (5 : Fin 6)) (y := 2) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (4 : Fin 6)) (y := 2) (by decide)
    have hbD : D.color b = .blue :=
      blue_of_flipped_red_endpoint C hflip ha hab.symm
        (degreeC (Or.inl hb))
        (hv (x := (0 : Fin 6)) (y := 2) (by decide))
    have hcD : D.color c = .red :=
      red_of_flipped_blue_endpoint C hflip hd hcd
        (degreeC (Or.inr hc))
        (hv (x := (3 : Fin 6)) (y := 1) (by decide))
    have hiD : D.color Q.i = .red :=
      red_of_reddish_gains_flipped_blue C hflip Q.hi Q.hci.symm
        Q.hib Q.hci.ne.symm
    have hgD : D.color Q.g = .blue :=
      blue_of_bluish_gains_flipped_red C hflip Q.hg Q.hbg.symm
        Q.hbg.ne.symm (color_ne Q.hg hc (by decide))
    have hjD : D.color j = .blue := by
      apply blue_of_untouched_blue_edge C hflip (by simp [hj]) (by simp [hk]) hjk
      · exact hjb
      · exact hjc
      · exact hkb
      · exact hkc
    have hkD : D.color k = .blue := by
      apply blue_of_untouched_blue_edge C hflip (by simp [hk]) (by simp [hj]) hjk.symm
      · exact hkb
      · exact hkc
      · exact hjb
      · exact hjc
    have hdD : D.color d = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip hd hcd.symm
      · simpa using nonedge 3 1 (by native_decide)
      · exact hv (x := (3 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (3 : Fin 6)) (y := 2) (by decide)
    have hhD : D.color Q.h = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hh Q.hhb
      · exact color_ne Q.hh hb (by decide)
      · exact color_ne Q.hh hc (by decide)

    have redNonedge {x mate y : V}
        (hx : D.color x = .red) (hm : D.color mate = .red)
        (hy : D.color y = .red) (hxm : G.Adj x mate) (hmy : mate ≠ y) :
        ¬ G.Adj x y :=
      D.redSide_not_adj_second_neighbor
        (by simp [hx]) (by simp [hm]) (by simp [hy]) hxm hmy
    have blueNonedge {x mate y : V}
        (hx : D.color x = .blue) (hm : D.color mate = .blue)
        (hy : D.color y = .blue) (hxm : G.Adj x mate) (hmy : mate ≠ y) :
        ¬ G.Adj x y :=
      D.blueSide_not_adj_second_neighbor
        (by simp [hx]) (by simp [hm]) (by simp [hy]) hxm hmy
    have color_neD {x y : V} {cx cy : Color}
        (hx : D.color x = cx) (hy : D.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
      intro h
      subst y
      simp_all

    have hec : ¬ G.Adj e c := redNonedge heD hfD hcD hef
      (hv (x := (5 : Fin 6)) (y := 2) (by decide))
    have hei : ¬ G.Adj e Q.i := redNonedge heD hfD hiD hef
      (color_ne hf Q.hi (by decide))
    have hfc : ¬ G.Adj f c := redNonedge hfD heD hcD hef.symm
      (hv (x := (4 : Fin 6)) (y := 2) (by decide))
    have hfi : ¬ G.Adj f Q.i := redNonedge hfD heD hiD hef.symm
      (color_ne he Q.hi (by decide))
    have hgj : ¬ G.Adj Q.g j := blueNonedge hgD hbD hjD Q.hbg.symm hjb.symm
    have hgk : ¬ G.Adj Q.g k := blueNonedge hgD hbD hkD Q.hbg.symm hkb.symm
    have hbj : ¬ G.Adj b j := blueNonedge hbD hgD hjD Q.hbg
      (color_ne Q.hg hj (by decide))
    have hbk : ¬ G.Adj b k := blueNonedge hbD hgD hkD Q.hbg
      (color_ne Q.hg hk (by decide))

    have heg : ¬ G.Adj e Q.g := by simpa [SimpleGraph.adj_comm] using Q.hge
    have heb : ¬ G.Adj e b := by simpa using nonedge 4 1 (by native_decide)
    have hfb : ¬ G.Adj f b := by simpa using nonedge 5 1 (by native_decide)
    have hcg : ¬ G.Adj c Q.g := by
      simpa [SimpleGraph.adj_comm] using
        C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
    have hig : ¬ G.Adj Q.i Q.g := Q.hig
    have hibAdj : ¬ G.Adj Q.i b :=
      C.reddish_not_adj_redSide Q.hi (Or.inl hb)
    have hcj : ¬ G.Adj c j :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hc]) (by simp [hd]) (by simp [hj]) hcd hjd.symm
    have hck : ¬ G.Adj c k :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hc]) (by simp [hd]) (by simp [hk]) hcd
          hdk

    have hfd : f ≠ d := hv (x := (5 : Fin 6)) (y := 3) (by decide)
    have hfh : f ≠ Q.h := color_ne hf Q.hh (by decide)
    have hdh : d ≠ Q.h := color_ne hd Q.hh (by decide)
    have hej : ¬ G.Adj e j := by
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        hfd hfh hdh
      · exact color_ne hj hf (by decide)
      · exact hjd
      · exact color_ne hj Q.hh (by decide)
    have hek : ¬ G.Adj e k := by
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        hfd hfh hdh
      · exact color_ne hk hf (by decide)
      · exact hdk.symm
      · exact color_ne hk Q.hh (by decide)

    by_cases hik : G.Adj Q.i k
    · have hmulti : 2 ≤ fourVertexCrossEdgeCount G c Q.i j k := by
        unfold fourVertexCrossEdgeCount
        rw [if_pos hij, if_pos hik]
        omega
      have hout := lemma4_2 D c Q.i j k Q.hci hcD hiD
        hjk hjD hkD hmulti
      exact (noD (hout.elim (HasReachableReduction.of_current_ptr D)
        (HasReachableReduction.of_current_ce D))).elim
    by_cases hfj : G.Adj f j
    · have hjg : j ≠ Q.g := color_ne hj Q.hg (by decide)
      have hkg : k ≠ Q.g := color_ne hk Q.hg (by decide)
      rcases lemma3_3 D hfD hjD hkD (Or.inl hgD) hfj Q.hgf.symm hjk
          hjg hkg with hgBluish | hceD
      · rw [hgD] at hgBluish
        contradiction
      · exact (noD (HasReachableReduction.of_current_ce D hceD)).elim
    by_cases hfk : G.Adj f k
    · have hkg : k ≠ Q.g := color_ne hk Q.hg (by decide)
      have hjg : j ≠ Q.g := color_ne hj Q.hg (by decide)
      rcases lemma3_3 D hfD hkD hjD (Or.inl hgD) hfk Q.hgf.symm hjk.symm
          hkg hjg with hgBluish | hceD
      · rw [hgD] at hgBluish
        contradiction
      · exact (noD (HasReachableReduction.of_current_ce D hceD)).elim

    have hefV : e ≠ f := hef.ne
    have hebV : e ≠ b := by
      simpa using hv (x := (4 : Fin 6)) (y := 1) (by decide)
    have hecV : e ≠ c := by
      simpa using hv (x := (4 : Fin 6)) (y := 2) (by decide)
    have hfbV : f ≠ b := by
      simpa using hv (x := (5 : Fin 6)) (y := 1) (by decide)
    have hfcV : f ≠ c := by
      simpa using hv (x := (5 : Fin 6)) (y := 2) (by decide)
    have coreNodup : [e, f, Q.g, b, c, Q.i, j, k].Nodup := by
      simp [hefV, hebV, hecV, hfbV, hfcV,
        color_ne he Q.hg (by decide), color_ne hf Q.hg (by decide),
        color_ne he Q.hi (by decide), color_ne he hj (by decide),
        color_ne he hk (by decide), color_ne hf Q.hi (by decide),
        color_ne hf hj (by decide), color_ne hf hk (by decide),
        color_ne Q.hg hb (by decide), color_ne Q.hg hc (by decide),
        color_ne Q.hg Q.hi (by decide), color_ne Q.hg hj (by decide),
        color_ne Q.hg hk (by decide), color_ne hb hc (by decide),
        color_ne hb Q.hi (by decide), color_ne hc Q.hi (by decide),
        color_ne Q.hi hj (by decide), color_ne Q.hi hk (by decide),
        hjb.symm, hkb.symm, hjc.symm, hkc.symm, hjkV]
    have hinduced : FormsInducedPath8 G e f Q.g b c Q.i j k := by
      refine ⟨?_, ?_⟩
      · have hvec : (![e, f, Q.g, b, c, Q.i, j, k] : Fin 8 → V) =
            [e, f, Q.g, b, c, Q.i, j, k].get := by
          funext x
          fin_cases x <;> rfl
        rw [hvec]
        exact coreNodup.injective_get
      · intro x y
        have hfg : G.Adj f Q.g := Q.hgf.symm
        have hfe : G.Adj f e := hef.symm
        have hgf : G.Adj Q.g f := Q.hgf
        have hgb : G.Adj Q.g b := Q.hbg.symm
        have hbg : G.Adj b Q.g := Q.hbg
        have hcb : G.Adj c b := hbc.symm
        have hic : G.Adj Q.i c := Q.hci.symm
        have hji : G.Adj j Q.i := hij.symm
        have hkj : G.Adj k j := hjk.symm
        have hbe : ¬ G.Adj b e := fun h => heb h.symm
        have hce : ¬ G.Adj c e := fun h => hec h.symm
        have hbf : ¬ G.Adj b f := fun h => hfb h.symm
        have hcf : ¬ G.Adj c f := fun h => hfc h.symm
        have hge : ¬ G.Adj Q.g e := fun h => heg h.symm
        have hif : ¬ G.Adj Q.i f := fun h => hfi h.symm
        have hkg : ¬ G.Adj k Q.g := fun h => hgk h.symm
        have hjb' : ¬ G.Adj j b := fun h => hbj h.symm
        have hkb' : ¬ G.Adj k b := fun h => hbk h.symm
        have hgc : ¬ G.Adj Q.g c := fun h => hcg h.symm
        have hgi : ¬ G.Adj Q.g Q.i := fun h => hig h.symm
        have hbi : ¬ G.Adj b Q.i := fun h => hibAdj h.symm
        have hjc' : ¬ G.Adj j c := fun h => hcj h.symm
        have hkc' : ¬ G.Adj k c := fun h => hck h.symm
        have hje : ¬ G.Adj j e := fun h => hej h.symm
        have hke : ¬ G.Adj k e := fun h => hek h.symm
        have hki : ¬ G.Adj k Q.i := fun h => hik h.symm
        have hjf' : ¬ G.Adj j f := fun h => hfj h.symm
        have hkf' : ¬ G.Adj k f := fun h => hfk h.symm
        have hie : ¬ G.Adj Q.i e := fun h => hei h.symm
        have hjg : ¬ G.Adj j Q.g := fun h => hgj h.symm
        fin_cases x <;> fin_cases y <;>
          simp [graphOfEdges, hef, hfe, hfg, hgf, hgb, hbg, hbc, hcb,
            Q.hci, hic, hij, hji, hjk, hkj,
            hbe, hce, hbf, hcf, hge, hif, hkg, hjb', hkb', hgc,
            hgi, hbi, hjc', hkc', hje, hke, hki, hjf', hkf',
            hec, hei, hfc, hfi, hgj, hgk, hbj, hbk, heg, heb, hfb,
            hcg, hig, hibAdj, hcj, hck, hej, hek, hik, hfj, hfk,
            hie, hjg]

    have hNoBlueAtE : ∀ z, G.Adj e z → D.color z ≠ .blue := by
      intro z hez hzblue
      rcases C.neighbor_eq_of_three_neighbors (Or.inl he)
          hef hde.symm Q.heh hfd hfh hdh hez with rfl | rfl | rfl
      · simp [hfD] at hzblue
      · simp [hdD] at hzblue
      · simp [hhD] at hzblue

    by_cases hNoRedAtK : ∀ z, G.Adj k z → D.color z ≠ .red
    · exact (noD (lemma4_8 D hinduced heD hfD hgD hbD hcD hiD hjD hkD
        hNoBlueAtE hNoRedAtK)).elim
    · push Not at hNoRedAtK
      obtain ⟨l, hkl, hl⟩ := hNoRedAtK
      have hlCorrect := D.color_correct l
      rw [hl] at hlCorrect
      obtain ⟨_, m, hmSide, hlm⟩ := hlCorrect
      have hmSide' := (D.mem_redSide_iff m).1 hmSide
      have hm : D.color m = .red := by
        rcases hmSide' with hm | hm
        · exact hm
        · exact (D.reddish_not_adj_redSide hm (Or.inl hl) hlm.symm).elim

      dsimp [FormsInducedPath8] at hinduced
      rcases hinduced with ⟨hcoreInj, hcoreEdges⟩
      have coreNonedge (x y : Fin 8) (hxy : ¬ (graphOfEdges
          [(0, 1), (1, 2), (2, 3), (3, 4),
           (4, 5), (5, 6), (6, 7)]).Adj x y) :
          ¬ G.Adj (![e, f, Q.g, b, c, Q.i, j, k] x)
            (![e, f, Q.g, b, c, Q.i, j, k] y) :=
        fun h => hxy ((hcoreEdges x y).mpr h)
      have lNotCore : l ∉ [e, f, Q.g, b, c, Q.i, j, k] := by
        have hle : l ≠ e := by
          intro h; subst l
          exact (coreNonedge 7 0 (by native_decide)) hkl
        have hlf : l ≠ f := by
          intro h; subst l
          exact (coreNonedge 7 1 (by native_decide)) hkl
        have hlc : l ≠ c := by
          intro h; subst l
          exact (coreNonedge 7 4 (by native_decide)) hkl
        have hli : l ≠ Q.i := by
          intro h; subst l
          exact (coreNonedge 7 5 (by native_decide)) hkl
        simp [hle, hlf, hlc, hli, color_neD hl hgD (by decide),
          color_neD hl hbD (by decide), color_neD hl hjD (by decide),
          color_neD hl hkD (by decide)]
      have lmV : l ≠ m := hlm.ne
      have me : m ≠ e := by
        intro h; subst m
        exact (redNonedge heD hfD hl hef
          (fun hfl => lNotCore (by simp [hfl]))) hlm.symm
      have mf : m ≠ f := by
        intro h; subst m
        exact (redNonedge hfD heD hl hef.symm
          (fun hel => lNotCore (by simp [hel]))) hlm.symm
      have mc : m ≠ c := by
        intro h; subst m
        exact (redNonedge hcD hiD hl Q.hci
          (fun hil => lNotCore (by simp [hil]))) hlm.symm
      have mi : m ≠ Q.i := by
        intro h; subst m
        exact (redNonedge hiD hcD hl Q.hci.symm
          (fun hcl => lNotCore (by simp [hcl]))) hlm.symm
      have mNotCore : m ∉ [e, f, Q.g, b, c, Q.i, j, k] := by
        simp [me, mf, mc, mi, color_neD hm hgD (by decide),
          color_neD hm hbD (by decide), color_neD hm hjD (by decide),
          color_neD hm hkD (by decide)]
      have path10Nodup : [e, f, Q.g, b, c, Q.i, j, k, l, m].Nodup := by
        have htail : [l, m].Nodup := by simp [lmV]
        rw [show [e, f, Q.g, b, c, Q.i, j, k, l, m] =
          [e, f, Q.g, b, c, Q.i, j, k] ++ [l, m] by rfl,
          List.nodup_append']
        refine ⟨coreNodup, htail, ?_⟩
        rw [List.disjoint_left]
        intro x hxCore hxTail
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxTail
        rcases hxTail with rfl | rfl
        · exact lNotCore hxCore
        · exact mNotCore hxCore
      have hsub : FormsPath10Subgraph G e f Q.g b c Q.i j k l m := by
        refine ⟨?_, ?_⟩
        · have hvec : (![e, f, Q.g, b, c, Q.i, j, k, l, m] : Fin 10 → V) =
              [e, f, Q.g, b, c, Q.i, j, k, l, m].get := by
            funext x
            fin_cases x <;> rfl
          rw [hvec]
          exact path10Nodup.injective_get
        · intro x y hxy
          have hfg : G.Adj f Q.g := Q.hgf.symm
          have hgb : G.Adj Q.g b := Q.hbg.symm
          have hbg : G.Adj b Q.g := Q.hbg
          have hci : G.Adj c Q.i := Q.hci
          have hic : G.Adj Q.i c := Q.hci.symm
          have hji : G.Adj j Q.i := hij.symm
          have hkj : G.Adj k j := hjk.symm
          have hlk : G.Adj l k := hkl.symm
          have hml : G.Adj m l := hlm.symm
          fin_cases x <;> fin_cases y <;>
            simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
          all_goals assumption
      exact (noD (lemma4_6 D hsub heD hfD hgD hbD hcD hiD hjD hkD hl hm)).elim
  · exact (noCurrentCE hce).elim

end Subcubic
