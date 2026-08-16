import Subcubic.Lemma4_10.CaseJ
import Subcubic.Lemma4_6

/-!
# Lemma 4.10, Case (3.2.2.3.2.3)

This file starts at Case (3.2.2.3.2.3): the bluish vertex `j` has, besides
its red neighbor `a`, another red neighbor `l`.  The red mate of `l` is
called `m`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_10_other_red_complete
    (C : MatchingCutColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma4_10OtherRedConfiguration C a b c d e f) :
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

  -- Since `l` is red, it has a unique red mate `m`.
  have hlCorrect := C.color_correct Q.l
  rw [Q.hl] at hlCorrect
  obtain ⟨_, m, hmSide, hlm⟩ := hlCorrect
  have hmSide' := (C.mem_redSide_iff m).1 hmSide
  have hm : C.color m = .red := by
    rcases hmSide' with hm | hm
    · exact hm
    · exact (C.reddish_not_adj_redSide hm (Or.inl Q.hl) hlm.symm).elim

  have habV : a ≠ b := hab.ne
  have hli : Q.l ≠ Q.i := color_ne Q.hl Q.hi (by decide)
  have hla : Q.l ≠ a := Q.hla
  have hia : Q.i ≠ a := color_ne Q.hi ha (by decide)
  have hjb : ¬ G.Adj Q.j b := by
    simpa [SimpleGraph.adj_comm] using
      C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
        (hv (x := (0 : Fin 6)) (y := 2) (by decide))
        (color_ne ha Q.hg (by decide)) (color_ne hc Q.hg (by decide))
        (color_ne Q.hj ha (by decide)) (color_ne Q.hj hc (by decide))
        (by intro h; apply Q.hig; simpa [h] using Q.hij)
  have hjh : Q.j ≠ Q.h := by
    intro h
    apply Q.hih
    simpa [h] using Q.hij
  have hje : ¬ G.Adj Q.j e := by
    simpa [SimpleGraph.adj_comm] using
      C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        (hv (x := (5 : Fin 6)) (y := 3) (by decide))
        (color_ne hf Q.hh (by decide)) (color_ne hd Q.hh (by decide))
        (color_ne Q.hj hf (by decide)) (color_ne Q.hj hd (by decide)) hjh
  have hlb : Q.l ≠ b := by
    intro h
    apply hjb
    simpa [h] using Q.hjl
  have hle : Q.l ≠ e := by
    intro h
    apply hje
    simpa [h] using Q.hjl
  have hlf : Q.l ≠ f := by
    intro h
    apply Q.hjf
    simpa [h] using Q.hjl
  have hma : m ≠ a := by
    intro h
    subst m
    exact (C.redSide_not_adj_second_neighbor
      (by simp [ha]) (by simp [hb]) (by simp [Q.hl]) hab hlb.symm) hlm.symm
  have hmb : m ≠ b := by
    intro h
    subst m
    exact (C.redSide_not_adj_second_neighbor
      (by simp [hb]) (by simp [ha]) (by simp [Q.hl]) hab.symm hla.symm) hlm.symm
  have hme : m ≠ e := by
    intro h
    subst m
    exact (C.redSide_not_adj_second_neighbor
      (by simp [he]) (by simp [hf]) (by simp [Q.hl]) hef hlf.symm) hlm.symm
  have hmf : m ≠ f := by
    intro h
    subst m
    exact (C.redSide_not_adj_second_neighbor
      (by simp [hf]) (by simp [he]) (by simp [Q.hl]) hef.symm hle.symm) hlm.symm
  have hmc : ¬ G.Adj m c := by
    simpa [SimpleGraph.adj_comm] using
      not_adj_fourth_neighbor_of_subcubic C.subcubic hbc.symm hcd Q.hci
        (hv (x := (1 : Fin 6)) (y := 3) (by decide))
        (color_ne hb Q.hi (by decide)) (color_ne hd Q.hi (by decide))
        hmb (color_ne hm hd (by decide)) (color_ne hm Q.hi (by decide))
  have hmd : ¬ G.Adj m d := by
    intro hmdAdj
    have hem : ¬ G.Adj e m :=
      C.redSide_not_adj_second_neighbor
        (by simp [he]) (by simp [hf]) (by simp [hm]) hef hmf.symm
    have hceSwap := containsCutEnhancerA_of C.swapSides
      (by simp [hd]) (by simp [he]) (by simp [hm])
      hde hmdAdj.symm hme.symm hem
    exact noCurrentCE
      ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)

  by_cases hNoBlueL : ∀ z, G.Adj Q.l z → C.color z ≠ .blue
  · by_cases hNoBlueM : ∀ z, G.Adj m z → C.color z ≠ .blue
    · -- Case (3.2.2.3.2.3.1): the red edge `lm` is isolated.
      have l_other : ∀ z, G.Adj Q.l z → z ≠ m → C.color z = .bluish := by
        intro z hlz hzm
        have hzSide := C.other_neighbor_of_red_is_blueSide
          Q.hl hm hlm hlz hzm
        rcases hzSide with hz | hz
        · exact (hNoBlueL z hlz hz).elim
        · exact hz
      have m_other : ∀ z, G.Adj m z → z ≠ Q.l → C.color z = .bluish := by
        intro z hmz hzl
        have hzSide := C.other_neighbor_of_red_is_blueSide
          hm Q.hl hlm.symm hmz hzl
        rcases hzSide with hz | hz
        · exact (hNoBlueM z hmz hz).elim
        · exact hz
      exact hresult (HasReachableReduction.of_current_ptr C
        (lemma4_4 C Q.hl hm hlm (degreeC (Or.inl Q.hl))
          (degreeC (Or.inl hm)) l_other m_other))
    · -- Case (3.2.2.3.2.3.3), completed below.
      push Not at hNoBlueM
      obtain ⟨n, hmn, hn⟩ := hNoBlueM
      have hnc : n ≠ c := by
        intro h
        subst n
        exact hmc hmn
      have hnd : n ≠ d := by
        intro h
        subst n
        exact hmd hmn
      have hem : ¬ G.Adj e m :=
        C.redSide_not_adj_second_neighbor
          (by simp [he]) (by simp [hf]) (by simp [hm]) hef hmf.symm
      have hbm : ¬ G.Adj b m :=
        C.redSide_not_adj_second_neighbor
          (by simp [hb]) (by simp [ha]) (by simp [hm]) hab.symm hma.symm
      have hen : ¬ G.Adj e n := by
        apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        · exact hv (x := (5 : Fin 6)) (y := 3) (by decide)
        · exact color_ne hf Q.hh (by decide)
        · exact color_ne hd Q.hh (by decide)
        · exact color_ne hn hf (by decide)
        · exact hnd
        · exact color_ne hn Q.hh (by decide)
      have hbn : ¬ G.Adj b n := by
        apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
        · exact hv (x := (0 : Fin 6)) (y := 2) (by decide)
        · exact color_ne ha Q.hg (by decide)
        · exact color_ne hc Q.hg (by decide)
        · exact color_ne hn ha (by decide)
        · exact hnc
        · exact color_ne hn Q.hg (by decide)
      have hdn : ¬ G.Adj d n :=
        C.blueSide_not_adj_second_neighbor
          (by simp [hd]) (by simp [hc]) (by simp [hn]) hcd.symm hnc.symm
      have hcn : ¬ G.Adj c n :=
        C.blueSide_not_adj_second_neighbor
          (by simp [hc]) (by simp [hd]) (by simp [hn]) hcd hnd.symm
      have hgc : ¬ G.Adj Q.g c :=
        C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
      have hgn : ¬ G.Adj Q.g n :=
        C.bluish_not_adj_blueSide Q.hg (Or.inl hn)
      have hhd : ¬ G.Adj Q.h d :=
        C.bluish_not_adj_blueSide Q.hh (Or.inl hd)
      have hhn : ¬ G.Adj Q.h n :=
        C.bluish_not_adj_blueSide Q.hh (Or.inl hn)
      have hmg : ¬ G.Adj m Q.g := by
        intro hmgAdj
        have hceSwap := containsCutEnhancerB_of C.swapSides
          (by simp [Q.hg]) (by simp [hb]) (by simp [hc])
          (by simp [hm]) (by simp [hn])
          Q.hbg.symm hmgAdj.symm hbc hmn hgc hgn hbm hbn
          (fun h => hmc h.symm) hcn
        exact noCurrentCE
          ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
      have hmh : ¬ G.Adj m Q.h := by
        intro hmhAdj
        have hceSwap := containsCutEnhancerB_of C.swapSides
          (by simp [Q.hh]) (by simp [he]) (by simp [hd])
          (by simp [hm]) (by simp [hn])
          Q.heh.symm hmhAdj.symm hde.symm hmn hhd hhn hem hen
          (fun h => hmd h.symm) hdn
        exact noCurrentCE
          ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)

      have hnCorrect := C.color_correct n
      rw [hn] at hnCorrect
      obtain ⟨_, o, hoSide, hno⟩ := hnCorrect
      have hoSide' := (C.not_mem_redSide_iff o).1 hoSide
      have ho : C.color o = .blue := by
        rcases hoSide' with ho | ho
        · exact ho
        · exact (C.bluish_not_adj_blueSide ho (Or.inl hn) hno.symm).elim
      rcases exists_flipAt_or_cutEnhancer C hm hn Q.hl ho
          (degreeC (Or.inl hm)) (degreeC (Or.inr hn))
          hlm.symm hmn hno with hflip | hce
      · obtain ⟨M, hflip⟩ := hflip
        let D := M.toColoring
        have noD (hout : HasReachableReduction D) : False :=
          hresult (HasReachableReduction.after_flip C hflip hout)
        have color_neD {x y : V} {cx cy : Color}
            (hx : D.color x = cx) (hy : D.color y = cy)
            (hxy : cx ≠ cy) : x ≠ y := by
          intro h
          subst y
          simp_all
        have haD : D.color a = .red :=
          red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
            hma.symm (color_ne ha hn (by decide)) hmb.symm (color_ne hb hn (by decide))
        have hbD : D.color b = .red :=
          red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
            hmb.symm (color_ne hb hn (by decide)) hma.symm (color_ne ha hn (by decide))
        have hcD : D.color c = .blue :=
          blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
            (color_ne hc hm (by decide)) hnc.symm
            (color_ne hd hm (by decide)) hnd.symm
        have hdD : D.color d = .blue :=
          blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
            (color_ne hd hm (by decide)) hnd.symm
            (color_ne hc hm (by decide)) hnc.symm
        have heD : D.color e = .red :=
          red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
            hme.symm (color_ne he hn (by decide)) hmf.symm (color_ne hf hn (by decide))
        have hfD : D.color f = .red :=
          red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
            hmf.symm (color_ne hf hn (by decide)) hme.symm (color_ne he hn (by decide))
        have hgD : D.color Q.g = .bluish := by
          apply bluish_of_untouched_bluish C hflip Q.hg
            (by simpa [SimpleGraph.adj_comm] using hmg)
          · exact color_ne Q.hg hm (by decide)
          · exact color_ne Q.hg hn (by decide)
        have hhD : D.color Q.h = .bluish := by
          apply bluish_of_untouched_bluish C hflip Q.hh
            (by simpa [SimpleGraph.adj_comm] using hmh)
          · exact color_ne Q.hh hm (by decide)
          · exact color_ne Q.hh hn (by decide)
        have hin : ¬ G.Adj Q.i n := by
          apply not_adj_fourth_neighbor_of_subcubic C.subcubic
            Q.hci.symm Q.hij Q.hik Q.hjc.symm Q.hkc.symm Q.hjk
          · exact hnc
          · exact color_ne hn Q.hj (by decide)
          · exact color_ne hn Q.hk (by decide)
        have hiD : D.color Q.i = .reddish := by
          apply reddish_of_untouched_reddish C hflip Q.hi hin
          · exact color_ne Q.hi hm (by decide)
          · exact color_ne Q.hi hn (by decide)
        have hjm : ¬ G.Adj Q.j m := by
          apply not_adj_fourth_neighbor_of_subcubic C.subcubic
            Q.hij.symm Q.hja Q.hjl hia hli.symm hla.symm
          · exact color_ne hm Q.hi (by decide)
          · exact hma
          · exact hlm.ne.symm
        have hjD : D.color Q.j = .bluish := by
          apply bluish_of_untouched_bluish C hflip Q.hj hjm
          · exact color_ne Q.hj hm (by decide)
          · exact color_ne Q.hj hn (by decide)
        have hln : ¬ G.Adj Q.l n := fun h => hNoBlueL n h hn
        have hlD : D.color Q.l = .reddish := by
          apply reddish_of_red_loses_flipped_mate C hflip Q.hl hlm hln
          · exact hlm.ne
          · exact color_ne Q.hl hn (by decide)
        let I' : Lemma4_10IConfiguration D a b c d e f := {
          toLemma4_10Case3_2Configuration := {
            toLemma4_10Case3Configuration := {
              g := Q.g
              h := Q.h
              hg := hgD
              hh := hhD
              hbg := Q.hbg
              hgf := Q.hgf
              heh := Q.heh
              hha := Q.hha
              hge := Q.hge
              hhb := Q.hhb }
            hga := Q.hga
            hhf := Q.hhf }
          i := Q.i
          hi := hiD
          hci := Q.hci
          hib := Q.hib
          hid := Q.hid
          hideg := Q.hideg
          hig := Q.hig }
        by_cases hmk : G.Adj m Q.k
        · have hkD : D.color Q.k = .blue := by
            apply blue_of_bluish_gains_flipped_red C hflip Q.hk hmk.symm
            · exact color_ne Q.hk hm (by decide)
            · exact color_ne Q.hk hn (by decide)
          exact noD (lemma4_10_case_3_2_1 D hp haD hbD hcD hdD heD hfD I'
            hkD Q.hik Q.hkc (color_ne Q.hk hd (by decide)))
        · have hkD : D.color Q.k = .bluish := by
            apply bluish_of_untouched_bluish C hflip Q.hk
              (by simpa [SimpleGraph.adj_comm] using hmk)
            · exact color_ne Q.hk hm (by decide)
            · exact color_ne Q.hk hn (by decide)
          let J' : Lemma4_10JConfiguration D a b c d e f := {
            toLemma4_10JKConfiguration := {
              toLemma4_10IConfiguration := I'
              j := Q.j
              k := Q.k
              hj := hjD
              hk := hkD
              hij := Q.hij
              hik := Q.hik
              hjc := Q.hjc
              hkc := Q.hkc
              hjk := Q.hjk
              hid' := Q.hid'
              hih := Q.hih }
            hja := Q.hja }
          rcases lemma4_10_j_cases D hp haD hbD hcD hdD heD hfD J' with
            hout | hR
          · exact noD hout
          · obtain ⟨r, hr, hjr, hra, _⟩ := hR
            have hnot : ¬ G.Adj Q.j r := by
              apply not_adj_fourth_neighbor_of_subcubic C.subcubic
                Q.hij.symm Q.hja Q.hjl hia hli.symm hla.symm
              · exact color_neD hr hiD (by decide)
              · exact hra
              · exact color_neD hr hlD (by decide)
            exact hnot hjr
      · exact noCurrentCE hce
  · -- Case (3.2.2.3.2.3.2), completed below.
    push Not at hNoBlueL
    obtain ⟨n, hln, hn⟩ := hNoBlueL
    have hnCorrect := C.color_correct n
    rw [hn] at hnCorrect
    obtain ⟨_, o, hoSide, hno⟩ := hnCorrect
    have hoSide' := (C.not_mem_redSide_iff o).1 hoSide
    have ho : C.color o = .blue := by
      rcases hoSide' with ho | ho
      · exact ho
      · exact (C.bluish_not_adj_blueSide ho (Or.inl hn) hno.symm).elim
    rcases exists_flipAt_or_cutEnhancer C Q.hl hn hm ho
        (degreeC (Or.inl Q.hl)) (degreeC (Or.inr hn))
        hlm hln hno with hflip | hce
    · obtain ⟨M, hflip⟩ := hflip
      let D := M.toColoring
      have noD (hout : HasReachableReduction D) : False :=
        hresult (HasReachableReduction.after_flip C hflip hout)
      have color_neD {x y : V} {cx cy : Color}
          (hx : D.color x = cx) (hy : D.color y = cy)
          (hxy : cx ≠ cy) : x ≠ y := by
        intro h
        subst y
        simp_all
      have hnM : n ∈ M.side := by
        rw [hflip.2]
        have hnOld : n ∉ C.redSide := by simp [hn]
        simp [Set.mem_symmDiff, hnOld, hflip.1.1.ne.symm]
      have hnc : n ≠ c := by
        intro hncEq
        have hbn : b ≠ n := by
          simpa [hncEq] using hv (x := (1 : Fin 6)) (y := 2) (by decide)
        have han : a ≠ n := by
          simpa [hncEq] using hv (x := (0 : Fin 6)) (y := 2) (by decide)
        have hbM : b ∈ M.side := by
          exact (mem_side_iff_of_flipAt C hflip hlb.symm hbn).2 (by simp [hb])
        have haM : a ∈ M.side := by
          exact (mem_side_iff_of_flipAt C hflip hla.symm han).2 (by simp [ha])
        have hbRed : D.color b = .red := by
          change colorOfCut G M.side b = .red
          exact (colorOfCut_eq_red_iff G M.side b).2 ⟨hbM, a, haM, hab.symm⟩
        have haRed : D.color a = .red := by
          change colorOfCut G M.side a = .red
          exact (colorOfCut_eq_red_iff G M.side a).2 ⟨haM, b, hbM, hab⟩
        have hnRed : D.color n = .red := by
          change colorOfCut G M.side n = .red
          exact (colorOfCut_eq_red_iff G M.side n).2
            ⟨hnM, b, hbM, by simpa [hncEq] using hbc.symm⟩
        have hnot := D.redSide_not_adj_second_neighbor
          (by simp [hbRed]) (by simp [haRed]) (by simp [hnRed]) hab.symm han
        exact hnot (by simpa [hncEq] using hbc)
      have hnd : n ≠ d := by
        intro hndEq
        have hen : e ≠ n := by
          simpa [hndEq] using hv (x := (4 : Fin 6)) (y := 3) (by decide)
        have hfn : f ≠ n := by
          simpa [hndEq] using hv (x := (5 : Fin 6)) (y := 3) (by decide)
        have heM : e ∈ M.side := by
          exact (mem_side_iff_of_flipAt C hflip hle.symm hen).2 (by simp [he])
        have hfM : f ∈ M.side := by
          exact (mem_side_iff_of_flipAt C hflip hlf.symm hfn).2 (by simp [hf])
        have heRed : D.color e = .red := by
          change colorOfCut G M.side e = .red
          exact (colorOfCut_eq_red_iff G M.side e).2 ⟨heM, f, hfM, hef⟩
        have hfRed : D.color f = .red := by
          change colorOfCut G M.side f = .red
          exact (colorOfCut_eq_red_iff G M.side f).2 ⟨hfM, e, heM, hef.symm⟩
        have hnRed : D.color n = .red := by
          change colorOfCut G M.side n = .red
          exact (colorOfCut_eq_red_iff G M.side n).2
            ⟨hnM, e, heM, by simpa [hndEq] using hde⟩
        have hnot := D.redSide_not_adj_second_neighbor
          (by simp [heRed]) (by simp [hfRed]) (by simp [hnRed]) hef hfn
        exact hnot (by simpa [hndEq] using hde.symm)
      have haD : D.color a = .red :=
        red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
          hla.symm (color_ne ha hn (by decide)) hlb.symm (color_ne hb hn (by decide))
      have hbD : D.color b = .red :=
        red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
          hlb.symm (color_ne hb hn (by decide)) hla.symm (color_ne ha hn (by decide))
      have hcD : D.color c = .blue :=
        blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
          (color_ne hc Q.hl (by decide)) hnc.symm
          (color_ne hd Q.hl (by decide)) hnd.symm
      have hdD : D.color d = .blue :=
        blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
          (color_ne hd Q.hl (by decide)) hnd.symm
          (color_ne hc Q.hl (by decide)) hnc.symm
      have heD : D.color e = .red :=
        red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
          hle.symm (color_ne he hn (by decide)) hlf.symm (color_ne hf hn (by decide))
      have hfD : D.color f = .red :=
        red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
          hlf.symm (color_ne hf hn (by decide)) hle.symm (color_ne he hn (by decide))
      have hjD : D.color Q.j = .blue := by
        apply blue_of_bluish_gains_flipped_red C hflip Q.hj Q.hjl
        · exact Q.hjl.ne
        · exact color_ne Q.hj hn (by decide)
      have hlD : D.color Q.l = .blue :=
        blue_of_flipped_red_endpoint C hflip hm hlm
          (degreeC (Or.inl Q.hl)) (color_ne hm hn (by decide))
      have hnD : D.color n = .red :=
        red_of_flipped_blue_endpoint C hflip ho hno
          (degreeC (Or.inr hn)) (color_ne ho Q.hl (by decide))
      have hnCorrectD := D.color_correct n
      rw [hnD] at hnCorrectD
      obtain ⟨_, p, hpSide, hnp⟩ := hnCorrectD
      have hpSide' := (D.mem_redSide_iff p).1 hpSide
      have hpD : D.color p = .red := by
        rcases hpSide' with hpD | hpD
        · exact hpD
        · exact (D.reddish_not_adj_redSide hpD (Or.inl hnD) hnp.symm).elim

      have path6Nodup : [f, e, d, c, b, a].Nodup := by
        have hfeV : f ≠ e := by simpa using hv (x := (5 : Fin 6)) (y := 4) (by decide)
        have hfdV : f ≠ d := by simpa using hv (x := (5 : Fin 6)) (y := 3) (by decide)
        have hfcV : f ≠ c := by simpa using hv (x := (5 : Fin 6)) (y := 2) (by decide)
        have hfbV : f ≠ b := by simpa using hv (x := (5 : Fin 6)) (y := 1) (by decide)
        have hfaV : f ≠ a := by simpa using hv (x := (5 : Fin 6)) (y := 0) (by decide)
        have hedV : e ≠ d := by simpa using hv (x := (4 : Fin 6)) (y := 3) (by decide)
        have hecV : e ≠ c := by simpa using hv (x := (4 : Fin 6)) (y := 2) (by decide)
        have hebV : e ≠ b := by simpa using hv (x := (4 : Fin 6)) (y := 1) (by decide)
        have heaV : e ≠ a := by simpa using hv (x := (4 : Fin 6)) (y := 0) (by decide)
        have hdcV : d ≠ c := by simpa using hv (x := (3 : Fin 6)) (y := 2) (by decide)
        have hdbV : d ≠ b := by simpa using hv (x := (3 : Fin 6)) (y := 1) (by decide)
        have hdaV : d ≠ a := by simpa using hv (x := (3 : Fin 6)) (y := 0) (by decide)
        have hcbV : c ≠ b := by simpa using hv (x := (2 : Fin 6)) (y := 1) (by decide)
        have hcaV : c ≠ a := by simpa using hv (x := (2 : Fin 6)) (y := 0) (by decide)
        have hbaV : b ≠ a := by simpa using hv (x := (1 : Fin 6)) (y := 0) (by decide)
        simp [hfeV, hfdV, hfcV, hfbV, hfaV, hedV, hecV, hebV, heaV,
          hdcV, hdbV, hdaV, hcbV, hcaV, hbaV]
      have hjNotPath : Q.j ∉ [f, e, d, c, b, a] := by
        simp [color_ne Q.hj hf (by decide), color_ne Q.hj he (by decide),
          color_ne Q.hj hd (by decide), color_ne Q.hj hc (by decide),
          color_ne Q.hj hb (by decide), color_ne Q.hj ha (by decide)]
      have hlNotPath : Q.l ∉ [f, e, d, c, b, a] := by
        simp [hlf, hle, color_ne Q.hl hd (by decide),
          color_ne Q.hl hc (by decide), hlb, hla]
      have hnNotPath : n ∉ [f, e, d, c, b, a] := by
        simp [color_ne hn hf (by decide), color_ne hn he (by decide),
          hnd, hnc, color_ne hn hb (by decide), color_ne hn ha (by decide)]
      have tailNodup : [Q.j, Q.l, n].Nodup := by
        simp [Q.hjl.ne, color_ne Q.hj hn (by decide),
          color_ne Q.hl hn (by decide)]
      have coreNodup : [f, e, d, c, b, a, Q.j, Q.l, n].Nodup := by
        rw [show [f, e, d, c, b, a, Q.j, Q.l, n] =
          [f, e, d, c, b, a] ++ [Q.j, Q.l, n] by rfl,
          List.nodup_append']
        refine ⟨path6Nodup, tailNodup, ?_⟩
        rw [List.disjoint_left]
        intro x hxPath hxTail
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hxTail
        rcases hxTail with rfl | rfl | rfl
        · exact hjNotPath hxPath
        · exact hlNotPath hxPath
        · exact hnNotPath hxPath
      have hpf : p ≠ f := by
        intro h
        subst p
        exact (D.redSide_not_adj_second_neighbor
          (by simp [hfD]) (by simp [heD]) (by simp [hnD]) hef.symm
          (color_ne he hn (by decide))) hnp.symm
      have hpe : p ≠ e := by
        intro h
        subst p
        exact (D.redSide_not_adj_second_neighbor
          (by simp [heD]) (by simp [hfD]) (by simp [hnD]) hef
          (color_ne hf hn (by decide))) hnp.symm
      have hpb : p ≠ b := by
        intro h
        subst p
        exact (D.redSide_not_adj_second_neighbor
          (by simp [hbD]) (by simp [haD]) (by simp [hnD]) hab.symm
          (color_ne ha hn (by decide))) hnp.symm
      have hpa : p ≠ a := by
        intro h
        subst p
        exact (D.redSide_not_adj_second_neighbor
          (by simp [haD]) (by simp [hbD]) (by simp [hnD]) hab
          (color_ne hb hn (by decide))) hnp.symm
      have pNotCore : p ∉ [f, e, d, c, b, a, Q.j, Q.l, n] := by
        simp [hpf, hpe, color_neD hpD hdD (by decide),
          color_neD hpD hcD (by decide), hpb, hpa,
          color_neD hpD hjD (by decide), color_neD hpD hlD (by decide),
          hnp.ne.symm]
      have pathNodup : [f, e, d, c, b, a, Q.j, Q.l, n, p].Nodup := by
        rw [show [f, e, d, c, b, a, Q.j, Q.l, n, p] =
          [f, e, d, c, b, a, Q.j, Q.l, n] ++ [p] by rfl,
          List.nodup_append']
        refine ⟨coreNodup, by simp, ?_⟩
        rw [List.disjoint_left]
        intro x hxCore hxP
        simp only [List.mem_singleton] at hxP
        subst x
        exact pNotCore hxCore
      have hsub : FormsPath10Subgraph G f e d c b a Q.j Q.l n p := by
        refine ⟨?_, ?_⟩
        · have hvec : (![f, e, d, c, b, a, Q.j, Q.l, n, p] : Fin 10 → V) =
              [f, e, d, c, b, a, Q.j, Q.l, n, p].get := by
            funext x
            fin_cases x <;> rfl
          rw [hvec]
          exact pathNodup.injective_get
        · intro x y hxy
          have hfe := hef.symm
          have hed := hde.symm
          have hdc := hcd.symm
          have hcb := hbc.symm
          have hba := hab.symm
          have haj := Q.hja.symm
          have hjl := Q.hjl
          have hlj := Q.hjl.symm
          have hnl := hln.symm
          have hpn := hnp.symm
          fin_cases x <;> fin_cases y <;>
            simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
          all_goals assumption
      exact noD (lemma4_6 D hsub hfD heD hdD hcD hbD haD hjD hlD hnD hpD)
    · exact noCurrentCE hce

end Subcubic
