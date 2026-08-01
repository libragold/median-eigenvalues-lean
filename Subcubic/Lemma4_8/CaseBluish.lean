import Subcubic.Lemma4_8.CaseBlueBlue

/-! The immediate subcases when both exposed neighbors of `k` are bluish. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_8BluishHardConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8LMConfiguration C a b c d e f g h where
  hl : C.color l = .bluish
  hm : C.color m = .bluish
  hbl : ¬ G.Adj b l
  hbm : ¬ G.Adj b m
  hal : G.Adj a l

theorem lemma4_8_case_lm_bluish
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (Q : Lemma4_8LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .bluish) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8BluishHardConfiguration C a b c d e f g h) := by
  classical
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8)
      (huv : (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv' : C.color v = cv)
      (hne : cu ≠ cv) : u ≠ v := by
    intro huv
    subst v
    exact hne (hu.symm.trans hv')
  have hdk : ¬ G.Adj d Q.k := by
    apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
    · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
    · exact color_ne hc Q.hi (by decide)
    · exact color_ne he Q.hi (by decide)
    · exact Q.hck.ne.symm
    · exact color_ne Q.hk he (by decide)
    · intro hki
      have : G.Adj c Q.i := by simpa [hki] using Q.hck
      exact Q.hic this.symm
  have hkbAdj : ¬ G.Adj Q.k b :=
    C.reddish_not_adj_redSide Q.hk (Or.inl hb)
  have hbd : ¬ G.Adj b d := by
    intro hbd
    exact (by native_decide : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj (1 : Fin 8) 3) ((hedge 1 3).mpr hbd)
  have hbdV : b ≠ d := by
    simpa using hv (u := (1 : Fin 8)) (v := 3) (by decide)
  have hacV : a ≠ c := by
    simpa using hv (u := (0 : Fin 8)) (v := 2) (by decide)
  have hadV : a ≠ d := by
    simpa using hv (u := (0 : Fin 8)) (v := 3) (by decide)
  have ptrL_of_left (hbl : G.Adj b Q.l) : ContainsPositiveTailReducer C := by
    have hbm : ¬ G.Adj b Q.m := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc hbl
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
      · exact color_ne ha hl (by decide)
      · exact color_ne hc hl (by decide)
      · exact color_ne hm ha (by decide)
      · exact Q.hmc
      · exact Q.hlm.symm
    have hn : [Q.k, b, Q.m, Q.l, c, d].Nodup := by
      simp [color_ne Q.hk hb (by decide), color_ne Q.hk hm (by decide),
        color_ne Q.hk hl (by decide), color_ne Q.hk hc (by decide),
        color_ne Q.hk hd (by decide), color_ne hb hm (by decide),
        color_ne hb hl (by decide), hbc.ne,
        hbdV, Q.hlm.symm,
        Q.hmc, color_ne hm hd (by decide), Q.hlc,
        color_ne hl hd (by decide), hcd.ne]
    exact containsPositiveL C Q.hk hb hm hl hc hd Q.hkm Q.hkl Q.hck.symm
      hbl hbc hcd hkbAdj (by simpa [SimpleGraph.adj_comm] using hdk) hbm hbd hn
  have ptrL_of_right (hbm : G.Adj b Q.m) : ContainsPositiveTailReducer C := by
    have hbl : ¬ G.Adj b Q.l := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc hbm
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
      · exact color_ne ha hm (by decide)
      · exact color_ne hc hm (by decide)
      · exact color_ne hl ha (by decide)
      · exact Q.hlc
      · exact Q.hlm
    have hn : [Q.k, b, Q.l, Q.m, c, d].Nodup := by
      simp [color_ne Q.hk hb (by decide), color_ne Q.hk hl (by decide),
        color_ne Q.hk hm (by decide), color_ne Q.hk hc (by decide),
        color_ne Q.hk hd (by decide), color_ne hb hl (by decide),
        color_ne hb hm (by decide), hbc.ne,
        hbdV, Q.hlm,
        Q.hlc, color_ne hl hd (by decide), Q.hmc,
        color_ne hm hd (by decide), hcd.ne]
    exact containsPositiveL C Q.hk hb hl hm hc hd Q.hkl Q.hkm Q.hck.symm
      hbm hbc hcd hkbAdj (by simpa [SimpleGraph.adj_comm] using hdk) hbl hbd hn
  by_cases hbl : G.Adj b Q.l
  · exact Or.inl (HasReachableReduction.of_current_ptr C (ptrL_of_left hbl))
  by_cases hbm : G.Adj b Q.m
  · exact Or.inl (HasReachableReduction.of_current_ptr C (ptrL_of_right hbm))
  by_cases hal : G.Adj a Q.l
  · exact Or.inr ⟨{ Q with hl := hl, hm := hm, hbl := hbl, hbm := hbm, hal := hal }⟩
  by_cases ham : G.Adj a Q.m
  · let Qswap : Lemma4_8LMConfiguration C a b c d e f g h := { Q with
      l := Q.m
      m := Q.l
      hkl := Q.hkm
      hkm := Q.hkl
      hlc := Q.hmc
      hmc := Q.hlc
      hlm := Q.hlm.symm
      hlSide := Or.inr hm
      hmSide := Or.inr hl }
    exact Or.inr ⟨{ Qswap with
      hl := hm
      hm := hl
      hbl := hbm
      hbm := hbl
      hal := ham }⟩
  · have hkx : ¬ G.Adj Q.k Q.x := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hck.symm Q.hkl Q.hkm
      · exact Q.hlc.symm
      · exact Q.hmc.symm
      · exact Q.hlm
      · exact color_ne Q.hx hc (by decide)
      · intro hxl
        have : G.Adj a Q.l := by simpa [hxl] using Q.hax
        exact hal this
      · intro hxm
        have : G.Adj a Q.m := by simpa [hxm] using Q.hax
        exact ham this
    have hky : ¬ G.Adj Q.k Q.y := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hck.symm Q.hkl Q.hkm
      · exact Q.hlc.symm
      · exact Q.hmc.symm
      · exact Q.hlm
      · exact Q.hyc
      · intro hyl
        have : G.Adj b Q.l := by simpa [hyl] using Q.hby
        exact hbl this
      · intro hym
        have : G.Adj b Q.m := by simpa [hym] using Q.hby
        exact hbm this
    have hlj : Q.l ≠ Q.j := by
      intro hlj
      have : G.Adj Q.k Q.j := by simpa [hlj] using Q.hkl
      exact Q.hkj this
    have hmj : Q.m ≠ Q.j := by
      intro hmj
      have : G.Adj Q.k Q.j := by simpa [hmj] using Q.hkm
      exact Q.hkj this
    have hly : Q.l ≠ Q.y := by
      intro hly
      have : G.Adj b Q.l := by simpa [← hly] using Q.hby
      exact hbl this
    have hmy : Q.m ≠ Q.y := by
      intro hmy
      have : G.Adj b Q.m := by simpa [← hmy] using Q.hby
      exact hbm this
    have hyj : Q.y ≠ Q.j := by
      intro hyj
      have : G.Adj Q.j b := by simpa [hyj] using Q.hby.symm
      exact Q.hjb this
    have hlx : Q.l ≠ Q.x := by
      intro hlx
      have : G.Adj a Q.l := by simpa [← hlx] using Q.hax
      exact hal this
    have hmx : Q.m ≠ Q.x := by
      intro hmx
      have : G.Adj a Q.m := by simpa [← hmx] using Q.hax
      exact ham this
    have hn : [Q.k, a, b, Q.l, Q.m, Q.x, Q.j, c, d, Q.y].Nodup := by
      simp [color_ne Q.hk ha (by decide), color_ne Q.hk hb (by decide),
        color_ne Q.hk hl (by decide), color_ne Q.hk hm (by decide),
        color_ne Q.hk Q.hx (by decide), color_ne Q.hk Q.hj (by decide),
        color_ne Q.hk hc (by decide), color_ne Q.hk hd (by decide),
        color_ne Q.hk Q.hy (by decide), hab.ne,
        color_ne ha hl (by decide), color_ne ha hm (by decide),
        color_ne ha Q.hx (by decide), color_ne ha Q.hj (by decide),
        hacV, hadV,
        color_ne ha Q.hy (by decide), color_ne hb hl (by decide),
        color_ne hb hm (by decide), color_ne hb Q.hx (by decide),
        color_ne hb Q.hj (by decide), hbc.ne,
        hbdV,
        color_ne hb Q.hy (by decide), Q.hlm,
        hal, hlj, Q.hlc, color_ne hl hd (by decide), hly,
        ham, hmj, Q.hmc, color_ne hm hd (by decide), hmy,
        hlx, hmx, Q.hxj, color_ne Q.hx hc (by decide), color_ne Q.hx hd (by decide),
        Q.hxy, color_ne Q.hj hc (by decide), color_ne Q.hj hd (by decide),
        hyj.symm, hcd.ne, Q.hyc.symm, (color_ne Q.hy hd (by decide)).symm]
    exact Or.inl (HasReachableReduction.of_current_ptr C
      (containsPositiveT C Q.hk ha hb hl hm Q.hx Q.hj hc hd Q.hy
        Q.hkl Q.hkm Q.hck.symm hab Q.hax Q.hja.symm hbc Q.hby hcd
        hkx Q.hkj (by simpa [SimpleGraph.adj_comm] using hdk) hky hn))

end Subcubic
