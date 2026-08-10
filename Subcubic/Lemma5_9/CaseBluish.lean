import Subcubic.Lemma5_9.CaseBlueBlue
import Subcubic.Lemma5_5

/-! Lemma 5.9, Case (3.4.4.1): both exposed neighbors of `k` are bluish. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_lm_bluish
    (C : GoodColoring G) {C₀ : GoodColoring G} {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_9LMConfiguration C₀ a b c d e f g h)
    (hi : C.color Q.i = .reddish) (hj : C.color Q.j = .bluish)
    (hx : C.color Q.x = .bluish) (hy : C.color Q.y = .bluish)
    (hk : C.color Q.k = .reddish)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .bluish) :
    HasReachableNegativeReduction C := by
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
    · exact color_ne hc hi (by decide)
    · exact color_ne he hi (by decide)
    · exact Q.hck.ne.symm
    · exact color_ne hk he (by decide)
    · intro hki
      have : G.Adj c Q.i := by simpa [hki] using Q.hck
      exact Q.hic this.symm
  have hkbAdj : ¬ G.Adj Q.k b :=
    C.reddish_not_adj_redSide hk (Or.inl hb)
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
  have ntrI_of_left (hblAdj : G.Adj b Q.l) : ContainsNegativeTailReducer C := by
    have hbm : ¬ G.Adj b Q.m := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc hblAdj
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
      · exact color_ne ha hl (by decide)
      · exact color_ne hc hl (by decide)
      · exact color_ne hm ha (by decide)
      · exact Q.hmc
      · exact Q.hlm.symm
    have hn : [b, Q.k, d, c, Q.l, Q.m].Nodup := by
      simp [color_ne hb hk (by decide), color_ne hb hd (by decide),
        color_ne hb hc (by decide), color_ne hb hl (by decide),
        color_ne hb hm (by decide), color_ne hk hd (by decide),
        color_ne hk hc (by decide), color_ne hk hl (by decide),
        color_ne hk hm (by decide), hcd.ne.symm,
        color_ne hd hl (by decide), color_ne hd hm (by decide),
        color_ne hc hl (by decide), color_ne hc hm (by decide), Q.hlm]
    exact containsNegativeI C hb hk hd hc hl hm hbc hblAdj
      Q.hck.symm Q.hkl Q.hkm hcd.symm
      (by simpa [SimpleGraph.adj_comm] using hkbAdj) hbd hbm
      (by simpa [SimpleGraph.adj_comm] using hdk) hn
  have ntrI_of_right (hbmAdj : G.Adj b Q.m) : ContainsNegativeTailReducer C := by
    have hbl : ¬ G.Adj b Q.l := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc hbmAdj
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
      · exact color_ne ha hm (by decide)
      · exact color_ne hc hm (by decide)
      · exact color_ne hl ha (by decide)
      · exact Q.hlc
      · exact Q.hlm
    have hn : [b, Q.k, d, c, Q.m, Q.l].Nodup := by
      simp [color_ne hb hk (by decide), color_ne hb hd (by decide),
        color_ne hb hc (by decide), color_ne hb hm (by decide),
        color_ne hb hl (by decide), color_ne hk hd (by decide),
        color_ne hk hc (by decide), color_ne hk hm (by decide),
        color_ne hk hl (by decide), hcd.ne.symm,
        color_ne hd hm (by decide), color_ne hd hl (by decide),
        color_ne hc hm (by decide), color_ne hc hl (by decide), Q.hlm.symm]
    exact containsNegativeI C hb hk hd hc hm hl hbc hbmAdj
      Q.hck.symm Q.hkm Q.hkl hcd.symm
      (by simpa [SimpleGraph.adj_comm] using hkbAdj) hbd hbl
      (by simpa [SimpleGraph.adj_comm] using hdk) hn
  by_cases hbl : G.Adj b Q.l
  · exact HasReachableNegativeReduction.of_current_ntr C (ntrI_of_left hbl)
  by_cases hbm : G.Adj b Q.m
  · exact HasReachableNegativeReduction.of_current_ntr C (ntrI_of_right hbm)
  have finish (l m : V) (hl : C.color l = .bluish) (hm : C.color m = .bluish)
      (hkl : G.Adj Q.k l) (hkm : G.Adj Q.k m)
      (hbl : ¬ G.Adj b l) (hbm : ¬ G.Adj b m) (hal : G.Adj a l)
      (hlm : l ≠ m) :
      HasReachableNegativeReduction C := by
    have hbk : ¬ G.Adj b Q.k := by simpa [SimpleGraph.adj_comm] using hkbAdj
    have hak : ¬ G.Adj a Q.k := by
      simpa [SimpleGraph.adj_comm] using
        C.reddish_not_adj_redSide hk (Or.inl ha)
    have hac : ¬ G.Adj a c := by
      intro q
      exact (by native_decide : ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj (0 : Fin 8) 2) ((hedge 0 2).mpr q)
    have hcl : ¬ G.Adj c l :=
      fun q => C.bluish_not_adj_blueSide hl (Or.inl hc) q.symm
    have hn : [b, a, Q.k, c, l].Nodup := by
      simp [hab.ne.symm, color_ne hb hk (by decide), hbc.ne,
        color_ne hb hl (by decide), color_ne ha hk (by decide),
        hacV, color_ne ha hl (by decide), color_ne hk hc (by decide),
        color_ne hk hl (by decide), color_ne hc hl (by decide)]
    have hpent : FormsInducedPentagon G b a Q.k c l := by
      refine ⟨?_, ?_⟩
      · intro u v huv
        apply hn.injective_get
        fin_cases u <;> fin_cases v <;> exact huv
      · intro u v
        fin_cases u <;> fin_cases v <;>
          simp [graphOfEdges, G.adj_comm, hab, hbc, hal, Q.hck,
            hkl.symm, hbk, hbl, hak, hac, hcl]
    have hbNoBlue : ∀ v, G.Adj b v → v ≠ c → v ≠ l → C.color v ≠ .blue := by
      intro v hbv hvc hvl hvblue
      rcases C.neighbor_eq_of_three_neighbors (Or.inl hb)
          hab.symm hbc Q.hby
          (hv (u := (0 : Fin 8)) (v := 2) (by decide)) Q.hya.symm Q.hyc.symm hbv with
        rfl | rfl | rfl
      · simp [ha] at hvblue
      · exact (hvc rfl).elim
      · simp [hy] at hvblue
    have haNoBlue : ∀ v, G.Adj a v → v ≠ c → v ≠ l → C.color v ≠ .blue := by
      intro v hav _ _
      exact hNoBlueAtA v hav
    have hkNoBlue : ∀ v, G.Adj Q.k v → v ≠ c → v ≠ l → C.color v ≠ .blue := by
      intro v hkv hvc hvl hvblue
      by_cases hvm : v = m
      · subst v
        simp [hm] at hvblue
      exact (not_adj_fourth_neighbor_of_degree_three Q.hkdeg
        Q.hck.symm hkl hkm
        (color_ne hc hl (by decide)) (color_ne hc hm (by decide)) hlm
        hvc hvl hvm) hkv
    exact lemma5_5 C hpent hb ha hk hc (Or.inr hl)
      hbNoBlue haNoBlue hkNoBlue
  by_cases hal : G.Adj a Q.l
  · exact finish Q.l Q.m hl hm Q.hkl Q.hkm hbl hbm hal Q.hlm
  by_cases ham : G.Adj a Q.m
  · exact finish Q.m Q.l hm hl Q.hkm Q.hkl hbm hbl ham Q.hlm.symm
  · have hkx : ¬ G.Adj Q.k Q.x := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hck.symm Q.hkl Q.hkm
      · exact Q.hlc.symm
      · exact Q.hmc.symm
      · exact Q.hlm
      · exact color_ne hx hc (by decide)
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
      simp [color_ne hk ha (by decide), color_ne hk hb (by decide),
        color_ne hk hl (by decide), color_ne hk hm (by decide),
        color_ne hk hx (by decide), color_ne hk hj (by decide),
        color_ne hk hc (by decide), color_ne hk hd (by decide),
        color_ne hk hy (by decide), hab.ne,
        color_ne ha hl (by decide), color_ne ha hm (by decide),
        color_ne ha hx (by decide), color_ne ha hj (by decide),
        hacV, hadV,
        color_ne ha hy (by decide), color_ne hb hl (by decide),
        color_ne hb hm (by decide), color_ne hb hx (by decide),
        color_ne hb hj (by decide), hbc.ne,
        hbdV,
        color_ne hb hy (by decide), Q.hlm,
        hlj, Q.hlc, color_ne hl hd (by decide), hly,
        hmj, Q.hmc, color_ne hm hd (by decide), hmy,
        hlx, hmx, Q.hxj, color_ne hx hc (by decide), color_ne hx hd (by decide),
        Q.hxy, color_ne hj hc (by decide), color_ne hj hd (by decide),
        hyj.symm, hcd.ne, Q.hyc.symm, (color_ne hy hd (by decide)).symm]
    exact HasReachableNegativeReduction.of_current_ntr C
      (containsNegativeAg C hk ha hb hl hm hx hj hc hd hy
        Q.hkl Q.hkm Q.hck.symm hab Q.hax Q.hja.symm hbc Q.hby hcd
        hkx Q.hkj (by simpa [SimpleGraph.adj_comm] using hdk) hky hn)

end Subcubic
