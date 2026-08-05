import Subcubic.Lemma5_13.InlinePath3Cases
import Subcubic.Lemma5_5

/-! Case (3) of Lemma 5.13. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case3
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_13ThirdNeighborConfiguration C a b c d)
    (hef : ¬ G.Adj Q.e Q.f) (hea : ¬ G.Adj Q.e a)
    (hfd : ¬ G.Adj Q.f d)
    (hOutsideF : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ d →
      C.color z = .bluish) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath4 G a b c d := ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have nonedge (x y : Fin 4)
      (hxy : ¬ (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d] x) (![a, b, c, d] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h; subst y; simp_all
  obtain ⟨x, y, hax, hay, hxb, hyb, hxy⟩ :=
    exists_two_other_neighbors_of_degree_three
      (C.red_or_blue_degree a (Or.inl ha)) hab
  have hxSide := C.other_neighbor_of_red_is_blueSide ha hb hab hax hxb
  have hySide := C.other_neighbor_of_red_is_blueSide ha hb hab hay hyb
  have hx : C.color x = .bluish := by
    rcases hxSide with hx | hx
    · exact (hNoBlueAtA x hax hx).elim
    · exact hx
  have hy : C.color y = .bluish := by
    rcases hySide with hy | hy
    · exact (hNoBlueAtA y hay hy).elim
    · exact hy
  obtain ⟨u, v, hfu, hfv, huc, hvc, huv⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hfdeg Q.hcf.symm
  have hud : u ≠ d := by intro h; subst u; exact hfd hfu
  have hvd : v ≠ d := by intro h; subst v; exact hfd hfv
  have hu := hOutsideF u hfu huc hud
  have hvv := hOutsideF v hfv hvc hvd
  by_cases hsx : G.Adj Q.f x
  · have hbf : ¬ G.Adj b Q.f :=
      C.reddish_not_adj_redSide Q.hf (Or.inl hb) ∘ SimpleGraph.Adj.symm
    have hbx : ¬ G.Adj b x := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbe
      · exact hv (x := (0 : Fin 4)) (y := 2) (by decide)
      · exact Q.hea.symm
      · exact Q.hec.symm
      · exact color_ne hx ha (by decide)
      · exact color_ne hx hc (by decide)
      · intro h; subst x; exact hea hax.symm
    have hxc : ¬ G.Adj x c :=
      C.bluish_not_adj_blueSide hx (Or.inl hc)
    have haf : ¬ G.Adj a Q.f :=
      C.reddish_not_adj_redSide Q.hf (Or.inl ha) ∘ SimpleGraph.Adj.symm
    have hcx : ¬ G.Adj c x := fun h => hxc h.symm
    have hpent : FormsInducedPentagon G b a Q.f c x := by
      dsimp [FormsInducedPentagon]
      refine ⟨?_, ?_⟩
      · have hn : [b, a, Q.f, c, x].Nodup := by
          simp [hab.ne.symm, hbc.ne, hsx.ne,
            color_ne ha Q.hf (by decide), color_ne ha hx (by decide),
            color_ne ha hc (by decide), color_ne hb Q.hf (by decide),
            color_ne hb hx (by decide), color_ne Q.hf hc (by decide),
            color_ne hc hx (by decide)]
        have hvec : (![b, a, Q.f, c, x] : Fin 5 → V) =
            [b, a, Q.f, c, x].get := by funext i; fin_cases i <;> rfl
        rw [hvec]
        exact hn.injective_get
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [graphOfEdges, G.adj_comm, hab, hax, hbc, Q.hcf,
            hsx.symm, hac, hbf, hbx, haf, hcx]
    have hbNoBlue : ∀ z, G.Adj b z → z ≠ c → z ≠ x →
        C.color z ≠ .blue := by
      intro z hbz hzc _ hz
      have hza : z ≠ a := color_ne hz ha (by decide)
      have hze : z ≠ Q.e := color_ne hz Q.he (by decide)
      exact (C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbe
        (hv (x := (0 : Fin 4)) (y := 2) (by decide)) Q.hea.symm Q.hec.symm
        hza hzc hze hbz).elim
    have haNoBlue : ∀ z, G.Adj a z → z ≠ c → z ≠ x →
        C.color z ≠ .blue := by
      intro z haz _ _ hz
      exact hNoBlueAtA z haz hz
    have hfNoBlue : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ x →
        C.color z ≠ .blue := by
      intro z hfz hzc _ hz
      have hzd : z ≠ d := by intro h; subst z; exact hfd hfz
      have hz' := hOutsideF z hfz hzc hzd
      simp [hz] at hz'
    rcases lemma5_5 C hpent hb ha Q.hf hc (Or.inr hx)
        hbNoBlue haNoBlue hfNoBlue with hntr | hce
    · exact HasReachableNegativeReduction.of_current_ntr C hntr
    · exact HasReachableNegativeReduction.of_current_ce C hce
  · by_cases hsy : G.Adj Q.f y
    · have hswap : FormsInducedPentagon G b a Q.f c y := by
        -- This is the preceding shared-neighbor argument with `x,y` exchanged.
        have hbf : ¬ G.Adj b Q.f :=
          C.reddish_not_adj_redSide Q.hf (Or.inl hb) ∘ SimpleGraph.Adj.symm
        have hby : ¬ G.Adj b y := by
          apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbe
          · exact hv (x := (0 : Fin 4)) (y := 2) (by decide)
          · exact Q.hea.symm
          · exact Q.hec.symm
          · exact color_ne hy ha (by decide)
          · exact color_ne hy hc (by decide)
          · intro h; subst y; exact hea hay.symm
        have hyc : ¬ G.Adj y c :=
          C.bluish_not_adj_blueSide hy (Or.inl hc)
        have haf : ¬ G.Adj a Q.f :=
          C.reddish_not_adj_redSide Q.hf (Or.inl ha) ∘ SimpleGraph.Adj.symm
        have hcy : ¬ G.Adj c y := fun h => hyc h.symm
        dsimp [FormsInducedPentagon]
        refine ⟨?_, ?_⟩
        · have hn : [b, a, Q.f, c, y].Nodup := by
            simp [hab.ne.symm, hbc.ne, hsy.ne,
              color_ne ha Q.hf (by decide), color_ne ha hy (by decide),
              color_ne ha hc (by decide), color_ne hb Q.hf (by decide),
              color_ne hb hy (by decide), color_ne Q.hf hc (by decide),
              color_ne hc hy (by decide)]
          have hvec : (![b, a, Q.f, c, y] : Fin 5 → V) =
              [b, a, Q.f, c, y].get := by funext i; fin_cases i <;> rfl
          rw [hvec]
          exact hn.injective_get
        · intro i j
          fin_cases i <;> fin_cases j <;>
            simp [graphOfEdges, G.adj_comm, hab, hay, hbc, Q.hcf,
              hsy.symm, hac, hbf, hby, haf, hcy]
      have hbNoBlue : ∀ z, G.Adj b z → z ≠ c → z ≠ y →
          C.color z ≠ .blue := by
        intro z hbz hzc _ hz
        have hza : z ≠ a := color_ne hz ha (by decide)
        have hze : z ≠ Q.e := color_ne hz Q.he (by decide)
        exact (C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbe
          (hv (x := (0 : Fin 4)) (y := 2) (by decide)) Q.hea.symm Q.hec.symm
          hza hzc hze hbz).elim
      have haNoBlue : ∀ z, G.Adj a z → z ≠ c → z ≠ y →
          C.color z ≠ .blue := by intro z haz _ _ hz; exact hNoBlueAtA z haz hz
      have hfNoBlue : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ y →
          C.color z ≠ .blue := by
        intro z hfz hzc _ hz
        have hzd : z ≠ d := by intro h; subst z; exact hfd hfz
        have hz' := hOutsideF z hfz hzc hzd
        simp [hz] at hz'
      rcases lemma5_5 C hswap hb ha Q.hf hc (Or.inr hy)
          hbNoBlue haNoBlue hfNoBlue with hntr | hce
      · exact HasReachableNegativeReduction.of_current_ntr C hntr
      · exact HasReachableNegativeReduction.of_current_ce C hce
    · apply HasReachableNegativeReduction.of_current_ntr C
      apply containsNegativeAf C Q.hf ha hb hu hvv hx hy hc hd Q.he
        hfu hfv Q.hcf.symm hab hax hay hbc Q.hbe hcd
        hsx hsy hfd (fun h => hef h.symm)
      have hux : u ≠ x := by intro h; subst u; exact hsx hfu
      have huy : u ≠ y := by intro h; subst u; exact hsy hfu
      have hvx : v ≠ x := by intro h; subst v; exact hsx hfv
      have hvy : v ≠ y := by intro h; subst v; exact hsy hfv
      have hue : u ≠ Q.e := by intro h; subst u; exact hef hfu.symm
      have hve : v ≠ Q.e := by intro h; subst v; exact hef hfv.symm
      have hxe : x ≠ Q.e := by intro h; subst x; exact hea hax.symm
      have hye : y ≠ Q.e := by intro h; subst y; exact hea hay.symm
      simp [hab.ne, hcd.ne, huv, hxy, hux, huy, hvx, hvy,
        hue, hve, hxe, hye,
        color_ne Q.hf ha (by decide), color_ne Q.hf hb (by decide),
        color_ne Q.hf hu (by decide), color_ne Q.hf hvv (by decide),
        color_ne Q.hf hx (by decide), color_ne Q.hf hy (by decide),
        color_ne Q.hf hc (by decide), color_ne Q.hf hd (by decide),
        color_ne Q.hf Q.he (by decide),
        color_ne ha hu (by decide), color_ne ha hvv (by decide),
        color_ne ha hx (by decide), color_ne ha hy (by decide),
        color_ne ha hc (by decide), color_ne ha hd (by decide),
        color_ne ha Q.he (by decide),
        color_ne hb hu (by decide), color_ne hb hvv (by decide),
        color_ne hb hx (by decide), color_ne hb hy (by decide),
        color_ne hb hc (by decide), color_ne hb hd (by decide),
        color_ne hb Q.he (by decide),
        color_ne hu hc (by decide), color_ne hu hd (by decide),
        color_ne hvv hc (by decide), color_ne hvv hd (by decide),
        color_ne hx hc (by decide), color_ne hx hd (by decide),
        color_ne hy hc (by decide), color_ne hy hd (by decide),
        color_ne hc Q.he (by decide), color_ne hd Q.he (by decide)]

end Subcubic
