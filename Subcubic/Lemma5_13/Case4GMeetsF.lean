import Subcubic.Lemma5_13.Case4Shared

/-! Lemma 5.13, Case (4.3): the bluish vertex `g` meets `f`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_g_meets_f
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hOutsideF : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ d →
      C.color z = .bluish)
    (hgf : G.Adj Q.g Q.f) : HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
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
  have hbf : ¬ G.Adj b Q.f :=
    C.reddish_not_adj_redSide Q.hf (Or.inl hb) ∘ SimpleGraph.Adj.symm
  have haf : ¬ G.Adj a Q.f :=
    C.reddish_not_adj_redSide Q.hf (Or.inl ha) ∘ SimpleGraph.Adj.symm
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h; subst y; simp_all
  by_cases hfd : G.Adj Q.f d
  · apply HasReachableNegativeReduction.of_current_ntr C
    apply containsNegativeH C
      (a := a) (b := Q.f) (c := Q.e) (d := Q.g) (e := c) (f := d)
      ha Q.hf Q.he Q.hg hc hd Q.heaEdge.symm Q.hag hgf.symm
      Q.hcf.symm hfd hcd haf hac
      (by intro h; exact hNoBlueAtA d h hd) (fun h => Q.hef h.symm)
    simp [color_ne ha Q.hf (by decide), color_ne ha Q.he (by decide),
      color_ne ha Q.hg (by decide), color_ne ha hc (by decide),
      color_ne ha hd (by decide), color_ne Q.hf Q.he (by decide),
      color_ne Q.hf Q.hg (by decide), color_ne Q.hf hc (by decide),
      color_ne Q.hf hd (by decide), color_ne Q.he hc (by decide),
      color_ne Q.he hd (by decide), color_ne Q.hg hc (by decide),
      color_ne Q.hg hd (by decide), hcd.ne, Q.hge.symm]
  · obtain ⟨u, hfu, huc, hug⟩ :=
      exists_third_neighbor_of_degree_three Q.hfdeg
        (color_ne hc Q.hg (by decide))
    have hud : u ≠ d := by intro h; subst u; exact hfd hfu
    have hu := hOutsideF u hfu huc hud
    have heu : Q.e ≠ u := by
      intro h; subst u; exact Q.hef hfu.symm
    apply HasReachableNegativeReduction.of_current_ntr C
    apply containsNegativeS C
      (a := a) (b := b) (c := Q.f) (d := Q.g) (e := Q.e)
      (f := c) (g := d) (h := u)
      ha hb Q.hf Q.hg Q.he hc hd hu hab Q.hag Q.heaEdge.symm
      Q.hbe hbc hgf.symm Q.hcf.symm hfu hcd
      (fun h => Q.hef h.symm) hfd
    simp [hab.ne, hcd.ne, hfu.ne, hgf.ne.symm, Q.hge,
      hug.symm, heu,
      color_ne ha Q.hf (by decide), color_ne ha Q.hg (by decide),
      color_ne ha Q.he (by decide), color_ne ha hc (by decide),
      color_ne ha hd (by decide), color_ne ha hu (by decide),
      color_ne hb Q.hf (by decide), color_ne hb Q.hg (by decide),
      color_ne hb Q.he (by decide), color_ne hb hc (by decide),
      color_ne hb hd (by decide), color_ne hb hu (by decide),
      color_ne Q.hf Q.he (by decide),
      color_ne Q.hf hc (by decide), color_ne Q.hf hd (by decide),
      color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he hd (by decide),
      color_ne hc hu (by decide), color_ne hd hu (by decide)]

end Subcubic
