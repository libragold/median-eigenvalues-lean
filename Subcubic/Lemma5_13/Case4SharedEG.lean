import Subcubic.Lemma5_13.Case4RedNeighbor

/-! Lemma 5.13, Case (4.4.1): `e` and `g` share a reddish neighbor. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_shared_eg
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hgf : ¬ G.Adj Q.g Q.f)
    (hNoOtherRedG : ∀ z, G.Adj Q.g z → C.color z = .red → z = a)
    {s : V} (hs : C.color s = .reddish)
    (hgs : G.Adj Q.g s) (hes : G.Adj Q.e s) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro e; subst y; simp_all
  have hgc : ¬ G.Adj Q.g c :=
    C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
  have hec : ¬ G.Adj Q.e c :=
    C.bluish_not_adj_blueSide Q.he (Or.inl hc)
  have hsf : s ≠ Q.f := by
    intro e
    subst s
    exact Q.hef hes
  have hcs : ¬ G.Adj c s := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hcf
    · exact color_ne hd hb (by decide)
    · exact color_ne hd Q.hf (by decide)
    · exact color_ne hb Q.hf (by decide)
    · exact color_ne hs hd (by decide)
    · exact color_ne hs hb (by decide)
    · exact hsf
  have baseNodup : [Q.g, Q.e, c, s, a, b, Q.f].Nodup := by
    simp [Q.hge, hgs.ne, hes.ne, hab.ne, Q.hcf.ne,
      color_ne Q.hg hc (by decide), color_ne Q.hg ha (by decide),
      color_ne Q.hg hb (by decide), color_ne Q.hg Q.hf (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he ha (by decide),
      color_ne Q.he hb (by decide), color_ne Q.he Q.hf (by decide),
      color_ne hc hs (by decide), color_ne hc ha (by decide),
      color_ne hc hb (by decide),
      color_ne hs ha (by decide), color_ne hs hb (by decide),
      hsf, color_ne ha Q.hf (by decide), color_ne hb Q.hf (by decide)]
  rcases C.degree_eq_two_or_three_of_two_neighbors
      (color_ne ha hs (by decide)) Q.hag.symm hgs with hdeg2 | hdeg3
  · apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegativeDcF C.swapSides
      (a := Q.g) (b := Q.e) (c := c) (d := s)
      (e := a) (f := b) (g := Q.f)
      (by simp [Q.hg]) (by simp [Q.he]) (by simp [hc]) (by simp [hs])
      (by simp [ha]) (by simp [hb]) (by simp [Q.hf]) hdeg2
      hgs Q.hag.symm hes Q.heaEdge Q.hbe.symm hbc.symm Q.hcf hab
      hgc hgf hec Q.hef hcs
    exact baseNodup
  · obtain ⟨x, hgx, hxa, hxs⟩ :=
      exists_third_neighbor_of_degree_three hdeg3 (color_ne ha hs (by decide))
    have hxSide : C.color x = .red ∨ C.color x = .reddish := by
      cases hxColor : C.color x with
      | red => exact Or.inl rfl
      | reddish => exact Or.inr rfl
      | blue => exact (C.bluish_not_adj_blueSide Q.hg (Or.inl hxColor) hgx).elim
      | bluish => exact (C.bluish_not_adj_blueSide Q.hg (Or.inr hxColor) hgx).elim
    have hx : C.color x = .reddish := by
      rcases hxSide with hx | hx
      · exact (hxa (hNoOtherRedG x hgx hx)).elim
      · exact hx
    have hxe : x ≠ Q.e := by
      intro e
      subst x
      exact C.bluish_not_adj_blueSide Q.hg (Or.inr Q.he) hgx
    have hex : ¬ G.Adj Q.e x := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hedeg
        Q.hbe.symm Q.heaEdge hes
      · exact hab.ne.symm
      · exact color_ne hb hs (by decide)
      · exact color_ne ha hs (by decide)
      · exact color_ne hx hb (by decide)
      · exact color_ne hx ha (by decide)
      · exact hxs
    have hxf : x ≠ Q.f := by
      intro e
      subst x
      exact hgf hgx
    have hcx : ¬ G.Adj c x := by
      apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hcf
      · exact color_ne hd hb (by decide)
      · exact color_ne hd Q.hf (by decide)
      · exact color_ne hb Q.hf (by decide)
      · exact color_ne hx hd (by decide)
      · exact color_ne hx hb (by decide)
      · exact hxf
    apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegative_of_embedding C.swapSides .v
      (![Q.g, Q.e, c, x, s, a, b, Q.f])
    · simp [NegativeTailReducerAmbientDegreeCondition]
    · have hn : [Q.g, Q.e, c, x, s, a, b, Q.f].Nodup := by
        simp [Q.hge, hgx.ne, hgs.ne, hxs, hes.ne, hab.ne, Q.hcf.ne,
          color_ne Q.hg hc (by decide), color_ne Q.hg ha (by decide),
          color_ne Q.hg hb (by decide), color_ne Q.hg Q.hf (by decide),
          color_ne Q.he hc (by decide), color_ne Q.he hx (by decide),
          color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
          color_ne Q.he Q.hf (by decide), color_ne hc hx (by decide),
          color_ne hc hs (by decide), color_ne hc ha (by decide),
          color_ne hc hb (by decide),
          color_ne hx ha (by decide), color_ne hx hb (by decide),
          color_ne hs ha (by decide), color_ne hs hb (by decide),
          hxf, hsf, color_ne ha Q.hf (by decide), color_ne hb Q.hf (by decide)]
      have hvec : (![Q.g, Q.e, c, x, s, a, b, Q.f] : Fin 8 → V) =
          [Q.g, Q.e, c, x, s, a, b, Q.f].get := by
        funext i; fin_cases i <;> rfl
      rw [hvec]
      exact hn.injective_get
    · intro i j hij
      apply (negativeTailReducerData .v).adj_map_of_edgesMapTo G _ ?_ hij
      unfold PatternData.EdgesMapTo
      dsimp only [negativeTailReducerData]
      intro e he
      change e ∈ [(0, 3), (0, 4), (0, 5), (1, 4), (1, 5),
        (1, 6), (2, 6), (2, 7), (5, 6)] at he
      simp at he
      rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hgx
      · exact hgs
      · exact Q.hag.symm
      · exact hes
      · exact Q.heaEdge
      · exact Q.hbe.symm
      · exact hbc.symm
      · exact Q.hcf
      · exact hab
    · intro i
      have hcolors : (negativeTailReducer .v).color =
          ![.reddish, .reddish, .red, .bluish, .bluish,
            .blue, .blue, .bluish] := by native_decide
      rw [hcolors]
      fin_cases i
      · change (C.color Q.g).swap = .reddish; simp [Q.hg]
      · change (C.color Q.e).swap = .reddish; simp [Q.he]
      · change (C.color c).swap = .red; simp [hc]
      · change (C.color x).swap = .bluish; simp [hx]
      · change (C.color s).swap = .bluish; simp [hs]
      · change (C.color a).swap = .blue; simp [ha]
      · change (C.color b).swap = .blue; simp [hb]
      · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · intro i j hne hnon hauto
      have hp := negativeV_boundaryNonedges i j hne hnon hauto
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals first
        | exact hgc | exact hgf | exact hec | exact hex | exact Q.hef
        | exact hcx | exact hcs
        | exact fun h => hgc h.symm | exact fun h => hgf h.symm
        | exact fun h => hec h.symm | exact fun h => hex h.symm
        | exact fun h => Q.hef h.symm | exact fun h => hcx h.symm
        | exact fun h => hcs h.symm

end Subcubic
