import Subcubic.Lemma5_13.Case4SharedEG

/-! Lemma 5.13, Case (4.4.2): `g` has degree one or two. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_low_degree
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hgf : ¬ G.Adj Q.g Q.f)
    (hNoOtherRedG : ∀ z, G.Adj Q.g z → C.color z = .red → z = a)
    (hNoShareEG : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj Q.g z)
    (hdeg : vertexDegree G Q.g = 1 ∨ vertexDegree G Q.g = 2) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
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
  have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
  have hrf : Q.r ≠ Q.f := by
    intro e
    apply Q.hef
    rw [← e]
    exact Q.her
  have hcr : ¬ G.Adj c Q.r := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hcf
    · exact color_ne hd hb (by decide)
    · exact color_ne hd Q.hf (by decide)
    · exact color_ne hb Q.hf (by decide)
    · exact color_ne Q.hr hd (by decide)
    · exact color_ne Q.hr hb (by decide)
    · exact hrf
  have baseNodup : [Q.g, Q.e, c, Q.r, a, b, Q.f].Nodup := by
    simp [Q.hge, Q.her.ne, Q.heaEdge.ne,
      hab.ne, Q.hcf.ne,
      color_ne Q.hg hc (by decide), color_ne Q.hg Q.hr (by decide),
      color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
      color_ne Q.hg Q.hf (by decide), color_ne Q.he hc (by decide),
      color_ne Q.he hb (by decide), color_ne Q.he Q.hf (by decide),
      color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
      color_ne hc hb (by decide), color_ne Q.hr ha (by decide),
      color_ne Q.hr hb (by decide), hrf, color_ne ha Q.hf (by decide),
      color_ne hb Q.hf (by decide)]
  rcases hdeg with hdeg1 | hdeg2
  · apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegative_of_embedding_with_degree C.swapSides .dcH
      (![Q.g, Q.e, c, Q.r, a, b, Q.f])
    · change vertexDegree G Q.g = 1
      exact hdeg1
    · have hvec : (![Q.g, Q.e, c, Q.r, a, b, Q.f] : Fin 7 → V) =
          [Q.g, Q.e, c, Q.r, a, b, Q.f].get := by
        funext i; fin_cases i <;> rfl
      rw [hvec]
      exact baseNodup.injective_get
    · intro i j hij
      apply (negativeTailReducerData .dcH).adj_map_of_edgesMapTo G _ ?_ hij
      unfold PatternData.EdgesMapTo
      dsimp only [negativeTailReducerData]
      intro e he
      change e ∈ [(0, 4), (1, 3), (1, 4), (1, 5),
        (2, 5), (2, 6), (4, 5)] at he
      simp at he
      rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact Q.hag.symm
      · exact Q.her
      · exact Q.heaEdge
      · exact Q.hbe.symm
      · exact hbc.symm
      · exact Q.hcf
      · exact hab
    · intro i
      have hcolors : (negativeTailReducer .dcH).color =
          ![.reddish, .reddish, .red, .bluish, .blue, .blue, .bluish] := by
        native_decide
      rw [hcolors]
      fin_cases i
      · change (C.color Q.g).swap = .reddish; simp [Q.hg]
      · change (C.color Q.e).swap = .reddish; simp [Q.he]
      · change (C.color c).swap = .red; simp [hc]
      · change (C.color Q.r).swap = .bluish; simp [Q.hr]
      · change (C.color a).swap = .blue; simp [ha]
      · change (C.color b).swap = .blue; simp [hb]
      · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · intro i j hne hnon hauto
      have hp := negativeDcH_boundaryNonedges i j hne hnon hauto
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals first
        | exact hgc | exact hgr | exact hgf | exact hec | exact Q.hef
        | exact hcr
        | exact fun h => hgc h.symm | exact fun h => hgr h.symm
        | exact fun h => hgf h.symm | exact fun h => hec h.symm
        | exact fun h => Q.hef h.symm | exact fun h => hcr h.symm
  · obtain ⟨x, hgx, hxa⟩ := exists_other_neighbor_of_degree_two hdeg2 Q.hag.symm
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
    have hex' : ¬ G.Adj Q.e x := fun h => hNoShareEG x hx h hgx
    have hcx : ¬ G.Adj c x := by
      apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hcf
      · exact color_ne hd hb (by decide)
      · exact color_ne hd Q.hf (by decide)
      · exact color_ne hb Q.hf (by decide)
      · exact color_ne hx hd (by decide)
      · exact color_ne hx hb (by decide)
      · intro e; subst x; exact hgf hgx
    have hxr : x ≠ Q.r := by
      intro e; subst x; exact hgr hgx
    have hxf : x ≠ Q.f := by intro e; subst x; exact hgf hgx
    have hn : [Q.g, Q.e, c, x, Q.r, a, b, Q.f].Nodup := by
      simp [Q.hge, hgx.ne, Q.her.ne,
        Q.heaEdge.ne, hab.ne, Q.hcf.ne, hxr, hxf,
        color_ne Q.hg hc (by decide), color_ne Q.hg Q.hr (by decide),
        color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
        color_ne Q.hg Q.hf (by decide), color_ne Q.he hc (by decide),
        color_ne Q.he hx (by decide), color_ne Q.he hb (by decide),
        color_ne Q.he Q.hf (by decide), color_ne hc hx (by decide),
        color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
        color_ne hc hb (by decide), color_ne hx ha (by decide),
        color_ne hx hb (by decide), color_ne Q.hr ha (by decide),
        color_ne Q.hr hb (by decide), hrf, color_ne ha Q.hf (by decide),
        color_ne hb Q.hf (by decide)]
    apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegative_of_embedding_with_degree C.swapSides .dcG
      (![Q.g, Q.e, c, x, Q.r, a, b, Q.f])
    · change vertexDegree G Q.g = 2
      exact hdeg2
    · have hvec : (![Q.g, Q.e, c, x, Q.r, a, b, Q.f] : Fin 8 → V) =
          [Q.g, Q.e, c, x, Q.r, a, b, Q.f].get := by
        funext i; fin_cases i <;> rfl
      rw [hvec]
      exact hn.injective_get
    · intro i j hij
      apply (negativeTailReducerData .dcG).adj_map_of_edgesMapTo G _ ?_ hij
      unfold PatternData.EdgesMapTo
      dsimp only [negativeTailReducerData]
      intro e he
      change e ∈ [(0, 3), (0, 5), (1, 4), (1, 5),
        (1, 6), (2, 6), (2, 7), (5, 6)] at he
      simp at he
      rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hgx
      · exact Q.hag.symm
      · exact Q.her
      · exact Q.heaEdge
      · exact Q.hbe.symm
      · exact hbc.symm
      · exact Q.hcf
      · exact hab
    · intro i
      have hcolors : (negativeTailReducer .dcG).color =
          ![.reddish, .reddish, .red, .bluish, .bluish,
            .blue, .blue, .bluish] := by native_decide
      rw [hcolors]
      fin_cases i
      · change (C.color Q.g).swap = .reddish; simp [Q.hg]
      · change (C.color Q.e).swap = .reddish; simp [Q.he]
      · change (C.color c).swap = .red; simp [hc]
      · change (C.color x).swap = .bluish; simp [hx]
      · change (C.color Q.r).swap = .bluish; simp [Q.hr]
      · change (C.color a).swap = .blue; simp [ha]
      · change (C.color b).swap = .blue; simp [hb]
      · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · intro i j hne hnon hauto
      have hp := negativeDcG_boundaryNonedges i j hne hnon hauto
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals first
        | exact hgc | exact hgr | exact hgf | exact hec | exact hex'
        | exact Q.hef | exact hcx | exact hcr
        | exact fun h => hgc h.symm | exact fun h => hgr h.symm
        | exact fun h => hgf h.symm | exact fun h => hec h.symm
        | exact fun h => hex' h.symm | exact fun h => Q.hef h.symm
        | exact fun h => hcx h.symm | exact fun h => hcr h.symm

end Subcubic
