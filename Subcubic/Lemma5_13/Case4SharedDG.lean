import Subcubic.Lemma5_13.Case4LowDegree

/-! Lemma 5.13, Cases (4.4.3.1) and (4.4.3.2). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(ag): `d` meets `f`, and `d,g` share the reddish vertex `s`. -/
theorem lemma5_13_case4_shared_dg_meets_f
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hgf : ¬ G.Adj Q.g Q.f)
    (hNoShareEG : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj Q.g z)
    {x s : V} (hx : C.color x = .reddish) (hs : C.color s = .reddish)
    (hgx : G.Adj Q.g x) (hgs : G.Adj Q.g s) (hxs : x ≠ s)
    (hds : G.Adj d s) (hdf : G.Adj d Q.f) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj u v) :
      G.Adj (![a, b, c, d] u) (![a, b, c, d] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e; subst v; simp_all
  have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
  have hex : ¬ G.Adj Q.e x := fun h => hNoShareEG x hx h hgx
  have hes : ¬ G.Adj Q.e s := fun h => hNoShareEG s hs h hgs
  have hxr : x ≠ Q.r := by intro e; subst x; exact hgr hgx
  have hxf : x ≠ Q.f := by intro e; subst x; exact hgf hgx
  have hrs : Q.r ≠ s := by intro e; subst s; exact hgr hgs
  have hrf : Q.r ≠ Q.f := by
    intro e; apply Q.hef; rw [← e]; exact Q.her
  have hfs : Q.f ≠ s := by intro e; subst s; exact hgf hgs
  have hn : [Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s].Nodup := by
    simp [Q.hge, hgx.ne, hgs.ne, Q.her.ne, Q.heaEdge.ne, Q.hbe.ne,
      hcd.ne, hbc.ne, hab.ne, Q.hcf.ne, hds.ne, hdf.ne,
      hxs, hxr, hxf, hrs, hrf, hfs,
      color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
      color_ne Q.hg hx (by decide), color_ne Q.hg Q.hr (by decide),
      color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
      color_ne Q.hg Q.hf (by decide), color_ne Q.hg hs (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he hd (by decide),
      color_ne Q.he hx (by decide), color_ne Q.he Q.hr (by decide),
      color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
      color_ne Q.he Q.hf (by decide), color_ne Q.he hs (by decide),
      color_ne hc hx (by decide), color_ne hc Q.hr (by decide),
      color_ne hc ha (by decide), color_ne hc hb (by decide),
      color_ne hc Q.hf (by decide), color_ne hc hs (by decide),
      color_ne hd hx (by decide), color_ne hd Q.hr (by decide),
      color_ne hd ha (by decide), color_ne hd hb (by decide),
      color_ne hd Q.hf (by decide), color_ne hd hs (by decide),
      color_ne hx ha (by decide), color_ne hx hb (by decide),
      color_ne Q.hr ha (by decide), color_ne Q.hr hb (by decide),
      color_ne ha Q.hf (by decide), color_ne ha hs (by decide),
      color_ne hb Q.hf (by decide), color_ne hb hs (by decide)]
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ag
    (![Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s] : Fin 10 → V) =
        [Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s].get := by
      funext i; fin_cases i <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro i j hij
    apply (negativeTailReducerData .ag).adj_map_of_edgesMapTo G _ ?_ hij
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 4), (0, 6), (0, 9), (1, 5), (1, 6),
      (1, 7), (2, 3), (2, 7), (2, 8), (3, 8), (3, 9), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hgx
    · exact Q.hag.symm
    · exact hgs
    · exact Q.her
    · exact Q.heaEdge
    · exact Q.hbe.symm
    · exact hcd
    · exact hbc.symm
    · exact Q.hcf
    · exact hdf
    · exact hds
    · exact hab
  · intro i
    have hcolors : (negativeTailReducer .ag).color =
        ![.reddish, .reddish, .red, .red, .bluish, .bluish,
          .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases i
    · change (C.color Q.g).swap = .reddish; simp [Q.hg]
    · change (C.color Q.e).swap = .reddish; simp [Q.he]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color Q.r).swap = .bluish; simp [Q.hr]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · change (C.color s).swap = .bluish; simp [hs]
  · intro i j hne hnon hauto
    have hp := negativeAg_boundaryNonedges i j hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hgr | exact hgf | exact hex | exact Q.hef | exact hes
      | exact fun h => hgr h.symm | exact fun h => hgf h.symm
      | exact fun h => hex h.symm | exact fun h => Q.hef h.symm
      | exact fun h => hes h.symm

/-- Figure 5(ah): `d` does not meet `f`, and both remaining neighbors of
`g` are also neighbors of `d`. -/
theorem lemma5_13_case4_two_shared_dg
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hgf : ¬ G.Adj Q.g Q.f) (hdf : ¬ G.Adj d Q.f)
    (hNoShareEG : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj Q.g z)
    {x s : V} (hx : C.color x = .reddish) (hs : C.color s = .reddish)
    (hgx : G.Adj Q.g x) (hgs : G.Adj Q.g s) (hxs : x ≠ s)
    (hdx : G.Adj d x) (hds : G.Adj d s) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj u v) :
      G.Adj (![a, b, c, d] u) (![a, b, c, d] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e; subst v; simp_all
  have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
  have hex : ¬ G.Adj Q.e x := fun h => hNoShareEG x hx h hgx
  have hes : ¬ G.Adj Q.e s := fun h => hNoShareEG s hs h hgs
  have hxr : x ≠ Q.r := by intro e; subst x; exact hgr hgx
  have hxf : x ≠ Q.f := by intro e; subst x; exact hgf hgx
  have hrs : Q.r ≠ s := by intro e; subst s; exact hgr hgs
  have hrf : Q.r ≠ Q.f := by intro e; apply Q.hef; rw [← e]; exact Q.her
  have hfs : Q.f ≠ s := by intro e; subst s; exact hgf hgs
  have hn : [Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s].Nodup := by
    simp [Q.hge, hgx.ne, hgs.ne, Q.her.ne, Q.heaEdge.ne,
      hcd.ne, hab.ne, Q.hcf.ne, hdx.ne, hds.ne,
      hxs, hxr, hxf, hrs, hrf, hfs,
      color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
      color_ne Q.hg hx (by decide), color_ne Q.hg Q.hr (by decide),
      color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
      color_ne Q.hg Q.hf (by decide), color_ne Q.hg hs (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he hd (by decide),
      color_ne Q.he hx (by decide), color_ne Q.he Q.hr (by decide),
      color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
      color_ne Q.he Q.hf (by decide), color_ne Q.he hs (by decide),
      color_ne hc hx (by decide), color_ne hc Q.hr (by decide),
      color_ne hc ha (by decide), color_ne hc hb (by decide),
      color_ne hc Q.hf (by decide), color_ne hc hs (by decide),
      color_ne hd hx (by decide), color_ne hd Q.hr (by decide),
      color_ne hd ha (by decide), color_ne hd hb (by decide),
      color_ne hd Q.hf (by decide), color_ne hd hs (by decide),
      color_ne hx ha (by decide), color_ne hx hb (by decide),
      color_ne Q.hr ha (by decide), color_ne Q.hr hb (by decide),
      color_ne ha Q.hf (by decide), color_ne ha hs (by decide),
      color_ne hb Q.hf (by decide), color_ne hb hs (by decide)]
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ah
    (![Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s] : Fin 10 → V) =
        [Q.g, Q.e, c, d, x, Q.r, a, b, Q.f, s].get := by
      funext i; fin_cases i <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro i j hij
    apply (negativeTailReducerData .ah).adj_map_of_edgesMapTo G _ ?_ hij
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 4), (0, 6), (0, 9), (1, 5), (1, 6),
      (1, 7), (2, 3), (2, 7), (2, 8), (3, 4), (3, 9), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hgx
    · exact Q.hag.symm
    · exact hgs
    · exact Q.her
    · exact Q.heaEdge
    · exact Q.hbe.symm
    · exact hcd
    · exact hbc.symm
    · exact Q.hcf
    · exact hdx
    · exact hds
    · exact hab
  · intro i
    have hcolors : (negativeTailReducer .ah).color =
        ![.reddish, .reddish, .red, .red, .bluish, .bluish,
          .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases i
    · change (C.color Q.g).swap = .reddish; simp [Q.hg]
    · change (C.color Q.e).swap = .reddish; simp [Q.he]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color Q.r).swap = .bluish; simp [Q.hr]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · change (C.color s).swap = .bluish; simp [hs]
  · intro i j hne hnon hauto
    have hp := negativeAh_boundaryNonedges i j hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hgr | exact hgf | exact hex | exact Q.hef | exact hes
      | exact fun h => hgr h.symm | exact fun h => hgf h.symm
      | exact fun h => hex h.symm | exact fun h => Q.hef h.symm
      | exact fun h => hes h.symm

end Subcubic
