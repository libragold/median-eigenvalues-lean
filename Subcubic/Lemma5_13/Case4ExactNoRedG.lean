import Subcubic.Lemma5_13.Case4ExactNoRedDG

/-! Lemma 5.13, Case (4.4.3.3.2.2): `i` and `g` overlap. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(v), used when `i` meets `f`. -/
theorem lemma5_13_case4_exact_no_red_shared_g_meets_f
    (C : GoodColoring G) {a b c i g h z f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hi : C.color i = .bluish)
    (hg : C.color g = .bluish)
    (hh : C.color h = .reddish) (hz : C.color z = .reddish)
    (hf : C.color f = .reddish)
    (hih : G.Adj i h) (hiz : G.Adj i z) (hif : G.Adj i f)
    (hgh : G.Adj g h) (hgz : G.Adj g z) (hga : G.Adj g a)
    (hcf : G.Adj c f) (hcb : G.Adj c b) (hab : G.Adj a b)
    (hic : ¬ G.Adj i c) (hia : ¬ G.Adj i a) (hib : ¬ G.Adj i b)
    (hgc : ¬ G.Adj g c) (hgf : ¬ G.Adj g f) (hgb : ¬ G.Adj g b)
    (hch : ¬ G.Adj c h) (hcz : ¬ G.Adj c z)
    (hca : ¬ G.Adj c a)
    (hn : [i, g, c, h, z, f, a, b].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .v (![i, g, c, h, z, f, a, b])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![i, g, c, h, z, f, a, b] : Fin 8 → V) =
        [i, g, c, h, z, f, a, b].get := by funext x; fin_cases x <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .v).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 5), (1, 3), (1, 4),
      (1, 6), (2, 5), (2, 7), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .v).color =
        ![.reddish, .reddish, .red, .bluish, .bluish, .bluish, .blue, .blue] := by
      native_decide
    rw [hcolors]
    fin_cases x
    · change (C.color i).swap = .reddish; simp [hi]
    · change (C.color g).swap = .reddish; simp [hg]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color z).swap = .bluish; simp [hz]
    · change (C.color f).swap = .bluish; simp [hf]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
  · intro x y hne hnon hauto
    have hp := negativeV_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hic | exact hia | exact hib | exact hgc | exact hgf
      | exact hgb | exact hch | exact hcz | exact hca
      | exact fun h => hic h.symm | exact fun h => hia h.symm
      | exact fun h => hib h.symm | exact fun h => hgc h.symm
      | exact fun h => hgf h.symm | exact fun h => hgb h.symm
      | exact fun h => hch h.symm | exact fun h => hcz h.symm
      | exact fun h => hca h.symm

/-- Figure 5(ab), used when `i` does not meet `f`. -/
theorem lemma5_13_case4_exact_no_red_shared_g_avoids_f
    (C : GoodColoring G) {a b c i g u h z f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hi : C.color i = .bluish)
    (hg : C.color g = .bluish)
    (hu : C.color u = .reddish) (hh : C.color h = .reddish)
    (hz : C.color z = .reddish) (hf : C.color f = .reddish)
    (hiu : G.Adj i u) (hih : G.Adj i h) (hiz : G.Adj i z)
    (hgh : G.Adj g h) (hgz : G.Adj g z) (hga : G.Adj g a)
    (hcb : G.Adj c b) (hcf : G.Adj c f) (hab : G.Adj a b)
    (hic : ¬ G.Adj i c) (hia : ¬ G.Adj i a) (hib : ¬ G.Adj i b)
    (hif : ¬ G.Adj i f) (hgc : ¬ G.Adj g c)
    (hgu : ¬ G.Adj g u) (hgb : ¬ G.Adj g b)
    (hgf : ¬ G.Adj g f) (hcu : ¬ G.Adj c u)
    (hch : ¬ G.Adj c h) (hcz : ¬ G.Adj c z)
    (hca : ¬ G.Adj c a)
    (hn : [i, g, c, u, h, z, a, b, f].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ab
    (![i, g, c, u, h, z, a, b, f])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![i, g, c, u, h, z, a, b, f] : Fin 9 → V) =
        [i, g, c, u, h, z, a, b, f].get := by funext x; fin_cases x <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro x y hxy
    apply (negativeTailReducerData .ab).adj_map_of_edgesMapTo G _ ?_ hxy
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 5), (1, 4), (1, 5),
      (1, 6), (2, 7), (2, 8), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  · intro x
    have hcolors : (negativeTailReducer .ab).color =
        ![.reddish, .reddish, .red, .bluish, .bluish,
          .bluish, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x
    · change (C.color i).swap = .reddish; simp [hi]
    · change (C.color g).swap = .reddish; simp [hg]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color u).swap = .bluish; simp [hu]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color z).swap = .bluish; simp [hz]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color f).swap = .bluish; simp [hf]
  · intro x y hne hnon hauto
    have hp := negativeAb_boundaryNonedges x y hne hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hic | exact hia | exact hib | exact hif | exact hgc
      | exact hgu | exact hgb | exact hgf | exact hcu | exact hch
      | exact hcz | exact hca
      | exact fun h => hic h.symm | exact fun h => hia h.symm
      | exact fun h => hib h.symm | exact fun h => hif h.symm
      | exact fun h => hgc h.symm | exact fun h => hgu h.symm
      | exact fun h => hgb h.symm | exact fun h => hgf h.symm
      | exact fun h => hcu h.symm | exact fun h => hch h.symm
      | exact fun h => hcz h.symm | exact fun h => hca h.symm

end Subcubic
