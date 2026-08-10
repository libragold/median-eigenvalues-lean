import Subcubic.Lemma5_13.Case4ExactNoRedG

/-! Lemma 5.13, Cases (4.4.3.3.2.3) and (4.4.3.3.2.4). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(ac): `i` meets the reddish third neighbor `f` of `c`. -/
theorem lemma5_13_case4_exact_no_red_meets_f
    (C : GoodColoring G) {a b c i g u x h f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hi : C.color i = .bluish)
    (hg : C.color g = .bluish)
    (hu : C.color u = .reddish) (hx : C.color x = .reddish)
    (hh : C.color h = .reddish) (hf : C.color f = .reddish)
    (hiu : G.Adj i u) (hih : G.Adj i h) (hif : G.Adj i f)
    (hgx : G.Adj g x) (hgh : G.Adj g h) (hga : G.Adj g a)
    (hcf : G.Adj c f) (hcb : G.Adj c b) (hab : G.Adj a b)
    (hic : ¬ G.Adj i c) (hix : ¬ G.Adj i x)
    (hia : ¬ G.Adj i a) (hib : ¬ G.Adj i b)
    (hgc : ¬ G.Adj g c) (hgu : ¬ G.Adj g u)
    (hgf : ¬ G.Adj g f) (hgb : ¬ G.Adj g b)
    (hcu : ¬ G.Adj c u) (hcx : ¬ G.Adj c x)
    (hch : ¬ G.Adj c h) (hca : ¬ G.Adj c a)
    (hn : [i, g, c, u, x, h, f, a, b].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ad
    (![i, g, c, u, x, h, f, a, b])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![i, g, c, u, x, h, f, a, b] : Fin 9 → V) =
        [i, g, c, u, x, h, f, a, b].get := by funext z; fin_cases z <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro p q hpq
    apply (negativeTailReducerData .ad).adj_map_of_edgesMapTo G _ ?_ hpq
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 5), (0, 6), (1, 4), (1, 5),
      (1, 7), (2, 6), (2, 8), (7, 8)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  · intro z
    have hcolors : (negativeTailReducer .ad).color =
        ![.reddish, .reddish, .red, .bluish, .bluish,
          .bluish, .bluish, .blue, .blue] := by native_decide
    rw [hcolors]
    fin_cases z
    · change (C.color i).swap = .reddish; simp [hi]
    · change (C.color g).swap = .reddish; simp [hg]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color u).swap = .bluish; simp [hu]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color f).swap = .bluish; simp [hf]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
  · intro p q hpq hnon hauto
    have hp := negativeAd_boundaryNonedges p q hpq hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hic | exact hix | exact hia | exact hib | exact hgc
      | exact hgu | exact hgf | exact hgb | exact hcu | exact hcx
      | exact hch | exact hca
      | exact fun h => hic h.symm | exact fun h => hix h.symm
      | exact fun h => hia h.symm | exact fun h => hib h.symm
      | exact fun h => hgc h.symm | exact fun h => hgu h.symm
      | exact fun h => hgf h.symm | exact fun h => hgb h.symm
      | exact fun h => hcu h.symm | exact fun h => hcx h.symm
      | exact fun h => hch h.symm | exact fun h => hca h.symm

/-- Figure 5(ad): `i` and `e` share a reddish neighbor `z`. -/
theorem lemma5_13_case4_exact_no_red_shared_e
    (C : GoodColoring G) {a b d i e u h z s : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hd : C.color d = .blue) (hi : C.color i = .bluish)
    (he : C.color e = .bluish)
    (hu : C.color u = .reddish) (hh : C.color h = .reddish)
    (hz : C.color z = .reddish) (hs : C.color s = .reddish)
    (hiu : G.Adj i u) (hih : G.Adj i h) (hiz : G.Adj i z)
    (hez : G.Adj e z) (hea : G.Adj e a) (heb : G.Adj e b)
    (hdh : G.Adj d h) (hds : G.Adj d s) (hab : G.Adj a b)
    (hid : ¬ G.Adj i d) (hia : ¬ G.Adj i a) (hib : ¬ G.Adj i b)
    (his : ¬ G.Adj i s) (hed : ¬ G.Adj e d)
    (heu : ¬ G.Adj e u) (heh : ¬ G.Adj e h) (hes : ¬ G.Adj e s)
    (hdu : ¬ G.Adj d u) (hdz : ¬ G.Adj d z)
    (hda : ¬ G.Adj d a) (hdb : ¬ G.Adj d b)
    (hn : [i, e, d, u, h, z, a, b, s].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ae
    (![i, e, d, u, h, z, a, b, s])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec : (![i, e, d, u, h, z, a, b, s] : Fin 9 → V) =
        [i, e, d, u, h, z, a, b, s].get := by funext q; fin_cases q <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro p q hpq
    apply (negativeTailReducerData .ae).adj_map_of_edgesMapTo G _ ?_ hpq
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 3), (0, 4), (0, 5), (1, 5), (1, 6),
      (1, 7), (2, 4), (2, 8), (6, 7)] at hedge
    simp at hedge
    rcases hedge with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals assumption
  · intro q
    have hcolors : (negativeTailReducer .ae).color =
        ![.reddish, .reddish, .red, .bluish, .bluish,
          .bluish, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases q
    · change (C.color i).swap = .reddish; simp [hi]
    · change (C.color e).swap = .reddish; simp [he]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color u).swap = .bluish; simp [hu]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color z).swap = .bluish; simp [hz]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color s).swap = .bluish; simp [hs]
  · intro p q hpq hnon hauto
    have hp := negativeAe_boundaryNonedges p q hpq hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hid | exact hia | exact hib | exact his | exact hed
      | exact heu | exact heh | exact hes | exact hdu | exact hdz
      | exact hda | exact hdb
      | exact fun h => hid h.symm | exact fun h => hia h.symm
      | exact fun h => hib h.symm | exact fun h => his h.symm
      | exact fun h => hed h.symm | exact fun h => heu h.symm
      | exact fun h => heh h.symm | exact fun h => hes h.symm
      | exact fun h => hdu h.symm | exact fun h => hdz h.symm
      | exact fun h => hda h.symm | exact fun h => hdb h.symm

end Subcubic
