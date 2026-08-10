import Subcubic.Lemma5_13.Case4ExactBlueNoRed

/-! Lemma 5.13, Case (4.4.4.2). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(al): the reddish neighborhoods of `d,e,g` are pairwise
disjoint and `d` does not meet `f`. -/
theorem lemma5_13_case4_disjoint_avoids_f
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {x y h s : V}
    (hx : C.color x = .reddish) (hy : C.color y = .reddish)
    (hh : C.color h = .reddish) (hs : C.color s = .reddish)
    (hgx : G.Adj Q.g x) (hgy : G.Adj Q.g y)
    (hdh : G.Adj d h) (hds : G.Adj d s)
    (hcd : G.Adj c d) (hbc : G.Adj b c) (hab : G.Adj a b)
    (hgr : ¬ G.Adj Q.g Q.r) (hgf : ¬ G.Adj Q.g Q.f)
    (hgh : ¬ G.Adj Q.g h) (hgs : ¬ G.Adj Q.g s)
    (hex : ¬ G.Adj Q.e x) (hey : ¬ G.Adj Q.e y)
    (heh : ¬ G.Adj Q.e h) (hes : ¬ G.Adj Q.e s)
    (hn : [Q.g, Q.e, c, d, x, y, Q.r, a, b, Q.f, h, s].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .al
    (![Q.g, Q.e, c, d, x, y, Q.r, a, b, Q.f, h, s])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec :
        (![Q.g, Q.e, c, d, x, y, Q.r, a, b, Q.f, h, s] : Fin 12 → V) =
        [Q.g, Q.e, c, d, x, y, Q.r, a, b, Q.f, h, s].get := by
      funext z; fin_cases z <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro p q hpq
    apply (negativeTailReducerData .al).adj_map_of_edgesMapTo G _ ?_ hpq
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 4), (0, 5), (0, 7), (1, 6), (1, 7),
      (1, 8), (2, 3), (2, 8), (2, 9), (3, 10), (3, 11), (7, 8)] at hedge
    simp at hedge
    rcases hedge with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hgx
    · exact hgy
    · exact Q.hag.symm
    · exact Q.her
    · exact Q.heaEdge
    · exact Q.hbe.symm
    · exact hcd
    · exact hbc.symm
    · exact Q.hcf
    · exact hdh
    · exact hds
    · exact hab
  · intro z
    have hcolors : (negativeTailReducer .al).color =
        ![.reddish, .reddish, .red, .red, .bluish, .bluish,
          .bluish, .blue, .blue, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases z
    · change (C.color Q.g).swap = .reddish; simp [Q.hg]
    · change (C.color Q.e).swap = .reddish; simp [Q.he]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color y).swap = .bluish; simp [hy]
    · change (C.color Q.r).swap = .bluish; simp [Q.hr]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color s).swap = .bluish; simp [hs]
  · intro p q hpq hnon hauto
    have hp := negativeAl_boundaryNonedges p q hpq hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩)
    all_goals first
      | exact hgr | exact hgf | exact hgh | exact hgs
      | exact hex | exact hey | exact Q.hef | exact heh | exact hes
      | exact fun h => hgr h.symm | exact fun h => hgf h.symm
      | exact fun h => hgh h.symm | exact fun h => hgs h.symm
      | exact fun h => hex h.symm | exact fun h => hey h.symm
      | exact fun h => Q.hef h.symm | exact fun h => heh h.symm
      | exact fun h => hes h.symm

end Subcubic
