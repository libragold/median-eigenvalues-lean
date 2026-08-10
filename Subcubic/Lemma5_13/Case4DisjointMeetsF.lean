import Subcubic.Lemma5_13.Case4Disjoint

/-! Lemma 5.13, Case (4.4.4.1). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Figure 5(an): after the temporary-flip reductions, the reddish
neighborhoods of `g,e,h` are disjoint. -/
theorem lemma5_13_case4_disjoint_meets_f_no_share
    (C : GoodColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {h x y s u v : V}
    (hh : C.color h = .bluish)
    (hx : C.color x = .reddish) (hy : C.color y = .reddish)
    (hs : C.color s = .reddish) (hu : C.color u = .reddish)
    (hv : C.color v = .reddish)
    (hga : G.Adj Q.g a) (hgx : G.Adj Q.g x) (hgy : G.Adj Q.g y)
    (her : G.Adj Q.e Q.r) (hea : G.Adj Q.e a) (heb : G.Adj Q.e b)
    (hcd : G.Adj c d) (hbc : G.Adj b c) (hcf : G.Adj c Q.f)
    (hdf : G.Adj d Q.f) (hds : G.Adj d s)
    (hhf : G.Adj h Q.f) (hhu : G.Adj h u) (hhv : G.Adj h v)
    (hab : G.Adj a b)
    (hgr : ¬ G.Adj Q.g Q.r) (hgf : ¬ G.Adj Q.g Q.f)
    (hgs : ¬ G.Adj Q.g s) (hgu : ¬ G.Adj Q.g u)
    (hgv : ¬ G.Adj Q.g v)
    (hex : ¬ G.Adj Q.e x) (hey : ¬ G.Adj Q.e y)
    (hef : ¬ G.Adj Q.e Q.f) (hes : ¬ G.Adj Q.e s)
    (heu : ¬ G.Adj Q.e u) (hev : ¬ G.Adj Q.e v)
    (hhx : ¬ G.Adj h x) (hhy : ¬ G.Adj h y)
    (hhr : ¬ G.Adj h Q.r) (hhs : ¬ G.Adj h s)
    (hn : [Q.g, Q.e, c, d, h, x, y, Q.r,
      a, b, Q.f, s, u, v].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ao
    (![Q.g, Q.e, c, d, h, x, y, Q.r, a, b, Q.f, s, u, v])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec :
        (![Q.g, Q.e, c, d, h, x, y, Q.r, a, b, Q.f, s, u, v] :
          Fin 14 → V) =
        [Q.g, Q.e, c, d, h, x, y, Q.r, a, b, Q.f, s, u, v].get := by
      funext z; fin_cases z <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro p q hpq
    apply (negativeTailReducerData .ao).adj_map_of_edgesMapTo G _ ?_ hpq
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 5), (0, 6), (0, 8), (1, 7), (1, 8),
      (1, 9), (2, 3), (2, 9), (2, 10), (3, 10), (3, 11),
      (4, 10), (4, 12), (4, 13), (8, 9)] at hedge
    simp at hedge
    rcases hedge with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | assumption | exact hbc.symm
  · intro z
    have hcolors : (negativeTailReducer .ao).color =
        ![.reddish, .reddish, .red, .red, .reddish,
          .bluish, .bluish, .bluish, .blue, .blue,
          .bluish, .bluish, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases z
    · change (C.color Q.g).swap = .reddish; simp [Q.hg]
    · change (C.color Q.e).swap = .reddish; simp [Q.he]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color h).swap = .reddish; simp [hh]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color y).swap = .bluish; simp [hy]
    · change (C.color Q.r).swap = .bluish; simp [Q.hr]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · change (C.color s).swap = .bluish; simp [hs]
    · change (C.color u).swap = .bluish; simp [hu]
    · change (C.color v).swap = .bluish; simp [hv]
  · intro p q hpq hnon hauto
    have hp := negativeAo_boundaryNonedges p q hpq hnon hauto
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
    rcases hp with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
         ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals first
      | exact hgr | exact hgf | exact hgs | exact hgu | exact hgv
      | exact hex | exact hey | exact hef | exact hes | exact heu | exact hev
      | exact hhx | exact hhy | exact hhr | exact hhs
      | exact fun h => hgr h.symm | exact fun h => hgf h.symm
      | exact fun h => hgs h.symm | exact fun h => hgu h.symm
      | exact fun h => hgv h.symm | exact fun h => hex h.symm
      | exact fun h => hey h.symm | exact fun h => hef h.symm
      | exact fun h => hes h.symm | exact fun h => heu h.symm
      | exact fun h => hev h.symm | exact fun h => hhx h.symm
      | exact fun h => hhy h.symm | exact fun h => hhr h.symm
      | exact fun h => hhs h.symm

end Subcubic
