import Subcubic.Lemma5_13.Case4ExactShared

/-! Lemma 5.13, the terminal no-overlap configuration in Case (4.4.3.3.2). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Terminal no-overlap configuration.  The embedding below uses the order

`(i,g,e,c,d,u,v,x,h,r,a,b,f,s)`,

where `u,v` are the two neighbors of `i` other than `h`, `x` is the
neighbor of `g` other than `a,h`, and `s` is the neighbor of `d` other
than `c,h`.  We use the color-reversed catalogued reducer. -/
theorem lemma5_13_case4_exact_no_overlap
    (C : MatchingCutColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {h i u v x s : V}
    (hh : C.color h = .reddish) (hi : C.color i = .bluish)
    (hu : C.color u = .reddish) (hv : C.color v = .reddish)
    (hx : C.color x = .reddish) (hs : C.color s = .reddish)
    (hih : G.Adj i h) (hiu : G.Adj i u) (hiv : G.Adj i v)
    (hga : G.Adj Q.g a) (hgx : G.Adj Q.g x) (hgh : G.Adj Q.g h)
    (hda : G.Adj c d) (hdh : G.Adj d h) (hds : G.Adj d s)
    (hca : G.Adj b c) (hab : G.Adj a b)
    (hix : ¬ G.Adj i x) (hir : ¬ G.Adj i Q.r)
    (hif : ¬ G.Adj i Q.f) (his : ¬ G.Adj i s)
    (hgu : ¬ G.Adj Q.g u) (hgv : ¬ G.Adj Q.g v)
    (hgr : ¬ G.Adj Q.g Q.r) (hgf : ¬ G.Adj Q.g Q.f)
    (hgs : ¬ G.Adj Q.g s)
    (heu : ¬ G.Adj Q.e u) (hev : ¬ G.Adj Q.e v)
    (hex : ¬ G.Adj Q.e x) (heh : ¬ G.Adj Q.e h)
    (hes : ¬ G.Adj Q.e s)
    (hn : [i, Q.g, Q.e, c, d, u, v, x, h, Q.r,
      a, b, Q.f, s].Nodup) :
    HasReachableNegativeReduction C := by
  classical
  apply HasReachableNegativeReduction.of_current_ntr C
  apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
  apply containsNegative_of_embedding C.swapSides .ap
    (![i, Q.g, Q.e, c, d, u, v, x, h, Q.r, a, b, Q.f, s])
  · simp [NegativeTailReducerAmbientDegreeCondition]
  · have hvec :
        (![i, Q.g, Q.e, c, d, u, v, x, h, Q.r, a, b, Q.f, s] :
          Fin 14 → V) =
        [i, Q.g, Q.e, c, d, u, v, x, h, Q.r, a, b, Q.f, s].get := by
      funext z
      fin_cases z <;> rfl
    rw [hvec]
    exact hn.injective_get
  · intro p q hpq
    apply (negativeTailReducerData .ap).adj_map_of_edgesMapTo G _ ?_ hpq
    unfold PatternData.EdgesMapTo
    dsimp only [negativeTailReducerData]
    intro edge hedge
    change edge ∈ [(0, 5), (0, 6), (0, 8), (1, 7), (1, 8),
      (1, 10), (2, 9), (2, 10), (2, 11), (3, 4), (3, 11),
      (3, 12), (4, 8), (4, 13), (10, 11)] at hedge
    simp at hedge
    rcases hedge with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
       rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact hiu
    · exact hiv
    · exact hih
    · exact hgx
    · exact hgh
    · exact hga
    · exact Q.her
    · exact Q.heaEdge
    · exact Q.hbe.symm
    · exact hda
    · exact hca.symm
    · exact Q.hcf
    · exact hdh
    · exact hds
    · exact hab
  · intro z
    have hcolors : (negativeTailReducer .ap).color =
        ![.reddish, .reddish, .reddish, .red, .red,
          .bluish, .bluish, .bluish, .bluish, .bluish,
          .blue, .blue, .bluish, .bluish] := by native_decide
    rw [hcolors]
    fin_cases z
    · change (C.color i).swap = .reddish; simp [hi]
    · change (C.color Q.g).swap = .reddish; simp [Q.hg]
    · change (C.color Q.e).swap = .reddish; simp [Q.he]
    · change (C.color c).swap = .red; simp [hc]
    · change (C.color d).swap = .red; simp [hd]
    · change (C.color u).swap = .bluish; simp [hu]
    · change (C.color v).swap = .bluish; simp [hv]
    · change (C.color x).swap = .bluish; simp [hx]
    · change (C.color h).swap = .bluish; simp [hh]
    · change (C.color Q.r).swap = .bluish; simp [Q.hr]
    · change (C.color a).swap = .blue; simp [ha]
    · change (C.color b).swap = .blue; simp [hb]
    · change (C.color Q.f).swap = .bluish; simp [Q.hf]
    · change (C.color s).swap = .bluish; simp [hs]
  · intro p q hpq hnon hauto
    have hp := negativeAp_boundaryNonedges p q hpq hnon hauto
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
      | exact hix | exact hir | exact hif | exact his
      | exact hgu | exact hgv | exact hgr | exact hgf | exact hgs
      | exact heu | exact hev | exact hex | exact heh
      | exact Q.hef | exact hes
      | exact fun h => hix h.symm | exact fun h => hir h.symm
      | exact fun h => hif h.symm | exact fun h => his h.symm
      | exact fun h => hgu h.symm | exact fun h => hgv h.symm
      | exact fun h => hgr h.symm | exact fun h => hgf h.symm
      | exact fun h => hgs h.symm | exact fun h => heu h.symm
      | exact fun h => hev h.symm | exact fun h => hex h.symm
      | exact fun h => heh h.symm | exact fun h => Q.hef h.symm
      | exact fun h => hes h.symm

end Subcubic
