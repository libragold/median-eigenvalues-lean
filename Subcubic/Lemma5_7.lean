import Subcubic.Lemma5_6
import Subcubic.Lemma5_4
import Subcubic.Lemma4_5

/-!
# Lemma 5.7

This is the negative-tail analogue of Lemma 4.5.  The proof follows the two
sequential permitted flips.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
private theorem FormsInducedPath10.prefix6
    {a b c d e f g h i j : V}
    (hp : FormsInducedPath10 G a b c d e f g h i j) :
    FormsInducedPath6 G a b c d e f := by
  classical
  dsimp [FormsInducedPath10, FormsInducedPath6] at hp ⊢
  rcases hp with ⟨hinj, hedge⟩
  let ι : Fin 6 → Fin 10 := fun x => ⟨x, by omega⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    have hv : x.val = y.val := by
      simpa [ι] using congrArg Fin.val hxy
    exact Fin.ext hv
  have hmap (x : Fin 6) :
      ![a, b, c, d, e, f] x = ![a, b, c, d, e, f, g, h, i, j] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hι
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

omit [Fintype V] in
private theorem FormsInducedPath10.suffix6
    {a b c d e f g h i j : V}
    (hp : FormsInducedPath10 G a b c d e f g h i j) :
    FormsInducedPath6 G e f g h i j := by
  classical
  dsimp [FormsInducedPath10, FormsInducedPath6] at hp ⊢
  rcases hp with ⟨hinj, hedge⟩
  let ι : Fin 6 → Fin 10 := ![4, 5, 6, 7, 8, 9]
  have hι : Function.Injective ι := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ι]
  have hmap (x : Fin 6) :
      ![e, f, g, h, i, j] x = ![a, b, c, d, e, f, g, h, i, j] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hι
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

/-- **Lemma 5.7.** The alternating induced ten-vertex path has a reachable
negative reducer or cut enhancer. -/
theorem lemma5_7
    (C : MatchingCutColoring G) {a b c d e f g h i j : V}
    (hpath : FormsInducedPath10 G a b c d e f g h i j)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .red) (hj : C.color j = .red) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degreeC {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  have hprefix := hpath.prefix6
  have hsuffix := hpath.suffix6
  dsimp [FormsInducedPath10] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 10} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h, i, j] x) ≠
        (![a, b, c, d, e, f, g, h, i, j] y) := hinj.ne hxy
  have edge (x y : Fin 10) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
       (5, 6), (6, 7), (7, 8), (8, 9)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h, i, j] x)
        (![a, b, c, d, e, f, g, h, i, j] y) := (hedge x y).mp hxy
  have nonedge (x y : Fin 10) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
       (5, 6), (6, 7), (7, 8), (8, 9)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h, i, j] x)
        (![a, b, c, d, e, f, g, h, i, j] y) :=
    fun hadj => hxy ((hedge x y).mpr hadj)
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hfg : G.Adj f g := edge 5 6 (by native_decide)
  have hgh : G.Adj g h := edge 6 7 (by native_decide)
  have hhi : G.Adj h i := edge 7 8 (by native_decide)
  have hij : G.Adj i j := edge 8 9 (by native_decide)
  have current_ntr (hntr : ContainsNegativeTailReducer C) :
      HasReachableNegativeReduction C :=
    HasReachableNegativeReduction.of_current_ntr C hntr
  have current_ce (hce : ContainsCutEnhancer C) :
      HasReachableNegativeReduction C :=
    HasReachableNegativeReduction.of_current_ce C hce

  have hdf : d ≠ f := hv (x := (3 : Fin 10)) (y := 5) (by decide)
  obtain ⟨k, hek, hkd, hkf⟩ := C.exists_third_neighbor (degreeC (Or.inl he)) hdf
  have hkSide := C.other_neighbor_of_red_is_blueSide he hf hef hek hkf
  have hkc : k ≠ c := by
    intro hkc
    subst k
    exact (nonedge 4 2 (by native_decide)) hek
  rcases lemma3_3 C he hd hc hkSide hde.symm hek hcd.symm
      hkd.symm hkc.symm with hk | hceFound
  · by_cases hki : G.Adj k i
    · have hceSwap := containsCutEnhancerB_of C.swapSides
        (a := k) (b := e) (c := d) (d := i) (e := h)
        (by simp [hk]) (by simp [he]) (by simp [hd]) (by simp [hi])
        (by simp [hh]) hek.symm hki hde.symm hhi.symm
        (C.bluish_not_adj_blueSide hk (Or.inl hd))
        (C.bluish_not_adj_blueSide hk (Or.inl hh))
        (by simpa using nonedge 4 8 (by native_decide))
        (by simpa using nonedge 4 7 (by native_decide))
        (by simpa using nonedge 3 8 (by native_decide))
        (by simpa using nonedge 3 7 (by native_decide))
      exact current_ce
        ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
    · by_cases hkb : G.Adj k b
      · rcases lemma5_6 C hprefix ha hb hc hd he hf with hnone | hfound
        · exact (hnone ⟨k, hkb.symm, hek⟩).elim
        · exact hfound
      · have hegV : e ≠ g := hv (x := (4 : Fin 10)) (y := 6) (by decide)
        obtain ⟨l, hfl, hle, hlg⟩ := C.exists_third_neighbor
          (degreeC (Or.inl hf)) hegV
        have hlSide := C.other_neighbor_of_red_is_blueSide hf he hef.symm hfl hle
        have hlh : l ≠ h := by
          intro hlh
          subst l
          exact (nonedge 5 7 (by native_decide)) hfl
        rcases lemma3_3 C hf hg hh hlSide hfg hfl hgh
            hlg.symm hlh.symm with hl | hceFound
        · by_cases hlb : G.Adj l b
          · have hceSwap := containsCutEnhancerB_of C.swapSides
              (a := l) (b := f) (c := g) (d := b) (e := c)
              (by simp [hl]) (by simp [hf]) (by simp [hg]) (by simp [hb])
              (by simp [hc]) hfl.symm hlb hfg hbc
              (C.bluish_not_adj_blueSide hl (Or.inl hg))
              (C.bluish_not_adj_blueSide hl (Or.inl hc))
              (by simpa using nonedge 5 1 (by native_decide))
              (by simpa using nonedge 5 2 (by native_decide))
              (by simpa using nonedge 6 1 (by native_decide))
              (by simpa using nonedge 6 2 (by native_decide))
            exact current_ce
              ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
          · by_cases hli : G.Adj l i
            · rcases lemma5_6 C hsuffix he hf hg hh hi hj with hnone | hfound
              · exact (hnone ⟨l, hfl, hli.symm⟩).elim
              · exact hfound
            · rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
                (degreeC (Or.inl hb)) (degreeC (Or.inr hc))
                hab.symm hbc hcd with ⟨M₁, hflip₁⟩ | hce
              · let D₁ := M₁.toColoring
                have hi₁ : D₁.color i = .red :=
                  red_of_untouched_red_edge C hflip₁ (by simp [hi]) (by simp [hj])
                    hij
                    (hv (x := (8 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (8 : Fin 10)) (y := 2) (by decide))
                    (hv (x := (9 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (9 : Fin 10)) (y := 2) (by decide))
                have hj₁ : D₁.color j = .red :=
                  red_of_untouched_red_edge C hflip₁ (by simp [hj]) (by simp [hi])
                    hij.symm
                    (hv (x := (9 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (9 : Fin 10)) (y := 2) (by decide))
                    (hv (x := (8 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (8 : Fin 10)) (y := 2) (by decide))
                have hh₁ : D₁.color h = .blue :=
                  blue_of_untouched_blue_edge C hflip₁ (by simp [hh]) (by simp [hg])
                    hgh.symm
                    (hv (x := (7 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (7 : Fin 10)) (y := 2) (by decide))
                    (hv (x := (6 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (6 : Fin 10)) (y := 2) (by decide))
                have hg₁ : D₁.color g = .blue :=
                  blue_of_untouched_blue_edge C hflip₁ (by simp [hg]) (by simp [hh])
                    hgh
                    (hv (x := (6 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (6 : Fin 10)) (y := 2) (by decide))
                    (hv (x := (7 : Fin 10)) (y := 1) (by decide))
                    (hv (x := (7 : Fin 10)) (y := 2) (by decide))
                have degreeD₁ {v : V}
                    (hv : D₁.color v = .red ∨ D₁.color v = .blue) :
                    vertexDegree G v = 3 := by
                  rcases lemma3_6_negative D₁ hv with hdegree | hntr | hceD
                  · exact hdegree
                  · exact (hdone (HasReachableNegativeReduction.after_flip C hflip₁
                      (.of_current_ntr D₁ hntr))).elim
                  · exact (hdone (HasReachableNegativeReduction.after_flip C hflip₁
                      (.of_current_ce D₁ hceD))).elim
                rcases exists_flipAt_or_cutEnhancer D₁ hi₁ hh₁ hj₁ hg₁
                    (degreeD₁ (Or.inl hi₁)) (degreeD₁ (Or.inr hh₁))
                    hij hhi.symm hgh.symm with ⟨M₂, hflip₂⟩ | hce₁
                · let D₂ := M₂.toColoring
                  have he₁ : D₁.color e = .red :=
                    red_of_untouched_red_edge C hflip₁ (by simp [he]) (by simp [hf])
                      hef
                      (hv (x := (4 : Fin 10)) (y := 1) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 2) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 1) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 2) (by decide))
                  have hf₁ : D₁.color f = .red :=
                    red_of_untouched_red_edge C hflip₁ (by simp [hf]) (by simp [he])
                      hef.symm
                      (hv (x := (5 : Fin 10)) (y := 1) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 2) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 1) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 2) (by decide))
                  have he₂ : D₂.color e = .red :=
                    red_of_untouched_red_edge D₁ hflip₂ (by simp [he₁]) (by simp [hf₁])
                      hef
                      (hv (x := (4 : Fin 10)) (y := 8) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 7) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 8) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 7) (by decide))
                  have hf₂ : D₂.color f = .red :=
                    red_of_untouched_red_edge D₁ hflip₂ (by simp [hf₁]) (by simp [he₁])
                      hef.symm
                      (hv (x := (5 : Fin 10)) (y := 8) (by decide))
                      (hv (x := (5 : Fin 10)) (y := 7) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 8) (by decide))
                      (hv (x := (4 : Fin 10)) (y := 7) (by decide))
                  have hd₁ : D₁.color d = .bluish :=
                    bluish_of_blue_loses_flipped_mate C hflip₁ hd hcd.symm
                      (by simpa using nonedge 3 1 (by native_decide))
                      (hv (x := (3 : Fin 10)) (y := 1) (by decide))
                      hcd.ne.symm
                  have hd₂ : D₂.color d = .bluish :=
                    bluish_of_untouched_bluish D₁ hflip₂ hd₁
                      (by simpa using nonedge 3 8 (by native_decide))
                      (hv (x := (3 : Fin 10)) (y := 8) (by decide))
                      (hv (x := (3 : Fin 10)) (y := 7) (by decide))
                  have hk₁ : D₁.color k = .bluish :=
                    bluish_of_untouched_bluish C hflip₁ hk hkb
                      (vertex_ne_of_color_eq hk hb (by decide))
                      (vertex_ne_of_color_eq hk hc (by decide))
                  have hk₂ : D₂.color k = .bluish :=
                    bluish_of_untouched_bluish D₁ hflip₂ hk₁ hki
                      (vertex_ne_of_color_eq hk hi (by decide))
                      (vertex_ne_of_color_eq hk hh (by decide))
                  have hg₂ : D₂.color g = .bluish :=
                    bluish_of_blue_loses_flipped_mate D₁ hflip₂ hg₁ hgh
                      (by simpa using nonedge 6 8 (by native_decide))
                      (hv (x := (6 : Fin 10)) (y := 8) (by decide))
                      hgh.ne
                  have hl₁ : D₁.color l = .bluish :=
                    bluish_of_untouched_bluish C hflip₁ hl hlb
                      (vertex_ne_of_color_eq hl hb (by decide))
                      (vertex_ne_of_color_eq hl hc (by decide))
                  have hl₂ : D₂.color l = .bluish :=
                    bluish_of_untouched_bluish D₁ hflip₂ hl₁ hli
                      (vertex_ne_of_color_eq hl hi (by decide))
                      (vertex_ne_of_color_eq hl hh (by decide))
                  have hdone := lemma5_4 D₂ he₂ hf₂ hef
                      (by
                        intro z hez hzf
                        rcases C.neighbor_eq_of_three_neighbors (Or.inl he)
                            hef hde.symm hek hdf.symm hkf.symm hkd.symm hez with
                          rfl | rfl | rfl
                        · exact (hzf rfl).elim
                        · exact hd₂
                        · exact hk₂)
                      (by
                        intro z hfz hze
                        rcases C.neighbor_eq_of_three_neighbors (Or.inl hf)
                            hef.symm hfg hfl hegV hle.symm hlg.symm hfz with
                          rfl | rfl | rfl
                        · exact (hze rfl).elim
                        · exact hg₂
                        · exact hl₂)
                  exact HasReachableNegativeReduction.after_flip C hflip₁
                    (HasReachableNegativeReduction.after_flip D₁ hflip₂ hdone)
                · exact HasReachableNegativeReduction.after_flip C hflip₁
                    (HasReachableNegativeReduction.of_current_ce D₁ hce₁)
              · exact current_ce hce
        · exact current_ce hceFound
  · exact current_ce hceFound

end Subcubic
