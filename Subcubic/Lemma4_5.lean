import Subcubic.Lemma4_4
import Subcubic.FlipLemmas
import Subcubic.PositiveReduction
import Mathlib.Tactic.FinCases

/-!
# Lemma 4.5

The initial configuration is the induced path
`a-b-c-d-e-f-g-h-i-j`, with red edges `ab`, `ef`, `ij` and blue
edges `cd`, `gh`.  The proof flips the cut preservers `bc` and `ih` in
sequence; colors are recomputed after each valid matching-cut flip.
-/

namespace Subcubic

open Set
open scoped symmDiff

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The ten displayed vertices, in order, induce exactly a path. -/
def FormsInducedPath10 (G : SimpleGraph V)
    (a b c d e f g h i j : V) : Prop :=
  let p : Fin 10 → V := ![a, b, c, d, e, f, g, h, i, j]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
       (5, 6), (6, 7), (7, 8), (8, 9)]).Adj x y ↔ G.Adj (p x) (p y)

private theorem contains_cutEnhancerB
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .reddish) (hb : C.color b = .blue)
    (hc : C.color c = .red) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (hab : G.Adj a b) (had : G.Adj a d)
    (hbc : G.Adj b c) (hde : G.Adj d e)
    (hac : ¬ G.Adj a c) (hae : ¬ G.Adj a e)
    (hbd : ¬ G.Adj b d) (hbe : ¬ G.Adj b e)
    (hcd : ¬ G.Adj c d) (hce : ¬ G.Adj c e) :
    ContainsCutEnhancer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hab_ne := hab.ne
    have had_ne := had.ne
    have hbc_ne := hbc.ne
    have hde_ne := hde.ne
    have hac_ne : a ≠ c := by intro h; subst c; simp_all
    have hae_ne : a ≠ e := by intro h; subst e; simp_all
    have hbd_ne : b ≠ d := by intro h; subst d; simp_all
    have hbe_ne : b ≠ e := by intro h; subst e; simp_all
    have hcd_ne : c ≠ d := by intro h; subst d; simp_all
    have hce_ne : c ≠ e := by intro h; subst e; simp_all
    simp [hab_ne, hac_ne, had_ne, hae_ne, hbc_ne, hbd_ne, hbe_ne,
      hcd_ne, hce_ne, hde_ne]
  refine ⟨cutEnhancer .b, ⟨.b, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, by
    intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [cutEnhancer, graphOfEdges, G.adj_comm, hab, had, hbc, hde,
        hac, hae, hbd, hbe, hcd, hce]
  · intro x
    fin_cases x <;> simp [cutEnhancer, ha, hb, hc, hd, he]

private theorem contains_positiveC
    (C : GoodColoring G) {a b c d e : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .bluish)
    (hac : G.Adj a c) (hae : G.Adj a e)
    (hbd : G.Adj b d) (hbe : G.Adj b e) (hcd : G.Adj c d)
    (hab : ¬ G.Adj a b) (had : ¬ G.Adj a d)
    (hbc : ¬ G.Adj b c) :
    ContainsPositiveTailReducer C := by
  have hn : [a, b, c, d, e].Nodup := by
    have hae_ne := hae.ne
    have hbe_ne := hbe.ne
    have hac_ne := hac.ne
    have hbd_ne := hbd.ne
    have hcd_ne := hcd.ne
    have hab : a ≠ b := by intro h; subst b; simp_all
    have had : a ≠ d := by intro h; subst d; simp_all
    have hbc : b ≠ c := by intro h; subst c; simp_all
    have hce : c ≠ e := by intro h; subst e; simp_all
    have hde : d ≠ e := by intro h; subst e; simp_all
    simp [hab, hac_ne, had, hae_ne, hbc, hbd_ne, hbe_ne, hcd_ne, hce, hde]
  have hce : ¬ G.Adj c e := fun h =>
    C.bluish_not_adj_blueSide he (Or.inl hc) h.symm
  have hde : ¬ G.Adj d e := fun h =>
    C.bluish_not_adj_blueSide he (Or.inl hd) h.symm
  refine ⟨positiveTailReducer .c, ⟨.c, rfl⟩, Or.inl ?_⟩
  refine ⟨[a, b, c, d, e].get, hn.injective_get, ?_, ?_, by
    intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
  · intro x y
    fin_cases x <;> fin_cases y <;>
      simp [positiveTailReducer, positiveTailReducerData, PatternData.toPattern,
        graphOfEdges, G.adj_comm, hac, hae, hbd, hbe, hcd,
        hab, had, hbc, hce, hde]
  · intro x
    have hcolors : (positiveTailReducer .c).color =
        ![.red, .red, .blue, .blue, .bluish] := by native_decide
    rw [hcolors]
    fin_cases x <;> simp [ha, hb, hc, hd, he] <;> native_decide

/-- **Lemma 4.5.** In the displayed alternating five-edge configuration,
the original coloring or a coloring reached by sequential cut-preserver
flips contains a positive tail reducer or a cut enhancer. -/
theorem lemma4_5
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (hpath : FormsInducedPath10 G a b c d e f g h i j)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .red) (hj : C.color j = .red) :
    ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
      (ContainsPositiveTailReducer M.toGoodColoring ∨
       ContainsCutEnhancer M.toGoodColoring) := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degreeC {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath10] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have path_vertices_ne {x y : Fin 10} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h, i, j] x) ≠
        (![a, b, c, d, e, f, g, h, i, j] y) :=
    hinj.ne hxy
  have hab : G.Adj a b := by
    apply (hedge 0 1).mp
    native_decide
  have hbc : G.Adj b c := by
    apply (hedge 1 2).mp
    native_decide
  have hcd : G.Adj c d := by
    apply (hedge 2 3).mp
    native_decide
  have hde : G.Adj d e := by
    apply (hedge 3 4).mp
    native_decide
  have hef : G.Adj e f := by
    apply (hedge 4 5).mp
    native_decide
  have hfg : G.Adj f g := by
    apply (hedge 5 6).mp
    native_decide
  have hgh : G.Adj g h := by
    apply (hedge 6 7).mp
    native_decide
  have hhi : G.Adj h i := by
    apply (hedge 7 8).mp
    native_decide
  have hij : G.Adj i j := by
    apply (hedge 8 9).mp
    native_decide
  have path_nonedge (x y : Fin 10)
      (hxy : ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
         (5, 6), (6, 7), (7, 8), (8, 9)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h, i, j] x)
        (![a, b, c, d, e, f, g, h, i, j] y) := by
    intro h
    exact hxy ((hedge x y).mpr h)
  have finish_ptr (hptr : ContainsPositiveTailReducer C) :
      ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
        (ContainsPositiveTailReducer M.toGoodColoring ∨
         ContainsCutEnhancer M.toGoodColoring) := by
    refine ⟨C.toMatchingCut, .refl, Or.inl ?_⟩
    exact (containsInducedUpToSwap_congr_color IsPositiveTailReducer
      (by simp)).1 hptr
  have finish_ce (hce : ContainsCutEnhancer C) :
      ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
        (ContainsPositiveTailReducer M.toGoodColoring ∨
         ContainsCutEnhancer M.toGoodColoring) := by
    refine ⟨C.toMatchingCut, .refl, Or.inr ?_⟩
    exact (containsInducedUpToSwap_congr_color IsCutEnhancer
      (by simp)).1 hce
  have hdf : d ≠ f := by
    intro h
    have hidx : (3 : Fin 10) = 5 := hinj (by simpa using h)
    exact (by decide : (3 : Fin 10) ≠ 5) hidx
  obtain ⟨k, hek, hkd, hkf⟩ :=
    C.exists_third_neighbor (degreeC (Or.inl he)) hdf
  have hkside : C.color k = .blue ∨ C.color k = .bluish :=
    C.other_neighbor_of_red_is_blueSide he hf hef hek hkf
  have hec : ¬ G.Adj e c := by
    intro hec
    exact (by native_decide :
      ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
         (5, 6), (6, 7), (7, 8), (8, 9)]).Adj (4 : Fin 10) 2)
      ((hedge 4 2).mpr hec)
  have hkc : k ≠ c := by
    intro h
    subst k
    exact hec hek
  rcases lemma3_3 C he hd hc hkside hde.symm hek hcd.symm
      hkd.symm hkc.symm with hk | hce
  · have hbe : ¬ G.Adj b e := by
      simpa using path_nonedge 1 4 (by native_decide)
    have hbd : ¬ G.Adj b d := by
      simpa using path_nonedge 1 3 (by native_decide)
    have hec' : ¬ G.Adj e c := by
      simpa using path_nonedge 4 2 (by native_decide)
    by_cases hkb : G.Adj k b
    · exact finish_ptr (contains_positiveC C hb he hc hd hk
        hbc hkb.symm hde.symm hek hcd hbe hbd hec')
    · by_cases hki : G.Adj k i
      · have hkd_nonedge : ¬ G.Adj k d :=
          C.bluish_not_adj_blueSide hk (Or.inl hd)
        have hkh_nonedge : ¬ G.Adj k h :=
          C.bluish_not_adj_blueSide hk (Or.inl hh)
        have hei : ¬ G.Adj e i := by
          simpa using path_nonedge 4 8 (by native_decide)
        have heh : ¬ G.Adj e h := by
          simpa using path_nonedge 4 7 (by native_decide)
        have hdi : ¬ G.Adj d i := by
          simpa using path_nonedge 3 8 (by native_decide)
        have hdh : ¬ G.Adj d h := by
          simpa using path_nonedge 3 7 (by native_decide)
        have hceSwap := contains_cutEnhancerB C.swapSides
          (by simp [hk]) (by simp [he]) (by simp [hd])
          (by simp [hi]) (by simp [hh]) hek.symm hki hde.symm hhi.symm
          hkd_nonedge hkh_nonedge hei heh hdi hdh
        exact finish_ce
          ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
      · have heg : e ≠ g := by
          intro h
          have hidx : (4 : Fin 10) = 6 := hinj (by simpa using h)
          exact (by decide : (4 : Fin 10) ≠ 6) hidx
        obtain ⟨l, hfl, hle, hlg⟩ :=
          C.exists_third_neighbor (degreeC (Or.inl hf)) heg
        have hlside : C.color l = .blue ∨ C.color l = .bluish :=
          C.other_neighbor_of_red_is_blueSide hf he hef.symm hfl hle
        have hfh : ¬ G.Adj f h := by
          simpa using path_nonedge 5 7 (by native_decide)
        have hlh : l ≠ h := by
          intro h
          subst l
          exact hfh hfl
        rcases lemma3_3 C hf hg hh hlside hfg hfl hgh
            hlg.symm hlh.symm with hl | hce
        · have hif : ¬ G.Adj i f := by
            simpa using path_nonedge 8 5 (by native_decide)
          have hig : ¬ G.Adj i g := by
            simpa using path_nonedge 8 6 (by native_decide)
          by_cases hli : G.Adj l i
          · exact finish_ptr (contains_positiveC C hi hf hh hg hl
              hhi.symm hli.symm hfg hfl hgh.symm hif hig hfh)
          · by_cases hlb : G.Adj l b
            · have hlg_nonedge : ¬ G.Adj l g :=
                C.bluish_not_adj_blueSide hl (Or.inl hg)
              have hlc_nonedge : ¬ G.Adj l c :=
                C.bluish_not_adj_blueSide hl (Or.inl hc)
              have hfb : ¬ G.Adj f b := by
                simpa using path_nonedge 5 1 (by native_decide)
              have hfc : ¬ G.Adj f c := by
                simpa using path_nonedge 5 2 (by native_decide)
              have hgb : ¬ G.Adj g b := by
                simpa using path_nonedge 6 1 (by native_decide)
              have hgc : ¬ G.Adj g c := by
                simpa using path_nonedge 6 2 (by native_decide)
              have hceSwap := contains_cutEnhancerB C.swapSides
                (by simp [hl]) (by simp [hf]) (by simp [hg])
                (by simp [hb]) (by simp [hc]) hfl.symm hlb hfg hbc
                hlg_nonedge hlc_nonedge hfb hfc hgb hgc
              exact finish_ce
                ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
            · have hac_vertices : a ≠ c := by
                intro h
                have hidx : (0 : Fin 10) = 2 := hinj (by simpa using h)
                exact (by decide : (0 : Fin 10) ≠ 2) hidx
              obtain ⟨x, hbx, hxa, hxc⟩ :=
                C.exists_third_neighbor (degreeC (Or.inl hb)) hac_vertices
              have hxside :=
                C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbx hxa
              have hbd_path : ¬ G.Adj b d := by
                simpa using path_nonedge 1 3 (by native_decide)
              have hxd : x ≠ d := by
                intro h
                subst x
                exact hbd_path hbx
              rcases lemma3_3 C hb hc hd hxside hbc hbx hcd
                  hxc.symm hxd.symm with hx | hce
              ·
                have hbd_vertices : b ≠ d := by
                  intro h'
                  have hidx : (1 : Fin 10) = 3 := hinj (by simpa using h')
                  exact (by decide : (1 : Fin 10) ≠ 3) hidx
                obtain ⟨u, hcu, hub, hud⟩ :=
                  C.exists_third_neighbor (degreeC (Or.inr hc)) hbd_vertices
                have huside :=
                  C.other_neighbor_of_blue_is_redSide hc hd hcd hcu hud
                have hca_path : ¬ G.Adj c a := by
                  simpa using path_nonedge 2 0 (by native_decide)
                have hua : u ≠ a := by
                  intro h'; subst u; exact hca_path hcu
                rcases lemma3_3_reversed C hc hb ha huside hbc.symm hcu
                    hab.symm hub.symm hua.symm with hu | hce
                · obtain ⟨M₁, hflip₁⟩ := exists_flipAt_of_local C
                    hb hc ha hd (Or.inl hx) (Or.inl hu) hab.symm hbc hbx hcd hcu
                  let D₁ := M₁.toGoodColoring
                  have hside₁ : M₁.side = C.redSide ∆ ({b, c} : Set V) :=
                    hflip₁.2
                  have hib : i ≠ b := by
                    simpa using path_vertices_ne (x := (8 : Fin 10)) (y := 1) (by decide)
                  have hic : i ≠ c := by
                    simpa using path_vertices_ne (x := (8 : Fin 10)) (y := 2) (by decide)
                  have hjb : j ≠ b := by
                    simpa using path_vertices_ne (x := (9 : Fin 10)) (y := 1) (by decide)
                  have hjc : j ≠ c := by
                    simpa using path_vertices_ne (x := (9 : Fin 10)) (y := 2) (by decide)
                  have hhb : h ≠ b := by
                    simpa using path_vertices_ne (x := (7 : Fin 10)) (y := 1) (by decide)
                  have hhc : h ≠ c := by
                    simpa using path_vertices_ne (x := (7 : Fin 10)) (y := 2) (by decide)
                  have hgb : g ≠ b := by
                    simpa using path_vertices_ne (x := (6 : Fin 10)) (y := 1) (by decide)
                  have hgc : g ≠ c := by
                    simpa using path_vertices_ne (x := (6 : Fin 10)) (y := 2) (by decide)
                  have hiM₁ : i ∈ M₁.side := by
                    rw [hside₁]
                    simp [Set.mem_symmDiff, C.mem_redSide_iff, hi, hib, hic]
                  have hjM₁ : j ∈ M₁.side := by
                    rw [hside₁]
                    simp [Set.mem_symmDiff, C.mem_redSide_iff, hj, hjb, hjc]
                  have hhM₁ : h ∉ M₁.side := by
                    rw [hside₁]
                    simp [Set.mem_symmDiff, hh, hhb, hhc]
                  have hgM₁ : g ∉ M₁.side := by
                    rw [hside₁]
                    simp [Set.mem_symmDiff, hg, hgb, hgc]
                  have hi₁ : D₁.color i = .red := by
                    change colorOfCut G M₁.side i = .red
                    exact (colorOfCut_eq_red_iff G M₁.side i).2
                      ⟨hiM₁, j, hjM₁, hij⟩
                  have hj₁ : D₁.color j = .red := by
                    change colorOfCut G M₁.side j = .red
                    exact (colorOfCut_eq_red_iff G M₁.side j).2
                      ⟨hjM₁, i, hiM₁, hij.symm⟩
                  have hh₁ : D₁.color h = .blue := by
                    change colorOfCut G M₁.side h = .blue
                    exact (colorOfCut_eq_blue_iff G M₁.side h).2
                      ⟨hhM₁, g, hgM₁, hgh.symm⟩
                  have hg₁ : D₁.color g = .blue := by
                    change colorOfCut G M₁.side g = .blue
                    exact (colorOfCut_eq_blue_iff G M₁.side g).2
                      ⟨hgM₁, h, hhM₁, hgh⟩
                  have finish₁_ce (hce₁ : ContainsCutEnhancer D₁) :
                      ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
                        (ContainsPositiveTailReducer M.toGoodColoring ∨
                         ContainsCutEnhancer M.toGoodColoring) := by
                    exact ⟨M₁, .step .refl hflip₁, Or.inr hce₁⟩
                  have degreeD₁ {z : V}
                      (hz : D₁.color z = .red ∨ D₁.color z = .blue) :
                      vertexDegree G z = 3 := by
                    rcases lemma3_6_positive D₁ hz with hdegree | hptr | hce
                    · exact hdegree
                    · exact (hdone ⟨M₁, .step .refl hflip₁, Or.inl hptr⟩).elim
                    · exact (hdone ⟨M₁, .step .refl hflip₁, Or.inr hce⟩).elim
                  have hhj_vertices : h ≠ j := by
                    intro h'
                    have hidx : (7 : Fin 10) = 9 := hinj (by simpa using h')
                    exact (by decide : (7 : Fin 10) ≠ 9) hidx
                  obtain ⟨y, hiy, hyh, hyj⟩ :=
                    D₁.exists_third_neighbor (degreeD₁ (Or.inl hi₁)) hhj_vertices
                  have hyside :=
                    D₁.other_neighbor_of_red_is_blueSide hi₁ hj₁ hij hiy hyj
                  have hig_path : ¬ G.Adj i g := by
                    simpa using path_nonedge 8 6 (by native_decide)
                  have hyg : y ≠ g := by
                    intro h'; subst y; exact hig_path hiy
                  rcases lemma3_3 D₁ hi₁ hh₁ hg₁ hyside hhi.symm hiy
                      hgh.symm hyh.symm hyg.symm with hy | hce₁
                  · have hig_vertices : i ≠ g := by
                      intro h'
                      have hidx : (8 : Fin 10) = 6 := hinj (by simpa using h')
                      exact (by decide : (8 : Fin 10) ≠ 6) hidx
                    obtain ⟨v, hhv, hvi, hvg⟩ :=
                      D₁.exists_third_neighbor (degreeD₁ (Or.inr hh₁)) hig_vertices
                    have hvside :=
                      D₁.other_neighbor_of_blue_is_redSide hh₁ hg₁
                        hgh.symm hhv hvg
                    have hhj_path : ¬ G.Adj h j := by
                      simpa using path_nonedge 7 9 (by native_decide)
                    have hvj : v ≠ j := by
                      intro h'; subst v; exact hhj_path hhv
                    rcases lemma3_3_reversed D₁ hh₁ hi₁ hj₁ hvside hhi hhv
                        hij hvi.symm hvj.symm with hv | hce₁
                    · obtain ⟨M₂, hflip₂⟩ := exists_flipAt_of_local D₁
                        hi₁ hh₁ hj₁ hg₁ (Or.inl hy) (Or.inl hv)
                        hij hhi.symm hiy hgh.symm hhv
                      let D₂ := M₂.toGoodColoring
                      have hflip₂' : M₁.IsFlipAt M₂ i h := by
                        constructor
                        · exact ⟨hhi.symm, by simpa [D₁] using hi₁,
                            by simpa [D₁] using hh₁⟩
                        · simpa [D₁, GoodColoring.redSide,
                            MatchingCut.redSideOf_color] using hflip₂.2
                      have hside₂ : M₂.side = M₁.side ∆ ({i, h} : Set V) :=
                        hflip₂'.2
                      have heb : e ≠ b := by
                        simpa using path_vertices_ne (x := (4 : Fin 10)) (y := 1)
                          (by decide)
                      have hecV : e ≠ c := by
                        simpa using path_vertices_ne (x := (4 : Fin 10)) (y := 2)
                          (by decide)
                      have hei : e ≠ i := by
                        simpa using path_vertices_ne (x := (4 : Fin 10)) (y := 8)
                          (by decide)
                      have heh : e ≠ h := by
                        simpa using path_vertices_ne (x := (4 : Fin 10)) (y := 7)
                          (by decide)
                      have hfbV : f ≠ b := by
                        simpa using path_vertices_ne (x := (5 : Fin 10)) (y := 1)
                          (by decide)
                      have hfcV : f ≠ c := by
                        simpa using path_vertices_ne (x := (5 : Fin 10)) (y := 2)
                          (by decide)
                      have hfi : f ≠ i := by
                        simpa using path_vertices_ne (x := (5 : Fin 10)) (y := 8)
                          (by decide)
                      have hfhV : f ≠ h := by
                        simpa using path_vertices_ne (x := (5 : Fin 10)) (y := 7)
                          (by decide)
                      have heM₂ : e ∈ M₂.side := by
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, C.mem_redSide_iff, he,
                          heb, hecV, hei, heh]
                      have hfM₂ : f ∈ M₂.side := by
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, C.mem_redSide_iff, hf,
                          hfbV, hfcV, hfi, hfhV]
                      have he₂ : D₂.color e = .red := by
                        change colorOfCut G M₂.side e = .red
                        exact (colorOfCut_eq_red_iff G M₂.side e).2
                          ⟨heM₂, f, hfM₂, hef⟩
                      have hf₂ : D₂.color f = .red := by
                        change colorOfCut G M₂.side f = .red
                        exact (colorOfCut_eq_red_iff G M₂.side f).2
                          ⟨hfM₂, e, heM₂, hef.symm⟩
                      have final_mem_of_old {z : V} (hz : z ∈ C.redSide)
                          (hzb : z ≠ b) (hzi : z ≠ i) : z ∈ M₂.side := by
                        have hzc : z ≠ c := by
                          intro h'; subst z; simp [hc] at hz
                        have hzh : z ≠ h := by
                          intro h'; subst z; simp [hh] at hz
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hz, hzb, hzi, hzc, hzh]
                      have not_final_implies_old_blue {z : V} (hz : z ∉ M₂.side)
                          (hzb : z ≠ b) (hzi : z ≠ i) : z ∉ C.redSide := by
                        intro hzold
                        exact hz (final_mem_of_old hzold hzb hzi)
                      have hdM₂ : d ∉ M₂.side := by
                        have hdb : d ≠ b := by
                          simpa using path_vertices_ne (x := (3 : Fin 10)) (y := 1)
                            (by decide)
                        have hdc : d ≠ c := hcd.ne.symm
                        have hdi : d ≠ i := by
                          simpa using path_vertices_ne (x := (3 : Fin 10)) (y := 8)
                            (by decide)
                        have hdh : d ≠ h := by
                          simpa using path_vertices_ne (x := (3 : Fin 10)) (y := 7)
                            (by decide)
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hd, hdb, hdc, hdi, hdh]
                      have hgM₂ : g ∉ M₂.side := by
                        have hgi : g ≠ i := by
                          simpa using path_vertices_ne (x := (6 : Fin 10)) (y := 8)
                            (by decide)
                        have hghV : g ≠ h := hgh.ne
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hg, hgb, hgc, hgi, hghV]
                      have hkM₂ : k ∉ M₂.side := by
                        have hkbV : k ≠ b := by intro h'; subst k; simp_all
                        have hkiV : k ≠ i := by intro h'; subst k; simp_all
                        have hkhV : k ≠ h := by intro h'; subst k; simp_all
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hk, hkbV, hkc, hkiV, hkhV]
                      have hlM₂ : l ∉ M₂.side := by
                        have hlbV : l ≠ b := by intro h'; subst l; simp_all
                        have hlcV : l ≠ c := by intro h'; subst l; simp_all
                        have hliV : l ≠ i := by intro h'; subst l; simp_all
                        have hlhV : l ≠ h := by intro h'; subst l; simp_all
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hl, hlbV, hlcV, hliV, hlhV]
                      have hcM₂ : c ∈ M₂.side := by
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hc, hbc.ne.symm, hic.symm, hhc.symm]
                      have hhM₂ : h ∈ M₂.side := by
                        rw [hside₂, hside₁]
                        simp [Set.mem_symmDiff, hh, hhb, hhc, hhi.ne]
                      have hd₂ : D₂.color d = .bluish := by
                        change colorOfCut G M₂.side d = .bluish
                        apply (colorOfCut_eq_bluish_iff G M₂.side d).2
                        refine ⟨hdM₂, ?_⟩
                        rintro ⟨z, hz, hdz⟩
                        by_cases hzb : z = b
                        · subst z; exact hbd_path hdz.symm
                        by_cases hzi : z = i
                        · subst z
                          exact (path_nonedge 3 8 (by native_decide)) hdz
                        have hzside := C.other_neighbor_of_blue_is_redSide
                          hd hc hcd.symm hdz (by
                            intro h'; subst z; exact hz hcM₂ |> False.elim)
                        exact hz (final_mem_of_old
                          ((C.mem_redSide_iff z).2 hzside) hzb hzi)
                      have hg₂ : D₂.color g = .bluish := by
                        change colorOfCut G M₂.side g = .bluish
                        apply (colorOfCut_eq_bluish_iff G M₂.side g).2
                        refine ⟨hgM₂, ?_⟩
                        rintro ⟨z, hz, hgz⟩
                        by_cases hzb : z = b
                        · subst z
                          exact (path_nonedge 6 1 (by native_decide)) hgz
                        by_cases hzi : z = i
                        · subst z
                          exact (path_nonedge 6 8 (by native_decide)) hgz
                        have hzside := C.other_neighbor_of_blue_is_redSide
                          hg hh hgh hgz (by
                            intro h'; subst z; exact hz hhM₂ |> False.elim)
                        exact hz (final_mem_of_old
                          ((C.mem_redSide_iff z).2 hzside) hzb hzi)
                      have hk₂ : D₂.color k = .bluish := by
                        change colorOfCut G M₂.side k = .bluish
                        apply (colorOfCut_eq_bluish_iff G M₂.side k).2
                        refine ⟨hkM₂, ?_⟩
                        rintro ⟨z, hz, hkz⟩
                        by_cases hzb : z = b
                        · subst z; exact hkb hkz
                        by_cases hzi : z = i
                        · subst z; exact hki hkz
                        have hcorrect := C.color_correct k
                        rw [hk] at hcorrect
                        exact hcorrect.2
                          ⟨z, not_final_implies_old_blue hz hzb hzi, hkz⟩
                      have hl₂ : D₂.color l = .bluish := by
                        change colorOfCut G M₂.side l = .bluish
                        apply (colorOfCut_eq_bluish_iff G M₂.side l).2
                        refine ⟨hlM₂, ?_⟩
                        rintro ⟨z, hz, hlz⟩
                        by_cases hzb : z = b
                        · subst z; exact hlb hlz
                        by_cases hzi : z = i
                        · subst z; exact hli hlz
                        have hcorrect := C.color_correct l
                        rw [hl] at hcorrect
                        exact hcorrect.2
                          ⟨z, not_final_implies_old_blue hz hzb hzi, hlz⟩
                      have degreeD₂ {z : V}
                          (hz : D₂.color z = .red ∨ D₂.color z = .blue) :
                          vertexDegree G z = 3 := by
                        rcases lemma3_6_positive D₂ hz with hdegree | hptr | hce
                        · exact hdegree
                        · exact (hdone ⟨M₂, .step (.step .refl hflip₁) hflip₂',
                              Or.inl hptr⟩).elim
                        · exact (hdone ⟨M₂, .step (.step .refl hflip₁) hflip₂',
                              Or.inr hce⟩).elim
                      have hptr₂ : ContainsPositiveTailReducer D₂ :=
                        lemma4_4 D₂ he₂ hf₂ hef
                          (degreeD₂ (Or.inl he₂)) (degreeD₂ (Or.inl hf₂))
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
                                hef.symm hfg hfl heg hle.symm hlg.symm hfz with
                              rfl | rfl | rfl
                            · exact (hze rfl).elim
                            · exact hg₂
                            · exact hl₂)
                      exact ⟨M₂, .step (.step .refl hflip₁) hflip₂', Or.inl hptr₂⟩
                    · exact finish₁_ce hce₁
                  · exact finish₁_ce hce₁
                · exact finish_ce hce
              · exact finish_ce hce
        · exact finish_ce hce
  · exact finish_ce hce

end Subcubic
