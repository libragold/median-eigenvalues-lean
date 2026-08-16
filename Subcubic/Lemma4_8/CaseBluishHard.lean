import Subcubic.Lemma4_8.CaseBluish
import Subcubic.Lemma4_6

/-! # Final all-bluish branch of Lemma 4.8 -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_8NConfiguration (C : MatchingCutColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8BluishHardConfiguration C a b c d e f g h where
  n : V
  hn : C.color n = .red
  hln : G.Adj l n
  hna : n ≠ a
  hlf : ¬ G.Adj l f

/-- Case (3.4.3.1.3.2), using the corresponding corrected configuration. -/
theorem lemma4_8_case_l_adj_f
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8BluishHardConfiguration C a b c d e f g h)
    (hlf : G.Adj Q.l f) : HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  obtain ⟨n, hgn, hnf, hnh⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inr hg))
      (hv (u := (5 : Fin 8)) (v := 7) (by decide))
  have hnSide := C.other_neighbor_of_blue_is_redSide hg hh hgh hgn hnh
  have hen : e ≠ n := by
    intro hen
    subst n
    exact (nonedge 6 4 (by native_decide)) hgn
  rcases lemma3_3_reversed C hg hf he hnSide hfg.symm hgn hef.symm
      hnf.symm hen with hn | hce
  · have hlc : ¬ G.Adj Q.l c :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hc)
    have hlg : ¬ G.Adj Q.l g :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hg)
    have hlb : ¬ G.Adj Q.l b := by
      simpa [SimpleGraph.adj_comm] using Q.hbl
    have hle : ¬ G.Adj Q.l e := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hkl.symm Q.hal.symm hlf
      · exact color_ne Q.hk ha (by decide)
      · exact color_ne Q.hk hf (by decide)
      · exact hv (u := (0 : Fin 8)) (v := 5) (by decide)
      · exact color_ne he Q.hk (by decide)
      · exact hv (u := (4 : Fin 8)) (v := 0) (by decide)
      · exact hv (u := (4 : Fin 8)) (v := 5) (by decide)
    have hnk : n ≠ Q.k := by
      intro h
      subst n
      exact Q.hkg hgn.symm
    have hln : ¬ G.Adj Q.l n := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hkl.symm Q.hal.symm hlf
      · exact color_ne Q.hk ha (by decide)
      · exact color_ne Q.hk hf (by decide)
      · exact hv (u := (0 : Fin 8)) (v := 5) (by decide)
      · exact hnk
      · exact color_ne hn ha (by decide)
      · exact color_ne hn hf (by decide)
    have hcg : ¬ G.Adj c g :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hc]) (by simp [hd]) (by simp [hg]) hcd
        (hv (u := (3 : Fin 8)) (v := 6) (by decide))
    have hcn : ¬ G.Adj c n := by
      apply C.not_adj_fourth_neighbor (Or.inr hc) hcd Q.hck hbc.symm
      · exact Q.hkd.symm
      · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
      · exact Q.hkb
      · exact color_ne hn hd (by decide)
      · exact hnk
      · exact color_ne hn hb (by decide)
    have hptrSwap := containsPositiveR C.swapSides
      (a := Q.l) (b := c) (c := g) (d := Q.k)
      (e := a) (f := b) (g := f) (h := e) (i := n)
      (by simp [Q.hl]) (by simp [hc]) (by simp [hg]) (by simp [Q.hk])
      (by simp [ha]) (by simp [hb]) (by simp [hf]) (by simp [he])
      (by simp [hn]) Q.hkl.symm Q.hal.symm hlf Q.hck hbc.symm
      hfg.symm hgn hab hef.symm hlc hlg hlb hle hln hcg
      (by simpa using nonedge 2 0 (by native_decide))
      (by simpa using nonedge 2 4 (by native_decide)) hcn
      (by simpa [SimpleGraph.adj_comm] using Q.hkg)
      (by simpa using nonedge 6 0 (by native_decide))
      (by simpa using nonedge 6 1 (by native_decide))
      (by simpa using nonedge 6 4 (by native_decide))
      (by
        simp [color_ne Q.hl hc (by decide), color_ne Q.hl hg (by decide),
          color_ne Q.hl Q.hk (by decide), color_ne Q.hl ha (by decide),
          color_ne Q.hl hb (by decide), color_ne Q.hl hf (by decide),
          color_ne Q.hl he (by decide), color_ne Q.hl hn (by decide),
          color_ne hc Q.hk (by decide), color_ne hc ha (by decide),
          color_ne hc hb (by decide), color_ne hc hf (by decide),
          color_ne hc he (by decide), color_ne hc hn (by decide),
          color_ne hg Q.hk (by decide), color_ne hg ha (by decide),
          color_ne hg hb (by decide), color_ne hg hf (by decide),
          color_ne hg he (by decide), color_ne hg hn (by decide),
          color_ne Q.hk ha (by decide), color_ne Q.hk hb (by decide),
          color_ne Q.hk hf (by decide), color_ne Q.hk he (by decide),
          color_ne ha hn (by decide), color_ne hb hn (by decide),
          color_ne hf hn (by decide), color_ne he hn (by decide)]
        exact ⟨hv (u := (2 : Fin 8)) (v := 6) (by decide), hnk.symm,
          ⟨hv (u := (0 : Fin 8)) (v := 1) (by decide),
            hv (u := (0 : Fin 8)) (v := 5) (by decide),
            hv (u := (0 : Fin 8)) (v := 4) (by decide)⟩,
          ⟨hv (u := (1 : Fin 8)) (v := 5) (by decide),
            hv (u := (1 : Fin 8)) (v := 4) (by decide)⟩,
          hv (u := (5 : Fin 8)) (v := 4) (by decide)⟩)
    exact HasReachableReduction.of_current_ptr C
      ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptrSwap)
  · exact HasReachableReduction.of_current_ce C hce

theorem lemma4_8_bluish_hard_setup
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8BluishHardConfiguration C a b c d e f g h) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8NConfiguration C a b c d e f g h) := by
  classical
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hca : ¬ G.Adj c a := by simpa using nonedge 2 0 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  by_cases hother : ∃ n, G.Adj Q.l n ∧ C.color n = .red ∧ n ≠ a
  · obtain ⟨n, hln, hn, hna⟩ := hother
    by_cases hlf : G.Adj Q.l f
    · exact Or.inl (lemma4_8_case_l_adj_f C hp ha hb hc hd he hf hg hh Q hlf)
    · exact Or.inr ⟨⟨Q, n, hn, hln, hna, hlf⟩⟩
  · have hother' : ∀ n, G.Adj Q.l n → C.color n = .red → n = a := by
      intro n hln hn
      by_contra hna
      exact hother ⟨n, hln, hn, hna⟩
    have hlaV : Q.l ≠ a := Q.hal.ne.symm
    have hlkV : Q.l ≠ Q.k := Q.hkl.ne.symm
    have hkaV : Q.k ≠ a := color_ne Q.hk ha (by decide)
    have hlc : ¬ G.Adj Q.l c :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hc)
    have hlb : ¬ G.Adj Q.l b := by simpa [SimpleGraph.adj_comm] using Q.hbl
    by_cases hldeg2 : vertexDegree G Q.l = 2
    · have hptrSwap := containsPositiveDcA C.swapSides
        (a := Q.l) (b := c) (c := Q.k) (d := a) (e := b)
        (by simp [Q.hl]) (by simp [hc]) (by simp [Q.hk])
        (by simp [ha]) (by simp [hb]) hldeg2 Q.hkl.symm Q.hal.symm
        Q.hck hbc.symm hab hlc hlb hca
        (by
          simp [color_ne Q.hl hc (by decide), color_ne Q.hl Q.hk (by decide),
            color_ne Q.hl ha (by decide), color_ne Q.hl hb (by decide),
            color_ne hc Q.hk (by decide), color_ne hc ha (by decide),
            color_ne hc hb (by decide), color_ne Q.hk ha (by decide),
            color_ne Q.hk hb (by decide)]
          exact hv (u := (0 : Fin 8)) (v := 1) (by decide))
      exact Or.inl (HasReachableReduction.of_current_ptr C
        ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptrSwap))
    · have lower : 2 ≤ vertexDegree G Q.l := by
        have hsubset : ({Q.k, a} : Set V) ⊆ G.neighborSet Q.l := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · simpa using Q.hkl.symm
          · simpa using Q.hal.symm
        unfold vertexDegree
        simpa [hkaV] using Set.ncard_le_ncard hsubset
      have hldeg3 : vertexDegree G Q.l = 3 := by
        have upper := C.subcubic Q.l
        omega
      obtain ⟨x, y, hlx, hly, hxk, hyk, hxy⟩ :=
        exists_two_other_neighbors_of_degree_three hldeg3 Q.hkl.symm
      have choose : ∃ n, G.Adj Q.l n ∧ n ≠ Q.k ∧ n ≠ a := by
        by_cases hxa : x = a
        · exact ⟨y, hly, hyk, fun h => hxy (hxa.trans h.symm)⟩
        · exact ⟨x, hlx, hxk, hxa⟩
      obtain ⟨n, hln, hnk, hna⟩ := choose
      have hn : C.color n = .reddish := by
        cases hnc : C.color n with
        | red => exact (hna (hother' n hln hnc)).elim
        | reddish => exact rfl
        | blue => exact (C.bluish_not_adj_blueSide Q.hl (Or.inl hnc) hln).elim
        | bluish => exact (C.bluish_not_adj_blueSide Q.hl (Or.inr hnc) hln).elim
      have hcn : ¬ G.Adj c n := by
        apply C.not_adj_fourth_neighbor (Or.inr hc) hcd Q.hck hbc.symm
        · exact Q.hkd.symm
        · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
        · exact Q.hkb
        · exact color_ne hn hd (by decide)
        · exact hnk
        · exact color_ne hn hb (by decide)
      have hptrSwap := containsPositiveM C.swapSides
        (a := Q.l) (b := c) (c := n) (d := Q.k) (e := a) (f := b)
        (by simp [Q.hl]) (by simp [hc]) (by simp [hn]) (by simp [Q.hk])
        (by simp [ha]) (by simp [hb]) hln Q.hkl.symm Q.hal.symm Q.hck hbc.symm hab
        hlc hlb hcn hca
        (by
          simp [color_ne Q.hl hc (by decide), color_ne Q.hl hn (by decide),
            color_ne Q.hl Q.hk (by decide), color_ne Q.hl ha (by decide),
            color_ne Q.hl hb (by decide), color_ne hc hn (by decide),
            color_ne hc Q.hk (by decide), color_ne hc ha (by decide),
            color_ne hc hb (by decide), hnk,
            color_ne hn ha (by decide), color_ne hn hb (by decide),
            color_ne Q.hk ha (by decide), color_ne Q.hk hb (by decide)]
          exact hv (u := (0 : Fin 8)) (v := 1) (by decide))
      exact Or.inl (HasReachableReduction.of_current_ptr C
        ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptrSwap))

/-- Case (3.4.3.1.3.3.2): the additional red neighbor of `l` has no blue
neighbor. -/
theorem lemma4_8_n_no_blue
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (_hf : C.color f = .red)
    (Q : Lemma4_8NConfiguration C a b c d e f g h)
    (hNoBlue : ∀ z, G.Adj Q.n z → C.color z ≠ .blue) :
    HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  have hnCorrect := C.color_correct Q.n
  rw [Q.hn] at hnCorrect
  obtain ⟨_, q, hqSide, hnq⟩ := hnCorrect
  have hqSide' := (C.mem_redSide_iff q).1 hqSide
  have hq : C.color q = .red := by
    rcases hqSide' with hq | hq
    · exact hq
    · exact (C.reddish_not_adj_redSide hq (Or.inl Q.hn) hnq.symm).elim
  have hql : q ≠ Q.l := color_ne hq Q.hl (by decide)
  obtain ⟨o, hno, hoq, hol⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inl Q.hn)) hql
  have hoSide := C.other_neighbor_of_red_is_blueSide
    Q.hn hq hnq hno hoq
  have ho : C.color o = .bluish := by
    rcases hoSide with ho | ho
    · exact (hNoBlue o hno ho).elim
    · exact ho
  have hnb : Q.n ≠ b := by
    intro hnb
    apply Q.hbl
    simpa [hnb] using Q.hln.symm
  have hnf : Q.n ≠ f := by
    intro hnf
    apply Q.hlf
    simpa [hnf] using Q.hln
  have hne : Q.n ≠ e := by
    intro hne
    have hle : G.Adj Q.l e := by simpa [hne] using Q.hln
    have hlj : Q.l ≠ Q.j := by
      intro hlj
      exact Q.hkj (by simpa [hlj] using Q.hkl)
    have hld : Q.l ≠ d := color_ne Q.hl hd (by decide)
    have hlf : Q.l ≠ f := color_ne Q.hl _hf (by decide)
    exact (C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      (hv (u := (5 : Fin 8)) (v := 3) (by decide))
      (color_ne _hf Q.hj (by decide)) (color_ne hd Q.hj (by decide))
      hlf hld hlj) hle.symm
  have hnd : ¬ G.Adj Q.n d := by
    rw [SimpleGraph.adj_comm]
    apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
    · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
    · exact color_ne hc Q.hi (by decide)
    · exact color_ne he Q.hi (by decide)
    · exact color_ne Q.hn hc (by decide)
    · exact hne
    · exact color_ne Q.hn Q.hi (by decide)
  have hnaAdj : ¬ G.Adj Q.n a := by
    simpa [SimpleGraph.adj_comm] using C.redSide_not_adj_second_neighbor
      (by simp [ha]) (by simp [hb]) (by simp [Q.hn]) hab hnb.symm
  by_cases hnj : G.Adj Q.n Q.j
  · have hen : ¬ G.Adj e Q.n :=
      C.redSide_not_adj_second_neighbor
        (by simp [he]) (by simp [_hf]) (by simp [Q.hn]) hef hnf.symm
    have hea : ¬ G.Adj e a := by simpa using nonedge 4 0 (by native_decide)
    have hdj : ¬ G.Adj d Q.j :=
      C.bluish_not_adj_blueSide Q.hj (Or.inl hd) ∘ SimpleGraph.Adj.symm
    have hda : ¬ G.Adj d a := by simpa using nonedge 3 0 (by native_decide)
    exact HasReachableReduction.of_current_ce C
      (containsCutEnhancerC_of C he Q.hn hd Q.hj ha hde.symm Q.hej
        hnj Q.hja hen hea hnd hnaAdj hdj hda hne.symm
        (hv (u := (4 : Fin 8)) (v := 0) (by decide)) Q.hna)
  · have hao : ¬ G.Adj a o := by
      have hjl : Q.j ≠ Q.l := by
        intro hjl
        exact Q.hkj (by simpa [hjl] using Q.hkl)
      apply C.not_adj_fourth_neighbor (Or.inl ha) hab Q.hja.symm Q.hal
      · exact color_ne hb Q.hj (by decide)
      · exact color_ne hb Q.hl (by decide)
      · exact hjl
      · exact color_ne ho hb (by decide)
      · intro hoj
        subst o
        exact hnj hno
      · exact hol
    have han : ¬ G.Adj a Q.n := by simpa [SimpleGraph.adj_comm] using hnaAdj
    have hlj : Q.l ≠ Q.j := by
      intro hlj
      exact Q.hkj (by simpa [hlj] using Q.hkl)
    have hoj : o ≠ Q.j := by intro hoj; subst o; exact hnj hno
    have hnptr := containsPositiveG C ha Q.hn Q.hj Q.hl ho
      Q.hja.symm Q.hal Q.hln.symm hno han hao hnj
      (by
        simp [color_ne ha Q.hj (by decide),
          color_ne ha Q.hl (by decide), color_ne ha ho (by decide),
          color_ne Q.hn Q.hj (by decide), color_ne Q.hn Q.hl (by decide),
          color_ne Q.hn ho (by decide)]
        exact ⟨Q.hna.symm, ⟨hlj.symm, hoj.symm⟩, hol.symm⟩)
    exact HasReachableReduction.of_current_ptr C hnptr

/-- Case (3.4.3.1.3.3.1): flip a blue neighbor of `n` and invoke the
five-edge subgraph lemma. -/
theorem lemma4_8_n_has_blue
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8NConfiguration C a b c d e f g h)
    {o : V} (hno : G.Adj Q.n o) (ho : C.color o = .blue) :
    HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  have hnb : Q.n ≠ b := by
    intro hn
    apply Q.hbl
    simpa [hn] using Q.hln.symm
  have hnf : Q.n ≠ f := by
    intro hn
    apply Q.hlf
    simpa [hn] using Q.hln
  have hne : Q.n ≠ e := by
    intro hne
    have hlj : Q.l ≠ Q.j := by
      intro hlj
      exact Q.hkj (by simpa [hlj] using Q.hkl)
    have hle : G.Adj Q.l e := by simpa [hne] using Q.hln
    exact (C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      (hv (u := (5 : Fin 8)) (v := 3) (by decide))
      (color_ne hf Q.hj (by decide)) (color_ne hd Q.hj (by decide))
      (color_ne Q.hl hf (by decide)) (color_ne Q.hl hd (by decide)) hlj) hle.symm
  have hnd : ¬ G.Adj Q.n d := by
    rw [SimpleGraph.adj_comm]
    apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
    · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
    · exact color_ne hc Q.hi (by decide)
    · exact color_ne he Q.hi (by decide)
    · exact color_ne Q.hn hc (by decide)
    · exact hne
    · exact color_ne Q.hn Q.hi (by decide)
  have hen : ¬ G.Adj e Q.n :=
    C.redSide_not_adj_second_neighbor
      (by simp [he]) (by simp [hf]) (by simp [Q.hn]) hef hnf.symm
  by_cases hng : G.Adj Q.n g
  · have hfn : ¬ G.Adj f Q.n :=
      C.redSide_not_adj_second_neighbor
        (by simp [hf]) (by simp [he]) (by simp [Q.hn]) hef.symm hne.symm
    have hceSwap := containsCutEnhancerA_of C.swapSides
      (by simp [hg]) (by simp [hf]) (by simp [Q.hn]) hfg.symm hng.symm
      hnf.symm hfn
    exact HasReachableReduction.of_current_ce C
      ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
  · by_cases hnh : G.Adj Q.n h
    · have hie : ¬ G.Adj Q.i e :=
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
      have hin : ¬ G.Adj Q.i Q.n :=
        C.reddish_not_adj_redSide Q.hi (Or.inl Q.hn)
      have hdh : ¬ G.Adj d h :=
        C.blueSide_not_adj_second_neighbor
          (by simp [hd]) (by simp [hc]) (by simp [hh]) hcd.symm
          (hv (u := (2 : Fin 8)) (v := 7) (by decide))
      have heh : ¬ G.Adj e h := by simpa using nonedge 4 7 (by native_decide)
      exact HasReachableReduction.of_current_ce C
        (containsCutEnhancerB_of C Q.hi hd he hh Q.hn Q.hdi.symm Q.hih
          hde hnh.symm hie hin hdh
          (by simpa [SimpleGraph.adj_comm] using hnd) heh hen)
    · have hnCorrect := C.color_correct Q.n
      rw [Q.hn] at hnCorrect
      obtain ⟨_, q, hqSide, hnq⟩ := hnCorrect
      have hqSide' := (C.mem_redSide_iff q).1 hqSide
      have hq : C.color q = .red := by
        rcases hqSide' with hq | hq
        · exact hq
        · exact (C.reddish_not_adj_redSide hq (Or.inl Q.hn) hnq.symm).elim
      have hoCorrect := C.color_correct o
      rw [ho] at hoCorrect
      obtain ⟨_, p, hpSide, hop⟩ := hoCorrect
      have hpSide' := (C.not_mem_redSide_iff p).1 hpSide
      have hpColor : C.color p = .blue := by
        rcases hpSide' with hpColor | hpColor
        · exact hpColor
        · exact (C.bluish_not_adj_blueSide hpColor (Or.inl ho) hop.symm).elim
      by_cases hoqAdj : G.Adj o q
      · have hmulti : 2 ≤ fourVertexCrossEdgeCount G Q.n q o p := by
          unfold fourVertexCrossEdgeCount
          rw [if_pos hno, if_pos hoqAdj.symm]
          omega
        have hout := lemma4_2 C Q.n q o p
          hnq Q.hn hq hop ho hpColor hmulti
        exact hout.elim (HasReachableReduction.of_current_ptr C)
          (HasReachableReduction.of_current_ce C)
      · rcases exists_flipAt_or_cutEnhancer C Q.hn ho hq hpColor
          (degree_of_color (Or.inl Q.hn)) (degree_of_color (Or.inr ho))
          hnq hno hop with hflip | hce
        · obtain ⟨M, hflip⟩ := hflip
          let D := M.toColoring
          have hnD : D.color Q.n = .blue :=
            blue_of_flipped_red_endpoint C hflip hq hnq
              (degree_of_color (Or.inl Q.hn))
              (color_ne hq ho (by decide))
          have hlD : D.color Q.l = .blue :=
            blue_of_bluish_gains_flipped_red C hflip Q.hl Q.hln
              Q.hln.ne (color_ne Q.hl ho (by decide))
          have haD : D.color a = .red := by
            apply red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
            · exact Q.hna.symm
            · exact color_ne ha ho (by decide)
            · exact hnb.symm
            · exact color_ne hb ho (by decide)
          have hbD : D.color b = .red := by
            apply red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
            · exact hnb.symm
            · exact color_ne hb ho (by decide)
            · exact Q.hna.symm
            · exact color_ne ha ho (by decide)
          have hncAdj : ¬ G.Adj Q.n c := by
            rw [SimpleGraph.adj_comm]
            apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hck
            · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
            · exact Q.hkd.symm
            · exact Q.hkb.symm
            · exact color_ne Q.hn hd (by decide)
            · exact hnb
            · exact color_ne Q.hn Q.hk (by decide)
          have hnoC : o ≠ c := by intro hoc; subst o; exact hncAdj hno
          have hnoD : o ≠ d := by intro hod; subst o; exact hnd hno
          have hnoG : o ≠ g := by intro hog; subst o; exact hng hno
          have hnoH : o ≠ h := by intro hoh; subst o; exact hnh hno
          have hcD : D.color c = .blue := by
            apply blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
            · exact color_ne hc Q.hn (by decide)
            · exact hnoC.symm
            · exact color_ne hd Q.hn (by decide)
            · exact hnoD.symm
          have hdD : D.color d = .blue := by
            apply blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
            · exact color_ne hd Q.hn (by decide)
            · exact hnoD.symm
            · exact color_ne hc Q.hn (by decide)
            · exact hnoC.symm
          have heD : D.color e = .red := by
            apply red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
            · exact hne.symm
            · exact color_ne he ho (by decide)
            · exact hnf.symm
            · exact color_ne hf ho (by decide)
          have hfD : D.color f = .red := by
            apply red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
            · exact hnf.symm
            · exact color_ne hf ho (by decide)
            · exact hne.symm
            · exact color_ne he ho (by decide)
          have hgD : D.color g = .blue := by
            apply blue_of_untouched_blue_edge C hflip (by simp [hg]) (by simp [hh]) hgh
            · exact color_ne hg Q.hn (by decide)
            · exact hnoG.symm
            · exact color_ne hh Q.hn (by decide)
            · exact hnoH.symm
          have hhD : D.color h = .blue := by
            apply blue_of_untouched_blue_edge C hflip (by simp [hh]) (by simp [hg]) hgh.symm
            · exact color_ne hh Q.hn (by decide)
            · exact hnoH.symm
            · exact color_ne hg Q.hn (by decide)
            · exact hnoG.symm
          have pathNodup : [a, b, c, d, e, f, g, h].Nodup := by
            simpa using List.nodup_ofFn_ofInjective hinj
          have hlNotPath : Q.l ∉ [a, b, c, d, e, f, g, h] := by
            simp [color_ne Q.hl ha (by decide), color_ne Q.hl hb (by decide),
              color_ne Q.hl hc (by decide), color_ne Q.hl hd (by decide),
              color_ne Q.hl he (by decide), color_ne Q.hl hf (by decide),
              color_ne Q.hl hg (by decide), color_ne Q.hl hh (by decide)]
          have hnNotPath : Q.n ∉ [a, b, c, d, e, f, g, h] := by
            simp [Q.hna, hnb, color_ne Q.hn hc (by decide),
              color_ne Q.hn hd (by decide), hne, hnf,
              color_ne Q.hn hg (by decide), color_ne Q.hn hh (by decide)]
          have hnNodup : [Q.n, Q.l, a, b, c, d, e, f, g, h].Nodup := by
            apply List.nodup_cons.mpr
            constructor
            · intro hmem
              rcases List.mem_cons.mp hmem with hnl | hmem
              · exact Q.hln.ne hnl.symm
              · exact hnNotPath hmem
            · exact List.nodup_cons.mpr ⟨hlNotPath, pathNodup⟩
          have hsub : FormsPath10Subgraph G Q.n Q.l a b c d e f g h := by
            refine ⟨?_, ?_⟩
            · have hvec : (![Q.n, Q.l, a, b, c, d, e, f, g, h] : Fin 10 → V) =
                  [Q.n, Q.l, a, b, c, d, e, f, g, h].get := by
                funext x
                fin_cases x <;> rfl
              rw [hvec]
              exact hnNodup.injective_get
            · intro x y hxy
              fin_cases x <;> fin_cases y <;>
                simp [graphOfEdges, SimpleGraph.adj_comm] at hxy ⊢
              all_goals first
                | exact Q.hln.symm
                | exact Q.hal
                | assumption
          have hout := lemma4_6 D.swapSides hsub
            (by simp [hnD]) (by simp [hlD])
            (by simp [haD]) (by simp [hbD])
            (by simp [hcD]) (by simp [hdD])
            (by simp [heD]) (by simp [hfD])
            (by simp [hgD]) (by simp [hhD])
          exact HasReachableReduction.after_flip C hflip
            (HasReachableReduction.of_swapSides D hout)
        · exact HasReachableReduction.of_current_ce C hce

theorem lemma4_8_n_cases
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8NConfiguration C a b c d e f g h) :
    HasReachableReduction C := by
  by_cases hblue : ∃ o, G.Adj Q.n o ∧ C.color o = .blue
  · obtain ⟨o, hno, ho⟩ := hblue
    exact lemma4_8_n_has_blue C hpath ha hb hc hd he hf hg hh Q hno ho
  · apply lemma4_8_n_no_blue C hpath ha hb hc hd he hf Q
    intro z hnz hz
    exact hblue ⟨z, hnz, hz⟩

theorem lemma4_8_case_lm_bluish_complete
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .bluish) :
    HasReachableReduction C := by
  rcases lemma4_8_case_lm_bluish C hpath ha hb hc hd he Q hl hm with
    hresult | hR
  · exact hresult
  · obtain ⟨R⟩ := hR
    rcases lemma4_8_bluish_hard_setup C hpath ha hb hc hd he hf hg hh R with
      hresult | hS
    · exact hresult
    · obtain ⟨S⟩ := hS
      exact lemma4_8_n_cases C hpath ha hb hc hd he hf hg hh S

/-- Restart Case (3.4.3.1) in a recomputed coloring.

`Q` is used only as a carrier for the graph-theoretic configuration obtained
before a flip.  The color hypotheses needed in the current coloring `C` are
listed explicitly.  In particular, the colors of the auxiliary third
neighbors `x` and `y` are reconstructed here rather than transported across
the flip. -/
theorem lemma4_8_case_lm_bluish_restart
    (C₀ C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8LMConfiguration C₀ a b c d e f g h)
    (hi : C.color Q.i = .reddish) (hj : C.color Q.j = .bluish)
    (hk : C.color Q.k = .reddish)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .bluish) :
    HasReachableReduction C := by
  classical
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  have hxSide := C.other_neighbor_of_red_is_blueSide ha hb hab Q.hax Q.hxb
  rcases hxSide with hx | hx
  · have hjx : ¬ G.Adj Q.j Q.x :=
      C.bluish_not_adj_blueSide hj (Or.inl hx)
    have hjd : ¬ G.Adj Q.j d :=
      C.bluish_not_adj_blueSide hj (Or.inl hd)
    have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
    have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
    have hxe : ¬ G.Adj Q.x e := by
      intro hxe
      have : G.Adj e Q.x := hxe.symm
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
        (hv (u := (5 : Fin 8)) (v := 3) (by decide))
        (color_ne hf hj (by decide)) (color_ne hd hj (by decide))
        (by intro h; exact (nonedge 0 5 (by native_decide)) (by simpa [h] using Q.hax))
        (by intro h; exact (nonedge 0 3 (by native_decide)) (by simpa [h] using Q.hax))
        Q.hxj
      exact this
    have hxc : Q.x ≠ c := by
      intro h
      exact (nonedge 0 2 (by native_decide)) (by simpa [h] using Q.hax)
    have hxd : ¬ G.Adj Q.x d := by
      have hdxc := C.blueSide_not_adj_second_neighbor
        (by simp [hd]) (by simp [hc]) (by simp [hx]) hcd.symm hxc.symm
      simpa [SimpleGraph.adj_comm] using hdxc
    have hceSwap := containsCutEnhancerB_of C.swapSides
      (by simp [hj]) (by simp [ha]) (by simp [hx])
      (by simp [he]) (by simp [hd])
      Q.hja Q.hej.symm Q.hax hde.symm hjx hjd hae had hxe hxd
    exact HasReachableReduction.of_current_ce C
      ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
  · have hySide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm Q.hby Q.hya
    have hyd : Q.y ≠ d := by
      intro h
      exact (nonedge 1 3 (by native_decide)) (by simpa [h] using Q.hby)
    rcases lemma3_3 C hb hc hd hySide hbc Q.hby hcd Q.hyc.symm hyd.symm with
      hy | hce
    · let deep : Lemma4_8Case3Configuration C a b c d e f g h := {
        i := Q.i
        j := Q.j
        x := Q.x
        y := Q.y
        hi := hi
        hj := hj
        hx := hx
        hy := hy
        hdi := Q.hdi
        hih := Q.hih
        hej := Q.hej
        hja := Q.hja
        hax := Q.hax
        hxb := Q.hxb
        hxj := Q.hxj
        hby := Q.hby
        hya := Q.hya
        hyc := Q.hyc
        hig := Q.hig
        hjb := Q.hjb }
      let late : Lemma4_8Case3_4Configuration C a b c d e f g h := {
        toLemma4_8Case3Configuration := deep
        hxy := Q.hxy
        hij := Q.hij
        hnotBoth := Q.hnotBoth }
      let kconfig : Lemma4_8KConfiguration C a b c d e f g h := {
        toLemma4_8Case3_4Configuration := late
        hic := Q.hic
        k := Q.k
        hk := hk
        hck := Q.hck
        hkb := Q.hkb
        hkd := Q.hkd
        hkg := Q.hkg
        hkdeg := Q.hkdeg }
      let current : Lemma4_8LMConfiguration C a b c d e f g h := {
        toLemma4_8KConfiguration := kconfig
        hkj := Q.hkj
        hkh := Q.hkh
        l := Q.l
        m := Q.m
        hkl := Q.hkl
        hkm := Q.hkm
        hlc := Q.hlc
        hmc := Q.hmc
        hlm := Q.hlm
        hlSide := Or.inr hl
        hmSide := Or.inr hm }
      exact lemma4_8_case_lm_bluish_complete C hp ha hb hc hd he hf hg hh
        current hl hm
    · exact HasReachableReduction.of_current_ce C hce

end Subcubic
