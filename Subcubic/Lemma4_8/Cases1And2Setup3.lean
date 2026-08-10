import Subcubic.Lemma4_8.Case2

/-!
# Lemma 4.8: Cases (1), (2), and setup for Case (3)

Cases (1) and (2) are discharged here.  In Case (3), the proof is oriented
as in the prose and the third neighbors needed by Cases (3.1)--(3.4) are
recorded in `Lemma4_8Case3Configuration`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_8Case3Configuration (C : GoodColoring G)
    (a b c d e f g h : V) where
  i : V
  j : V
  x : V
  y : V
  hi : C.color i = .reddish
  hj : C.color j = .bluish
  hx : C.color x = .bluish
  hy : C.color y = .bluish
  hdi : G.Adj d i
  hih : G.Adj i h
  hej : G.Adj e j
  hja : G.Adj j a
  hax : G.Adj a x
  hxb : x ≠ b
  hxj : x ≠ j
  hby : G.Adj b y
  hya : y ≠ a
  hyc : y ≠ c
  hig : ¬ G.Adj i g
  hjb : ¬ G.Adj j b

theorem lemma4_8_case3_setup
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (_he : C.color e = .red) (_hf : C.color f = .red)
    (_hg : C.color g = .blue) (_hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hi : C.color i = .reddish) (hj : C.color j = .bluish)
    (hdi : G.Adj d i) (hih : G.Adj i h)
    (hej : G.Adj e j) (hja : G.Adj j a)
    (hig : ¬ G.Adj i g) (hjb : ¬ G.Adj j b) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8Case3Configuration C a b c d e f g h) := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact Or.inl hdone
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
  have hbj : b ≠ j := by intro h; subst j; simp_all
  obtain ⟨x, hax, hxb, hxj⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inl ha)) hbj
  have hxSide := C.other_neighbor_of_red_is_blueSide ha hb hab hax hxb
  have hx : C.color x = .bluish := by
    rcases hxSide with hx | hx
    · exact (hNoBlueAtA x hax hx).elim
    · exact hx
  obtain ⟨y, hby, hya, hyc⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inl hb))
      (hv (u := (0 : Fin 8)) (v := 2) (by decide))
  have hySide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hby hya
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have hyd : y ≠ d := by intro h; subst y; exact hbd hby
  rcases lemma3_3 C hb hc hd hySide hbc hby hcd hyc.symm hyd.symm with hy | hce
  · exact Or.inr ⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
      hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩⟩
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

/-- Formalization of Cases (1) and (2), followed by the orientation and
third-neighbor setup at the start of Case (3). -/
theorem lemma4_8_cases1_and_2_setup3
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtH : ∀ v, G.Adj h v → C.color v ≠ .red) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8Case3Configuration C a b c d e f g h) := by
  classical
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8)
      (huv : (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8)
      (huv : ¬ (graphOfEdges
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
  rcases lemma4_8_third_neighbors C hp hc hd he hf with hthird | hce
  · rcases hthird with ⟨i, j, hdi, hi, hej, hj⟩
    by_cases hig : G.Adj i g
    · left
      apply lemma4_8_case_i_adj_g C hd he hf hg hi hde hdi hfg hig.symm hef
      · simpa using nonedge 3 6 (by native_decide)
      · simpa using nonedge 3 5 (by native_decide)
      · simpa using nonedge 6 4 (by native_decide)
      · have hid : i ≠ d := hdi.ne.symm
        have higV : i ≠ g := hig.ne
        have hie : i ≠ e := by intro h; subst i; simp_all
        have hif : i ≠ f := by intro h; subst i; simp_all
        have hdg : d ≠ g := hv (u := (3 : Fin 8)) (v := 6) (by decide)
        have hdeV : d ≠ e := hv (u := (3 : Fin 8)) (v := 4) (by decide)
        have hdfV : d ≠ f := hv (u := (3 : Fin 8)) (v := 5) (by decide)
        have hgeV : g ≠ e := hv (u := (6 : Fin 8)) (v := 4) (by decide)
        have hgfV : g ≠ f := hv (u := (6 : Fin 8)) (v := 5) (by decide)
        have hefV : e ≠ f := hv (u := (4 : Fin 8)) (v := 5) (by decide)
        simp [hdg, hdeV, hdfV, Ne.symm hid, hgeV, hgfV,
          Ne.symm higV, hefV, Ne.symm hie, Ne.symm hif]
    · by_cases hih : G.Adj i h
      · by_cases hja : G.Adj j a
        · by_cases hjb : G.Adj j b
          · left
            have hpRev := hp.reverse
            have hptrRev := lemma4_8_case_i_adj_g C.swapSides
              (d := e) (e := d) (f := c) (g := b) (i := j)
              (by simp [he]) (by simp [hd]) (by simp [hc]) (by simp [hb])
              (by simp [hj]) hde.symm hej hbc.symm hjb.symm hcd.symm
              (by simpa using nonedge 4 1 (by native_decide))
              (by simpa using nonedge 4 2 (by native_decide))
              (by simpa using nonedge 1 3 (by native_decide))
              (by
                have hje : j ≠ e := hej.ne.symm
                have hjbV : j ≠ b := hjb.ne
                have hjd : j ≠ d := by intro h; subst j; simp_all
                have hjc : j ≠ c := by intro h; subst j; simp_all
                have hebV : e ≠ b := hv (u := (4 : Fin 8)) (v := 1) (by decide)
                have hedV : e ≠ d := hv (u := (4 : Fin 8)) (v := 3) (by decide)
                have hecV : e ≠ c := hv (u := (4 : Fin 8)) (v := 2) (by decide)
                have hbdV : b ≠ d := hv (u := (1 : Fin 8)) (v := 3) (by decide)
                have hbcV : b ≠ c := hv (u := (1 : Fin 8)) (v := 2) (by decide)
                have hdcV : d ≠ c := hv (u := (3 : Fin 8)) (v := 2) (by decide)
                simp [hebV, hedV, hecV, Ne.symm hje, hbdV, hbcV,
                  Ne.symm hjbV, hdcV, Ne.symm hjd, Ne.symm hjc])
            exact HasReachableReduction.of_swapSides C hptrRev
          · exact lemma4_8_case3_setup C hp ha hb hc hd he hf hg hh
              hNoBlueAtA (i := i) (j := j) hi hj hdi hih hej hja hig hjb
        · by_cases hjb : G.Adj j b
          · left
            have hptrRev := lemma4_8_case_i_adj_g C.swapSides
              (d := e) (e := d) (f := c) (g := b) (i := j)
              (by simp [he]) (by simp [hd]) (by simp [hc]) (by simp [hb])
              (by simp [hj]) hde.symm hej hbc.symm hjb.symm hcd.symm
              (by simpa using nonedge 4 1 (by native_decide))
              (by simpa using nonedge 4 2 (by native_decide))
              (by simpa using nonedge 1 3 (by native_decide))
              (by
                have hje : j ≠ e := hej.ne.symm
                have hjbV : j ≠ b := hjb.ne
                have hjd : j ≠ d := by intro h; subst j; simp_all
                have hjc : j ≠ c := by intro h; subst j; simp_all
                have hebV : e ≠ b := hv (u := (4 : Fin 8)) (v := 1) (by decide)
                have hedV : e ≠ d := hv (u := (4 : Fin 8)) (v := 3) (by decide)
                have hecV : e ≠ c := hv (u := (4 : Fin 8)) (v := 2) (by decide)
                have hbdV : b ≠ d := hv (u := (1 : Fin 8)) (v := 3) (by decide)
                have hbcV : b ≠ c := hv (u := (1 : Fin 8)) (v := 2) (by decide)
                have hdcV : d ≠ c := hv (u := (3 : Fin 8)) (v := 2) (by decide)
                simp [hebV, hedV, hecV, Ne.symm hje, hbdV, hbcV,
                  Ne.symm hjbV, hdcV, Ne.symm hjd, Ne.symm hjc])
            exact HasReachableReduction.of_swapSides C hptrRev
          · left
            have hRev := lemma4_8_case_i_not_adj_g_h C.swapSides
              (a := h) (b := g) (c := f) (d := e)
              (e := d) (f := c) (g := b) (h := a) (i := j) (j := i)
              hp.reverse (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              (by simp [hj]) (by simp [hi]) hej hdi hjb hja
              (by
                intro v hav hvred
                have hvblue : C.color v = .blue := by
                  change (C.color v).swap = .red at hvred
                  exact (Color.swap_eq_red _).1 hvred
                exact hNoBlueAtA v hav hvblue)
            exact HasReachableReduction.of_swapSides C hRev
      · left
        exact lemma4_8_case_i_not_adj_g_h C hp hc hd he hf hg hh hi hj
          hdi hej hig hih hNoRedAtH
  · exact Or.inl (HasReachableReduction.of_lemma3_6 C
      (HasReachableLemma3_6Obstruction.of_current C hce))


end Subcubic
