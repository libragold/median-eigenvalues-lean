import Subcubic.Lemma5_9.Case2

/-!
# Lemma 5.9: Cases (1), (2), and setup for Case (3)

This is the negative-tail version of the opening split in Lemma 4.8.  The
orientation step is explicit: if `j` meets `b`, reverse the path and swap the
two sides; if it meets neither `a` nor `b`, the reversed Case (2) applies.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case3_setup
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hi : C.color i = .reddish) (hj : C.color j = .bluish)
    (hdi : G.Adj d i) (hih : G.Adj i h)
    (hej : G.Adj e j) (hja : G.Adj j a)
    (hig : ¬ G.Adj i g) (hjb : ¬ G.Adj j b) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9Case3Configuration C a b c d e f g h) := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact Or.inl hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
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
  have hbj : b ≠ j := by intro q; subst j; simp_all
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
  have hyd : y ≠ d := by intro q; subst y; exact hbd hby
  rcases lemma3_3 C hb hc hd hySide hbc hby hcd hyc.symm hyd.symm with hy | hce
  · exact Or.inr ⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
      hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩⟩
  · exact Or.inl (HasReachableNegativeReduction.of_current_ce C hce)

theorem lemma5_9_cases1_and_2_setup3
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtH : ∀ v, G.Adj h v → C.color v ≠ .red) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9Case3Configuration C a b c d e f g h) := by
  classical
  rcases lemma4_8_third_neighbors C hpath hc hd he hf with
      ⟨i, j, hdi, hi, hej, hj⟩ | hce
  · by_cases hig : G.Adj i g
    · exact Or.inl (lemma5_9_case_i_adj_g C hpath.suffix6
        hc hd he hf hg hh hdi hig)
    · by_cases hih : G.Adj i h
      · by_cases hjb : G.Adj j b
        · have hrev := lemma5_9_case_i_adj_g C.swapSides hpath.prefix6.reverse
            (by simp [hf]) (by simp [he]) (by simp [hd]) (by simp [hc])
            (by simp [hb]) (by simp [ha]) hej hjb
          exact Or.inl (HasReachableNegativeReduction.of_swapSides C hrev)
        · by_cases hja : G.Adj j a
          · exact lemma5_9_case3_setup C hpath ha hb hc hd hNoBlueAtA
              hi hj hdi hih hej hja hig hjb
          · have hrev := lemma5_9_case_i_not_adj_g_h C.swapSides
              (a := h) (b := g) (c := f) (d := e)
              (e := d) (f := c) (g := b) (h := a) (i := j) (j := i)
              hpath.reverse (by simp [hf]) (by simp [he])
              (by simp [hd]) (by simp [hc]) (by simp [hb]) (by simp [ha])
              (by simp [hj]) (by simp [hi]) hej hdi hjb hja
              (by
                intro v hav hvred
                have hvblue : C.color v = .blue := by
                  change (C.color v).swap = .red at hvred
                  exact (Color.swap_eq_red _).1 hvred
                exact hNoBlueAtA v hav hvblue)
            exact Or.inl (HasReachableNegativeReduction.of_swapSides C hrev)
      · exact Or.inl (lemma5_9_case_i_not_adj_g_h C hpath hc hd he hf
          hg hh hi hj hdi hej hig hih hNoRedAtH)
  · exact Or.inl (HasReachableNegativeReduction.of_lemma3_6 C
      (HasReachableLemma3_6Obstruction.of_current C hce))

end Subcubic
