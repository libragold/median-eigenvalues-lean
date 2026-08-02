import Subcubic.Lemma4_10.Isolated

/-!
# Lemma 4.10: Cases (1), (2), and setup for Case (3)

This module handles cases (1), (2), and the reversal used at the start of
case (3).  What remains is the single orientation shown in the prose proof.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_10Case3Configuration (C : GoodColoring G)
    (a b c d e f : V) where
  g : V
  h : V
  hg : C.color g = .bluish
  hh : C.color h = .bluish
  hbg : G.Adj b g
  hgf : G.Adj g f
  heh : G.Adj e h
  hha : G.Adj h a
  hge : ¬ G.Adj g e
  hhb : ¬ G.Adj h b

theorem lemma4_10_cases1_and_2_setup3
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoBlueAtF : ∀ v, G.Adj f v → C.color v ≠ .blue) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_10Case3Configuration C a b c d e f) := by
  classical
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath6 G a b c d e f := ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) :=
    hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    (hedge x y).mp hxy
  have nonedge (x y : Fin 6) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hbe : ¬ G.Adj b e := by simpa using nonedge 1 4 (by native_decide)
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have hec : ¬ G.Adj e c := by simpa using nonedge 4 2 (by native_decide)
  have hacV : a ≠ c := hv (x := (0 : Fin 6)) (y := 2) (by decide)
  obtain ⟨g, hbg, hga, hgc⟩ :=
    C.exists_third_neighbor (Or.inl hb) hacV
  have hgSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbg hga
  have hgd : g ≠ d := by intro h; subst g; exact hbd hbg
  rcases lemma3_3 C hb hc hd hgSide hbc hbg hcd
      hgc.symm hgd.symm with hg | hce
  · by_cases hge : G.Adj g e
    · left
      apply HasReachableReduction.of_current_ptr C
      apply containsPositiveC C hb he hc hd hg hbc hbg hde.symm hge.symm hcd
      · exact hbe
      · exact hbd
      · exact hec
    · by_cases hgf : G.Adj g f
      · have hfdV : f ≠ d := hv (x := (5 : Fin 6)) (y := 3) (by decide)
        obtain ⟨h, heh, hhf, hhd⟩ :=
          C.exists_third_neighbor (Or.inl he) hfdV
        have hhSide := C.other_neighbor_of_red_is_blueSide he hf hef heh hhf
        have hecAdj : ¬ G.Adj e c := hec
        have hhc : h ≠ c := by intro hx; subst h; exact hecAdj heh
        rcases lemma3_3 C he hd hc hhSide hde.symm heh hcd.symm
            hhd.symm hhc.symm with hh | hce
        · by_cases hhb : G.Adj h b
          · left
            apply HasReachableReduction.of_current_ptr C
            apply containsPositiveC C he hb hd hc hh hde.symm heh hbc
              hhb.symm hcd.symm
            · exact fun h => hbe h.symm
            · exact hec
            · exact hbd
          · by_cases hha : G.Adj h a
            · exact Or.inr ⟨⟨g, h, hg, hh, hbg, hgf, heh, hha, hge, hhb⟩⟩
            · left
              exact lemma4_10_flip_bc_isolates_ef C
                (a := f) (b := e) (c := d) (d := c) (e := b) (f := a)
                (g := h) hp.reverse hf he hd hc hb ha hh heh
                hhb hha hNoBlueAtA
        · exact Or.inl (HasReachableReduction.of_current_ce C hce)
      · exact Or.inl (lemma4_10_flip_bc_isolates_ef C hp ha hb hc hd he hf
          hg hbg hge hgf hNoBlueAtF)
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

end Subcubic
