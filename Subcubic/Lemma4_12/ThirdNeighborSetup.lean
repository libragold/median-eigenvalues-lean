import Subcubic.Lemma4_12.Basic

/-! Third-neighbor setup for Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_12_third_neighbor_setup
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_12ThirdNeighborConfiguration C a b c d) := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact Or.inl hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 4} (hxy : x ≠ y) :
      (![a, b, c, d] x) ≠ (![a, b, c, d] y) := hinj.ne hxy
  have edge (x y : Fin 4)
      (hxy : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      G.Adj (![a, b, c, d] x) (![a, b, c, d] y) := (hedge x y).mp hxy
  have nonedge (x y : Fin 4)
      (hxy : ¬ (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d] x) (![a, b, c, d] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hacV : a ≠ c := hv (x := (0 : Fin 4)) (y := 2) (by decide)
  obtain ⟨e, hbe, hea, hec⟩ :=
    C.exists_third_neighbor (degreeC (Or.inl hb)) hacV
  have heSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbe hea
  have hbd : ¬ G.Adj b d := by
    simpa using nonedge 1 3 (by native_decide)
  have hed : e ≠ d := by intro h; subst e; exact hbd hbe
  rcases lemma3_3 C hb hc hd heSide hbc hbe hcd hec.symm hed.symm with
    he | hce
  · have hbdV : b ≠ d := hv (x := (1 : Fin 4)) (y := 3) (by decide)
    obtain ⟨f, hcf, hfb, hfd⟩ :=
      C.exists_third_neighbor (degreeC (Or.inr hc)) hbdV
    have hfSide := C.other_neighbor_of_blue_is_redSide hc hd hcd hcf hfd
    have hca : ¬ G.Adj c a := by
      simpa using nonedge 2 0 (by native_decide)
    have hfa : f ≠ a := by intro h; subst f; exact hca hcf
    rcases lemma3_3_reversed C hc hb ha hfSide hbc.symm hcf hab.symm
        hfb.symm hfa.symm with hf | hce
    · rcases lemma3_5 C.swapSides (by simp [hc]) (by simp [hb])
          (by simp [he]) hbc.symm hbe with hedeg | hce
      · rcases lemma3_5 C hb hc hf hbc hcf with hfdeg | hce
        · exact Or.inr ⟨⟨e, f, he, hf, hbe, hcf, hea, hec,
            hfb, hfd, hedeg, hfdeg⟩⟩
        · exact Or.inl (HasReachableReduction.of_lemma3_4 C hce)
      · exact Or.inl (HasReachableReduction.of_swapSides C
          (HasReachableReduction.of_lemma3_4 C.swapSides hce))
    · exact Or.inl (HasReachableReduction.of_current_ce C hce)
  · exact Or.inl (HasReachableReduction.of_current_ce C hce)

end Subcubic
