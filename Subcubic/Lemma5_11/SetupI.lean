import Subcubic.Lemma5_11.Case3_1

/-!
# Entering case (3.2) of Lemma 5.11

The third neighbor `i` of `c` is reddish.  Lemma 3.5 supplies its ambient
degree, and cut enhancer `d` rules out the edge `i-g`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_11IConfiguration (C : GoodColoring G)
    (a b c d e f : V) extends
    Lemma5_11Case3_2Configuration C a b c d e f where
  i : V
  hi : C.color i = .reddish
  hci : G.Adj c i
  hib : i ≠ b
  hid : i ≠ d
  hideg : vertexDegree G i = 3
  hig : ¬ G.Adj i g

theorem lemma5_11_setup_i
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (_he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_11Case3_2Configuration C a b c d e f) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_11IConfiguration C a b c d e f) := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact Or.inl hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) := hinj.ne hxy
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
  have hbdV : b ≠ d := hv (x := (1 : Fin 6)) (y := 3) (by decide)
  obtain ⟨i, hci, hib, hid⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inr hc)) hbdV
  have hiSide := C.other_neighbor_of_blue_is_redSide hc hd hcd hci hid
  have hca : ¬ G.Adj c a := by simpa using nonedge 2 0 (by native_decide)
  have hia : i ≠ a := by intro h; subst i; exact hca hci
  rcases lemma3_3_reversed C hc hb ha hiSide hbc.symm hci hab.symm
      hib.symm hia.symm with hi | hce
  · rcases lemma3_5 C hb hc hi hbc hci with hideg | hce
    · by_cases hig : G.Adj i Q.g
      · left
        have hbi : ¬ G.Adj b i :=
          C.reddish_not_adj_redSide hi (Or.inl hb) ∘ SimpleGraph.Adj.symm
        have hbf : ¬ G.Adj b f := by
          simpa using nonedge 1 5 (by native_decide)
        have hif : ¬ G.Adj i f :=
          C.reddish_not_adj_redSide hi (Or.inl hf)
        have hcg : ¬ G.Adj c Q.g :=
          C.bluish_not_adj_blueSide Q.hg (Or.inl hc) ∘ SimpleGraph.Adj.symm
        have hcf : ¬ G.Adj c f := by
          simpa using nonedge 2 5 (by native_decide)
        exact HasReachableNegativeReduction.of_current_ce C
          (containsCutEnhancerD_of C hb hi hc Q.hg hf hbc Q.hbg hci.symm hig
            Q.hgf hbi hbf hif hcg hcf
            (hv (x := (1 : Fin 6)) (y := 5) (by decide)))
      · exact Or.inr ⟨⟨Q, i, hi, hci, hib, hid, hideg, hig⟩⟩
    · exact Or.inl (HasReachableNegativeReduction.of_lemma3_4 C hce)
  · exact Or.inl (HasReachableNegativeReduction.of_current_ce C hce)

end Subcubic
