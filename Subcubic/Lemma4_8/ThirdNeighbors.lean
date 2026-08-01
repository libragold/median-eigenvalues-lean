import Subcubic.Lemma4_8.Symmetry

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The first sentence of the proof of Lemma 4.8, for both middle vertices:
`d` has a reddish third neighbor `i`, and `e` has a bluish third neighbor
`j`, unless Lemma 3.3 has already produced a cut enhancer. -/
theorem lemma4_8_third_neighbors
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red) :
    (∃ i j, G.Adj d i ∧ C.color i = .reddish ∧
      G.Adj e j ∧ C.color j = .bluish) ∨ ContainsCutEnhancer C := by
  classical
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have vertex_ne {x y : Fin 8} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h] x) ≠
        (![a, b, c, d, e, f, g, h] y) := hinj.ne hxy
  have hcd : G.Adj c d := (hedge 2 3).mp (by native_decide)
  have hde : G.Adj d e := (hedge 3 4).mp (by native_decide)
  have hef : G.Adj e f := (hedge 4 5).mp (by native_decide)
  obtain ⟨i, hdi, hic, hie⟩ :=
    C.exists_third_neighbor (Or.inr hd)
      (vertex_ne (x := (2 : Fin 8)) (y := 4) (by decide))
  have hiSide : C.color i = .red ∨ C.color i = .reddish :=
    C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdi hic
  rcases lemma3_3_reversed C hd he hf hiSide hde hdi hef
      hie.symm (by
        intro hif
        subst i
        have hdf : ¬ G.Adj d f := fun hdf =>
          (by native_decide : ¬ (graphOfEdges
            [(0, 1), (1, 2), (2, 3), (3, 4),
             (4, 5), (5, 6), (6, 7)]).Adj (3 : Fin 8) 5)
            ((hedge 3 5).mpr hdf)
        exact hdf hdi) with hi | hce
  · obtain ⟨j, hej, hjd, hjf⟩ :=
      C.exists_third_neighbor (Or.inl he)
        (vertex_ne (x := (3 : Fin 8)) (y := 5) (by decide))
    have hjSide : C.color j = .blue ∨ C.color j = .bluish :=
      C.other_neighbor_of_red_is_blueSide he hf hef hej hjf
    rcases lemma3_3 C he hd hc hjSide hde.symm hej hcd.symm
        hjd.symm (by
          intro hjc
          subst j
          have hec : ¬ G.Adj e c := fun hec =>
            (by native_decide : ¬ (graphOfEdges
              [(0, 1), (1, 2), (2, 3), (3, 4),
               (4, 5), (5, 6), (6, 7)]).Adj (4 : Fin 8) 2)
              ((hedge 4 2).mpr hec)
          exact hec hej) with hj | hce
    · exact Or.inl ⟨i, j, hdi, hi, hej, hj⟩
    · exact Or.inr hce
  · exact Or.inr hce

end Subcubic
