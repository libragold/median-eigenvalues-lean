import Subcubic.Lemma5_9.SetupI

/-! Lemma 5.9, Case (3.4): expose the reddish third neighbor `k` of `c`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9KConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9IConfiguration C a b c d e f g h where
  k : V
  hk : C.color k = .reddish
  hck : G.Adj c k
  hkb : k ≠ b
  hkd : k ≠ d
  hkg : ¬ G.Adj k g
  hkdeg : vertexDegree G k = 3

theorem lemma5_9_setup_k
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hf : C.color f = .red) (hg : C.color g = .blue)
    (Q : Lemma5_9IConfiguration C a b c d e f g h) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9KConfiguration C a b c d e f g h) := by
  classical
  rcases Q with ⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, hideg, t, ht, hit, htd, hth⟩
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
  have hfg := edge 5 6 (by native_decide)
  obtain ⟨k, hck, hkb, hkd⟩ :=
    C.exists_third_neighbor (Or.inr hc)
      (hv (u := (1 : Fin 8)) (v := 3) (by decide))
  have hkSide : C.color k = .red ∨ C.color k = .reddish :=
    C.other_neighbor_of_blue_is_redSide hc hd hcd hck hkd
  have hak : a ≠ k := by
    intro q; subst k
    exact (nonedge 2 0 (by native_decide)) hck
  rcases lemma3_3_reversed C hc hb ha hkSide hbc.symm hck hab.symm
      hkb.symm hak with hk | hce
  · by_cases hkg : G.Adj k g
    · left
      have hkbAdj : ¬ G.Adj k b :=
        C.reddish_not_adj_redSide hk (Or.inl hb)
      have hkf : ¬ G.Adj k f :=
        C.reddish_not_adj_redSide hk (Or.inl hf)
      have hcg : ¬ G.Adj c g :=
        C.blueSide_not_adj_second_neighbor (by simp [hc]) (by simp [hd])
          (by simp [hg]) hcd
          (hv (u := (3 : Fin 8)) (v := 6) (by decide))
      have hcf : ¬ G.Adj c f := by simpa using nonedge 2 5 (by native_decide)
      have hbg : ¬ G.Adj b g := by simpa using nonedge 1 6 (by native_decide)
      have hbf : ¬ G.Adj b f :=
        C.redSide_not_adj_second_neighbor (by simp [hb]) (by simp [ha])
          (by simp [hf]) hab.symm
          (hv (u := (0 : Fin 8)) (v := 5) (by decide))
      exact HasReachableNegativeReduction.of_current_ce C
        (containsCutEnhancerB_of C hk hc hb hg hf hck.symm hkg
          hbc.symm hfg.symm hkbAdj hkf hcg hcf hbg hbf)
    · rcases lemma3_5 C hb hc hk hbc hck with hkdeg | hce
      · right
        exact ⟨{
          toLemma5_9IConfiguration :=
            ⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
              hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩,
              hxy, hij, hnotBoth⟩,
              hic, hideg, t, ht, hit, htd, hth⟩
          k := k
          hk := hk
          hck := hck
          hkb := hkb
          hkd := hkd
          hkg := hkg
          hkdeg := hkdeg }⟩
      · exact Or.inl (HasReachableNegativeReduction.of_current_ce C hce)
  · exact Or.inl (HasReachableNegativeReduction.of_current_ce C hce)

end Subcubic
