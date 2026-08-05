import Subcubic.Lemma5_7
import Subcubic.Lemma5_2
import Subcubic.Lemma5_3

/-!
# Inlined Lemma 5.10 argument

The paper uses this lemma whenever an alternating sequence of five
monochromatic edges occurs merely as a subgraph.  If an extra crossing edge
is present, Lemma 5.2 or 5.3 applies; otherwise the ten vertices induce the
path required by Lemma 5.7.  Distance bounds are deliberately omitted.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 5.10.** An alternating five-edge path occurring as a subgraph
already has the same reduction conclusion as the induced configuration of
Lemma 5.7. -/
theorem lemma5_10_inline
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (hpath : FormsPath10Subgraph G a b c d e f g h i j)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .red) (hj : C.color j = .red) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsPath10Subgraph] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 10} (hxy : x ≠ y) :
      (![a, b, c, d, e, f, g, h, i, j] x) ≠
        (![a, b, c, d, e, f, g, h, i, j] y) := hinj.ne hxy
  have hab : G.Adj a b := hedge 0 1 (by native_decide)
  have hbc : G.Adj b c := hedge 1 2 (by native_decide)
  have hcd : G.Adj c d := hedge 2 3 (by native_decide)
  have hde : G.Adj d e := hedge 3 4 (by native_decide)
  have hef : G.Adj e f := hedge 4 5 (by native_decide)
  have hfg : G.Adj f g := hedge 5 6 (by native_decide)
  have hgh : G.Adj g h := hedge 6 7 (by native_decide)
  have hhi : G.Adj h i := hedge 7 8 (by native_decide)
  have hij : G.Adj i j := hedge 8 9 (by native_decide)
  by_contra hresult
  have noCurrent (hout : ContainsNegativeTailReducer C ∨
      ContainsCutEnhancer C) : False := by
    apply hresult
    rcases hout with hntr | hce
    · exact HasReachableNegativeReduction.of_current_ntr C hntr
    · exact HasReachableNegativeReduction.of_current_ce C hce
  have noSwapped (hout : ContainsNegativeTailReducer C.swapSides ∨
      ContainsCutEnhancer C.swapSides) : False := by
    apply hresult
    apply HasReachableNegativeReduction.of_swapSides C
    rcases hout with hptr | hce
    · exact HasReachableNegativeReduction.of_current_ntr C.swapSides hptr
    · exact HasReachableNegativeReduction.of_current_ce C.swapSides hce
  have noSecondCrossing {r₀ r₁ s₀ s₁ x y : V}
      (hr₀ : C.color r₀ = .red) (hr₁ : C.color r₁ = .red)
      (hs₀ : C.color s₀ = .blue) (hs₁ : C.color s₁ = .blue)
      (hrr : G.Adj r₀ r₁) (hss : G.Adj s₀ s₁)
      (hone : G.Adj x y)
      (hxyOne : (x = r₀ ∨ x = r₁) ∧ (y = s₀ ∨ y = s₁))
      {u v : V} (htwo : G.Adj u v)
      (huvTwo : (u = r₀ ∨ u = r₁) ∧ (v = s₀ ∨ v = s₁))
      (hdifferent : (x, y) ≠ (u, v)) : False := by
    apply noCurrent
    apply lemma5_2 C r₀ r₁ s₀ s₁
      hrr hr₀ hr₁ hss hs₀ hs₁
    rcases hxyOne with ⟨rfl | rfl, rfl | rfl⟩ <;>
      rcases huvTwo with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp_all [fourVertexCrossEdgeCount] <;> omega
  have pair_ne_left {x y u v : V} (hxu : x ≠ u) : (x, y) ≠ (u, v) :=
    fun hpair => hxu (congrArg Prod.fst hpair)
  have pair_ne_right {x y u v : V} (hyv : y ≠ v) : (x, y) ≠ (u, v) :=
    fun hpair => hyv (congrArg Prod.snd hpair)
  -- Extra crossings between consecutive monochromatic edges invoke Lemma 5.2.
  have hac : ¬ G.Adj a c := fun h => noSecondCrossing ha hb hc hd hab hcd
    h ⟨Or.inl rfl, Or.inl rfl⟩ hbc ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (0 : Fin 10)) (y := 1) (by decide)))
  have had : ¬ G.Adj a d := fun h => noSecondCrossing ha hb hc hd hab hcd
    h ⟨Or.inl rfl, Or.inr rfl⟩ hbc ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (0 : Fin 10)) (y := 1) (by decide)))
  have hbd : ¬ G.Adj b d := fun h => noSecondCrossing ha hb hc hd hab hcd
    hbc ⟨Or.inr rfl, Or.inl rfl⟩ h ⟨Or.inr rfl, Or.inr rfl⟩
      (pair_ne_right (hv (x := (2 : Fin 10)) (y := 3) (by decide)))
  have hce : ¬ G.Adj c e := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inl rfl, Or.inl rfl⟩
      (pair_ne_right (hv (x := (3 : Fin 10)) (y := 2) (by decide)))
  have hcf : ¬ G.Adj c f := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (4 : Fin 10)) (y := 5) (by decide)))
  have hdf : ¬ G.Adj d f := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inr rfl⟩
      (pair_ne_left (hv (x := (4 : Fin 10)) (y := 5) (by decide)))
  have heg : ¬ G.Adj e g := fun h => noSecondCrossing he hf hg hh hef hgh
    h ⟨Or.inl rfl, Or.inl rfl⟩ hfg ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (4 : Fin 10)) (y := 5) (by decide)))
  have heh : ¬ G.Adj e h := fun h => noSecondCrossing he hf hg hh hef hgh
    h ⟨Or.inl rfl, Or.inr rfl⟩ hfg ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (4 : Fin 10)) (y := 5) (by decide)))
  have hfh : ¬ G.Adj f h := fun h => noSecondCrossing he hf hg hh hef hgh
    hfg ⟨Or.inr rfl, Or.inl rfl⟩ h ⟨Or.inr rfl, Or.inr rfl⟩
      (pair_ne_right (hv (x := (6 : Fin 10)) (y := 7) (by decide)))
  have hgi : ¬ G.Adj g i := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inl rfl, Or.inl rfl⟩
      (pair_ne_right (hv (x := (7 : Fin 10)) (y := 6) (by decide)))
  have hgj : ¬ G.Adj g j := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inl rfl⟩
      (pair_ne_left (hv (x := (8 : Fin 10)) (y := 9) (by decide)))
  have hhj : ¬ G.Adj h j := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inr rfl⟩
      (pair_ne_left (hv (x := (8 : Fin 10)) (y := 9) (by decide)))
  -- A crossing that skips a monochromatic block gives three neighbors of
  -- one blue edge, so the color-reversed Lemma 5.3 applies.
  have noFarLeft {x : V} (hx : C.color x = .red)
      (hxf : x ≠ f) (hxi : x ≠ i)
      (hcross : G.Adj g x ∨ G.Adj h x) : False := by
    apply noSwapped
    apply lemma5_3_of_three_neighbors C.swapSides
      (by simp [hg]) (by simp [hh]) hgh
      (by simp [hf]) (by simp [hi]) (by simp [hx])
      (hv (x := (5 : Fin 10)) (y := 8) (by decide)) hxf.symm hxi.symm
      (Or.inl hfg.symm) (Or.inr hhi) hcross
  have noFarRight {x : V} (hx : C.color x = .red)
      (hxb : x ≠ b) (hxe : x ≠ e)
      (hcross : G.Adj c x ∨ G.Adj d x) : False := by
    apply noSwapped
    apply lemma5_3_of_three_neighbors C.swapSides
      (by simp [hc]) (by simp [hd]) hcd
      (by simp [hb]) (by simp [he]) (by simp [hx])
      (hv (x := (1 : Fin 10)) (y := 4) (by decide)) hxb.symm hxe.symm
      (Or.inl hbc.symm) (Or.inr hde) hcross
  have hag : ¬ G.Adj a g := fun h => noFarLeft ha
    (hv (x := (0 : Fin 10)) (y := 5) (by decide))
    (hv (x := (0 : Fin 10)) (y := 8) (by decide)) (Or.inl h.symm)
  have hah : ¬ G.Adj a h := fun h => noFarLeft ha
    (hv (x := (0 : Fin 10)) (y := 5) (by decide))
    (hv (x := (0 : Fin 10)) (y := 8) (by decide)) (Or.inr h.symm)
  have hbg : ¬ G.Adj b g := fun h => noFarLeft hb
    (hv (x := (1 : Fin 10)) (y := 5) (by decide))
    (hv (x := (1 : Fin 10)) (y := 8) (by decide)) (Or.inl h.symm)
  have hbh : ¬ G.Adj b h := fun h => noFarLeft hb
    (hv (x := (1 : Fin 10)) (y := 5) (by decide))
    (hv (x := (1 : Fin 10)) (y := 8) (by decide)) (Or.inr h.symm)
  have hci : ¬ G.Adj c i := fun h => noFarRight hi
    (hv (x := (8 : Fin 10)) (y := 1) (by decide))
    (hv (x := (8 : Fin 10)) (y := 4) (by decide)) (Or.inl h)
  have hcj : ¬ G.Adj c j := fun h => noFarRight hj
    (hv (x := (9 : Fin 10)) (y := 1) (by decide))
    (hv (x := (9 : Fin 10)) (y := 4) (by decide)) (Or.inl h)
  have hdi : ¬ G.Adj d i := fun h => noFarRight hi
    (hv (x := (8 : Fin 10)) (y := 1) (by decide))
    (hv (x := (8 : Fin 10)) (y := 4) (by decide)) (Or.inr h)
  have hdj : ¬ G.Adj d j := fun h => noFarRight hj
    (hv (x := (9 : Fin 10)) (y := 1) (by decide))
    (hv (x := (9 : Fin 10)) (y := 4) (by decide)) (Or.inr h)
  -- Matching on each side supplies all remaining nonedges.
  have redNonedge {x mate y : V}
      (hx : C.color x = .red) (hm : C.color mate = .red)
      (hy : C.color y = .red) (hxm : G.Adj x mate) (hmy : mate ≠ y) :
      ¬ G.Adj x y := by
    exact C.redSide_not_adj_second_neighbor
      (by simp [hx]) (by simp [hm]) (by simp [hy]) hxm hmy
  have blueNonedge {x mate y : V}
      (hx : C.color x = .blue) (hm : C.color mate = .blue)
      (hy : C.color y = .blue) (hxm : G.Adj x mate) (hmy : mate ≠ y) :
      ¬ G.Adj x y := by
    exact C.blueSide_not_adj_second_neighbor
      (by simp [hx]) (by simp [hm]) (by simp [hy]) hxm hmy
  have hae := redNonedge ha hb he hab
    (hv (x := (1 : Fin 10)) (y := 4) (by decide))
  have haf := redNonedge ha hb hf hab
    (hv (x := (1 : Fin 10)) (y := 5) (by decide))
  have hai := redNonedge ha hb hi hab
    (hv (x := (1 : Fin 10)) (y := 8) (by decide))
  have haj := redNonedge ha hb hj hab
    (hv (x := (1 : Fin 10)) (y := 9) (by decide))
  have hbe := redNonedge hb ha he hab.symm
    (hv (x := (0 : Fin 10)) (y := 4) (by decide))
  have hbf := redNonedge hb ha hf hab.symm
    (hv (x := (0 : Fin 10)) (y := 5) (by decide))
  have hbi := redNonedge hb ha hi hab.symm
    (hv (x := (0 : Fin 10)) (y := 8) (by decide))
  have hbj := redNonedge hb ha hj hab.symm
    (hv (x := (0 : Fin 10)) (y := 9) (by decide))
  have hei := redNonedge he hf hi hef
    (hv (x := (5 : Fin 10)) (y := 8) (by decide))
  have hej := redNonedge he hf hj hef
    (hv (x := (5 : Fin 10)) (y := 9) (by decide))
  have hfi := redNonedge hf he hi hef.symm
    (hv (x := (4 : Fin 10)) (y := 8) (by decide))
  have hfj := redNonedge hf he hj hef.symm
    (hv (x := (4 : Fin 10)) (y := 9) (by decide))
  have hcg := blueNonedge hc hd hg hcd
    (hv (x := (3 : Fin 10)) (y := 6) (by decide))
  have hch := blueNonedge hc hd hh hcd
    (hv (x := (3 : Fin 10)) (y := 7) (by decide))
  have hdg := blueNonedge hd hc hg hcd.symm
    (hv (x := (2 : Fin 10)) (y := 6) (by decide))
  have hdh := blueNonedge hd hc hh hcd.symm
    (hv (x := (2 : Fin 10)) (y := 7) (by decide))
  have hinduced : FormsInducedPath10 G a b c d e f g h i j := by
    refine ⟨hinj, ?_⟩
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hde, hef, hfg, hgh,
        hhi, hij, hac, had, hbd, hce, hcf, hdf, heg, heh, hfh, hgi,
        hgj, hhj, hag, hah, hbg, hbh, hci, hcj, hdi, hdj,
        hae, haf, hai, haj, hbe, hbf, hbi, hbj, hei, hej, hfi, hfj,
        hcg, hch, hdg, hdh]
  exact hresult (lemma5_7 C hinduced ha hb hc hd he hf hg hh hi hj)

end Subcubic
