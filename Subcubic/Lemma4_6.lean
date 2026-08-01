import Subcubic.Lemma4_5

/-!
# Lemma 4.6 (distance-free form)

The paper uses this lemma whenever an alternating sequence of five
monochromatic edges occurs merely as a subgraph.  If an extra crossing edge
is present, Lemma 4.2 or 4.3 applies; otherwise the ten vertices induce the
path required by Lemma 4.5.  Distance bounds are deliberately omitted.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Ten distinct vertices containing the displayed path; extra edges are
allowed. -/
def FormsPath10Subgraph (G : SimpleGraph V)
    (a b c d e f g h i j : V) : Prop :=
  let p : Fin 10 → V := ![a, b, c, d, e, f, g, h, i, j]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5),
       (5, 6), (6, 7), (7, 8), (8, 9)]).Adj x y → G.Adj (p x) (p y)

/-- **Lemma 4.6.** An alternating five-edge path occurring as a subgraph
already has the same reduction conclusion as the induced configuration of
Lemma 4.5. -/
theorem lemma4_6
    (C : GoodColoring G) {a b c d e f g h i j : V}
    (hpath : FormsPath10Subgraph G a b c d e f g h i j)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hi : C.color i = .red) (hj : C.color j = .red) :
    ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
      (ContainsPositiveTailReducer M.toGoodColoring ∨
       ContainsCutEnhancer M.toGoodColoring) := by
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
  have current (hout : ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C) :
      ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
        (ContainsPositiveTailReducer M.toGoodColoring ∨
         ContainsCutEnhancer M.toGoodColoring) := by
    refine ⟨C.toMatchingCut, .refl, ?_⟩
    rcases hout with hptr | hce
    · exact Or.inl ((containsInducedUpToSwap_congr_color
        IsPositiveTailReducer (by simp)).1 hptr)
    · exact Or.inr ((containsInducedUpToSwap_congr_color
        IsCutEnhancer (by simp)).1 hce)
  by_contra hresult
  have noCurrent (hout : ContainsPositiveTailReducer C ∨
      ContainsCutEnhancer C) : False := hresult (current hout)
  have noSwapped (hout : ContainsPositiveTailReducer C.swapSides ∨
      ContainsCutEnhancer C.swapSides) : False := by
    apply noCurrent
    rcases hout with hptr | hce
    · exact Or.inl
        ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptr)
    · exact Or.inr
        ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hce)
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
    apply redEdge_blueEdge_multipleEdges C r₀ r₁ s₀ s₁
      hrr hr₀ hr₁ hss hs₀ hs₁
    rcases hxyOne with ⟨rfl | rfl, rfl | rfl⟩ <;>
      rcases huvTwo with ⟨rfl | rfl, rfl | rfl⟩ <;>
      simp_all [fourVertexCrossEdgeCount]
  -- Extra crossings between consecutive monochromatic edges invoke Lemma 4.2.
  have hac : ¬ G.Adj a c := fun h => noSecondCrossing ha hb hc hd hab hcd
    h ⟨Or.inl rfl, Or.inl rfl⟩ hbc ⟨Or.inr rfl, Or.inl rfl⟩ (by simp [hv (by decide)])
  have had : ¬ G.Adj a d := fun h => noSecondCrossing ha hb hc hd hab hcd
    h ⟨Or.inl rfl, Or.inr rfl⟩ hbc ⟨Or.inr rfl, Or.inl rfl⟩ (by simp [hv (by decide)])
  have hbd : ¬ G.Adj b d := fun h => noSecondCrossing ha hb hc hd hab hcd
    hbc ⟨Or.inr rfl, Or.inl rfl⟩ h ⟨Or.inr rfl, Or.inr rfl⟩ (by simp [hv (by decide)])
  have hce : ¬ G.Adj c e := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inl rfl, Or.inl rfl⟩
      (by simp [hv (by decide)])
  have hcf : ¬ G.Adj c f := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inl rfl⟩
      (by simp [hv (by decide)])
  have hdf : ¬ G.Adj d f := fun h => noSecondCrossing he hf hc hd hef hcd
    hde.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inr rfl⟩
      (by simp [hv (by decide)])
  have heg : ¬ G.Adj e g := fun h => noSecondCrossing he hf hg hh hef hgh
    h ⟨Or.inl rfl, Or.inl rfl⟩ hfg ⟨Or.inr rfl, Or.inl rfl⟩ (by simp [hv (by decide)])
  have heh : ¬ G.Adj e h := fun h => noSecondCrossing he hf hg hh hef hgh
    h ⟨Or.inl rfl, Or.inr rfl⟩ hfg ⟨Or.inr rfl, Or.inl rfl⟩ (by simp [hv (by decide)])
  have hfh : ¬ G.Adj f h := fun h => noSecondCrossing he hf hg hh hef hgh
    hfg ⟨Or.inr rfl, Or.inl rfl⟩ h ⟨Or.inr rfl, Or.inr rfl⟩ (by simp [hv (by decide)])
  have hgi : ¬ G.Adj g i := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inl rfl, Or.inl rfl⟩
      (by simp [hv (by decide)])
  have hgj : ¬ G.Adj g j := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inl rfl⟩
      (by simp [hv (by decide)])
  have hhj : ¬ G.Adj h j := fun h => noSecondCrossing hi hj hg hh hij hgh
    hhi.symm ⟨Or.inl rfl, Or.inr rfl⟩ h.symm ⟨Or.inr rfl, Or.inr rfl⟩
      (by simp [hv (by decide)])
  -- A crossing that skips a monochromatic block gives three neighbors of
  -- one blue edge, so the color-reversed Lemma 4.3 applies.
  have noFarLeft {x : V} (hx : C.color x = .red)
      (hxf : x ≠ f) (hxi : x ≠ i)
      (hcross : G.Adj g x ∨ G.Adj h x) : False := by
    apply noSwapped
    apply lemma4_3_of_three_neighbors C.swapSides
      (by simp [hg]) (by simp [hh]) hgh
      (by simp [hf]) (by simp [hi]) (by simp [hx])
      (hv (x := (5 : Fin 10)) (y := 8) (by decide)) hxf.symm hxi.symm
      (Or.inl hfg.symm) (Or.inr hhi) hcross
  have noFarRight {x : V} (hx : C.color x = .red)
      (hxb : x ≠ b) (hxe : x ≠ e)
      (hcross : G.Adj c x ∨ G.Adj d x) : False := by
    apply noSwapped
    apply lemma4_3_of_three_neighbors C.swapSides
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
  have hinduced : FormsInducedPath10 G a b c d e f g h i j := by
    refine ⟨hinj, ?_⟩
    intro x y
    fin_cases x <;> fin_cases y <;>
      simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hde, hef, hfg, hgh,
        hhi, hij, hac, had, hbd, hce, hcf, hdf, heg, heh, hfh, hgi,
        hgj, hhj, hag, hah, hbg, hbh, hci, hcj, hdi, hdj]
    all_goals first
      | exact redNonedge ha hb he hab (hv (by decide))
      | exact redNonedge ha hb hf hab (hv (by decide))
      | exact redNonedge ha hb hi hab (hv (by decide))
      | exact redNonedge ha hb hj hab (hv (by decide))
      | exact redNonedge hb ha he hab.symm (hv (by decide))
      | exact redNonedge hb ha hf hab.symm (hv (by decide))
      | exact redNonedge hb ha hi hab.symm (hv (by decide))
      | exact redNonedge hb ha hj hab.symm (hv (by decide))
      | exact redNonedge he hf ha hef (hv (by decide))
      | exact redNonedge he hf hb hef (hv (by decide))
      | exact redNonedge he hf hi hef (hv (by decide))
      | exact redNonedge he hf hj hef (hv (by decide))
      | exact redNonedge hf he ha hef.symm (hv (by decide))
      | exact redNonedge hf he hb hef.symm (hv (by decide))
      | exact redNonedge hf he hi hef.symm (hv (by decide))
      | exact redNonedge hf he hj hef.symm (hv (by decide))
      | exact redNonedge hi hj ha hij (hv (by decide))
      | exact redNonedge hi hj hb hij (hv (by decide))
      | exact redNonedge hi hj he hij (hv (by decide))
      | exact redNonedge hi hj hf hij (hv (by decide))
      | exact redNonedge hj hi ha hij.symm (hv (by decide))
      | exact redNonedge hj hi hb hij.symm (hv (by decide))
      | exact redNonedge hj hi he hij.symm (hv (by decide))
      | exact redNonedge hj hi hf hij.symm (hv (by decide))
      | exact blueNonedge hc hd hg hcd (hv (by decide))
      | exact blueNonedge hc hd hh hcd (hv (by decide))
      | exact blueNonedge hd hc hg hcd.symm (hv (by decide))
      | exact blueNonedge hd hc hh hcd.symm (hv (by decide))
      | exact blueNonedge hg hh hc hgh (hv (by decide))
      | exact blueNonedge hg hh hd hgh (hv (by decide))
      | exact blueNonedge hh hg hc hgh.symm (hv (by decide))
      | exact blueNonedge hh hg hd hgh.symm (hv (by decide))
  exact hresult (lemma4_5 C hinduced ha hb hc hd he hf hg hh hi hj)

end Subcubic
