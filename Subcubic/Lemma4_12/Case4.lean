import Subcubic.Lemma4_12.Case1

/-! Case (4.2) of Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_12RedGConfiguration (C : GoodColoring G)
    (a b c d : V) extends Lemma4_12ThirdNeighborConfiguration C a b c d where
  g : V
  h : V
  hg : C.color g = .red
  hh : C.color h = .red
  heg : G.Adj e g
  hgh : G.Adj g h
  hga : g ≠ a
  hgb : g ≠ b

/-- If the third neighbor `g` of `e` in Case (4) is reddish, reducers `o+`
or `q+` apply (with colors reversed). -/
theorem lemma4_12_case4_reddish
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma4_12ThirdNeighborConfiguration C a b c d)
    {g : V} (hg : C.color g = .reddish) (heg : G.Adj Q.e g)
    (hga : g ≠ a) (hgb : g ≠ b)
    (hea : G.Adj Q.e a) (hfd : G.Adj Q.f d)
    (hef : ¬ G.Adj Q.e Q.f) : HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
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
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h; subst y; simp_all
  have hgf : g ≠ Q.f := by intro h; subst g; exact hef heg
  by_cases hgd : G.Adj g d
  · apply HasReachableReduction.of_current_ptr C
    apply (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
    apply containsPositiveO C.swapSides (a := Q.e) (b := c) (c := d)
      (d := a) (e := b) (f := g) (g := Q.f)
      (by simp [Q.he]) (by simp [hc]) (by simp [hd])
      (by simp [ha]) (by simp [hb]) (by simp [hg]) (by simp [Q.hf])
      hea Q.hbe.symm heg hcd hbc.symm Q.hcf hgd.symm hfd.symm hab
      hef
    simp [List.nodup_cons, color_ne Q.he hc (by decide),
      color_ne Q.he hd (by decide), color_ne Q.he ha (by decide),
      color_ne Q.he hb (by decide), color_ne Q.he hg (by decide),
      color_ne Q.he Q.hf (by decide), hcd.ne, hab.ne, hga.symm, hgb.symm,
      hgf, color_ne hc ha (by decide), color_ne hc hb (by decide),
      color_ne hc hg (by decide), color_ne hc Q.hf (by decide),
      color_ne hd ha (by decide), color_ne hd hb (by decide),
      color_ne hd hg (by decide), color_ne hd Q.hf (by decide),
      color_ne ha Q.hf (by decide), color_ne hb Q.hf (by decide)]
  · obtain ⟨k, hdk, hkc, hkf⟩ :=
      C.exists_third_neighbor (degreeC (Or.inr hd))
        (color_ne hc Q.hf (by decide))
    have hkSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdk hkc
    have hk : C.color k = .reddish := by
      rcases hkSide with hk | hk
      · exact (hNoRedAtD k hdk hk).elim
      · exact hk
    have hkg : k ≠ g := by intro h; subst k; exact hgd hdk.symm
    have hek : ¬ G.Adj Q.e k := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hedeg Q.hbe.symm hea heg
      · exact hab.ne.symm
      · exact hgb.symm
      · exact hga.symm
      · exact color_ne hk hb (by decide)
      · exact color_ne hk ha (by decide)
      · exact hkg
    apply HasReachableReduction.of_current_ptr C
    apply (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
    apply containsPositiveQ C.swapSides (a := Q.e) (b := c) (c := d)
      (d := g) (e := a) (f := b) (g := Q.f) (h := k)
      (by simp [Q.he]) (by simp [hc]) (by simp [hd]) (by simp [hg])
      (by simp [ha]) (by simp [hb]) (by simp [Q.hf]) (by simp [hk])
      heg hea Q.hbe.symm hcd hbc.symm Q.hcf hfd.symm hdk hab hef hek
    simp [List.nodup_cons, color_ne Q.he hc (by decide),
      color_ne Q.he hd (by decide), color_ne Q.he hg (by decide),
      color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
      color_ne Q.he Q.hf (by decide), color_ne Q.he hk (by decide),
      hcd.ne, hab.ne, hgf,
      color_ne hc hg (by decide), color_ne hc ha (by decide),
      color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
      color_ne hc hk (by decide), color_ne hd hg (by decide),
      color_ne hd ha (by decide), color_ne hd hb (by decide),
      color_ne hd Q.hf (by decide), color_ne hd hk (by decide),
      color_ne hg ha (by decide), color_ne hg hb (by decide), hkg.symm,
      color_ne ha Q.hf (by decide), color_ne ha hk (by decide),
      color_ne hb Q.hf (by decide), color_ne hb hk (by decide), hkf.symm]

/-- Split Case (4) according to the color of the third neighbor of `e`. -/
theorem lemma4_12_case4_split
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma4_12ThirdNeighborConfiguration C a b c d)
    (hea : G.Adj Q.e a) (hfd : G.Adj Q.f d)
    (hef : ¬ G.Adj Q.e Q.f) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_12RedGConfiguration C a b c d) := by
  classical
  obtain ⟨x, y, hex, hey, hxb, hyb, hxy⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hedeg Q.hbe.symm
  obtain ⟨g, heg, hga, hgb⟩ :
      ∃ g, G.Adj Q.e g ∧ g ≠ a ∧ g ≠ b := by
    by_cases hxa : x = a
    · refine ⟨y, hey, ?_, hyb⟩
      intro hya
      apply hxy
      simp [hxa, hya]
    · exact ⟨x, hex, hxa, hxb⟩
  cases hg : C.color g with
  | red =>
      have hgCorrect := C.color_correct g
      rw [hg] at hgCorrect
      obtain ⟨_, h, hhSide, hgh⟩ := hgCorrect
      have hhSide' := (C.mem_redSide_iff h).1 hhSide
      have hh : C.color h = .red := by
        rcases hhSide' with hh | hh
        · exact hh
        · exact (C.reddish_not_adj_redSide hh (Or.inl hg) hgh.symm).elim
      exact Or.inr ⟨⟨Q, g, h, hg, hh, heg, hgh, hga, hgb⟩⟩
  | reddish =>
      exact Or.inl (lemma4_12_case4_reddish C hpath ha hb hc hd
        hNoRedAtD Q hg heg hga hgb hea hfd hef)
  | blue =>
      exact (C.bluish_not_adj_blueSide Q.he (Or.inl hg) heg).elim
  | bluish =>
      exact (C.bluish_not_adj_blueSide Q.he (Or.inr hg) heg).elim

end Subcubic
