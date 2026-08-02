import Subcubic.Lemma4_12.Case3NoShare

/-! The shared-reddish-neighbor cases of Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Case (3.1.1): the shared reddish neighbor has no blue neighbor other
than `d`.  Degree two gives `m-minus+`; degree three gives `m+`. -/
theorem lemma4_12_case3_shared_no_other_blue
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma4_12CoreConfiguration C a b c d)
    {g : V} (hg : C.color g = .reddish)
    (heg : G.Adj Q.e g) (hdg : G.Adj d g)
    (hNoOtherBlue : ∀ z, G.Adj g z → C.color z = .blue → z = d) :
    HasReachableReduction C := by
  classical
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
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h; subst y; simp_all
  have hgc : ¬ G.Adj g c := fun h =>
    (hv (x := (2 : Fin 4)) (y := 3) (by decide))
      (hNoOtherBlue c h hc)
  have hgb : ¬ G.Adj g b :=
    C.reddish_not_adj_redSide hg (Or.inl hb)
  have hge : g ≠ Q.e := heg.ne.symm
  have hgd : g ≠ d := hdg.ne.symm
  have hed : Q.e ≠ d := by
    exact color_ne Q.he hd (by decide)
  have lower : 2 ≤ vertexDegree G g := by
    have hs : ({Q.e, d} : Set V) ⊆ G.neighborSet g := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact heg.symm
      · exact hdg.symm
    unfold vertexDegree
    simpa [hed] using Set.ncard_le_ncard hs
  by_cases hgdeg2 : vertexDegree G g = 2
  · apply HasReachableReduction.of_current_ptr C
    apply containsPositiveMMinus C (a := g) (b := b) (c := Q.e)
      (d := d) (e := c) hg hb Q.he hd hc hgdeg2 heg.symm hdg.symm
      Q.hbe hbc hcd.symm hgb hgc hbd
    simp [List.nodup_cons, color_ne hg hb (by decide),
      color_ne hg hc (by decide), color_ne hb Q.he (by decide),
      color_ne hb hd (by decide), hge, hgd, hbc.ne, Q.hec,
      hcd.ne.symm, hed]
  · have hgdeg3 : vertexDegree G g = 3 := by
      have upper := C.subcubic g
      omega
    obtain ⟨x, y, hgx, hgy, hxd, hyd, hxy⟩ :=
      exists_two_other_neighbors_of_degree_three hgdeg3 hdg.symm
    obtain ⟨h, hgh, hhd, hhe⟩ :
        ∃ h, G.Adj g h ∧ h ≠ d ∧ h ≠ Q.e := by
      by_cases hxe : x = Q.e
      · refine ⟨y, hgy, hyd, ?_⟩
        intro hye
        apply hxy
        simp [hxe, hye]
      · exact ⟨x, hgx, hxd, hxe⟩
    have hh : C.color h = .bluish := by
      cases hh' : C.color h with
      | red => exact (C.reddish_not_adj_redSide hg (Or.inl hh') hgh).elim
      | reddish => exact (C.reddish_not_adj_redSide hg (Or.inr hh') hgh).elim
      | blue => exact (hhd (hNoOtherBlue h hgh hh')).elim
      | bluish => exact rfl
    have hbh : ¬ G.Adj b h := by
      apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbe
      · exact hv (x := (0 : Fin 4)) (y := 2) (by decide)
      · exact Q.hea.symm
      · exact Q.hec.symm
      · intro h; subst h; simp_all
      · exact (by intro h; subst h; simp_all)
      · exact (by intro h; subst h; simp_all)
    apply HasReachableReduction.of_current_ptr C
    apply containsPositiveM C (a := g) (b := b) (c := h) (d := Q.e)
      (e := d) (f := c) hg hb hh Q.he hd hc hgh heg.symm hdg.symm
      Q.hbe hbc hcd.symm hgb hgc hbh hbd
    simp [List.nodup_cons, color_ne hg hb (by decide),
      color_ne hg hc (by decide), color_ne hb hh (by decide),
      color_ne hb Q.he (by decide), color_ne hb hd (by decide),
      color_ne hb hc (by decide), color_ne hh hc (by decide),
      hgh.ne, hge, hgd, hhe, hhd, Q.hec, hcd.ne.symm, hed]

/-- The data at the start of Case (3.1.2): `g` is a shared reddish
neighbor of `e,d`, and its additional blue neighbor `h` lies on a blue edge
`hi`. -/
structure Lemma4_12SharedBlueConfiguration (C : GoodColoring G)
    (a b c d : V) extends Lemma4_12CoreConfiguration C a b c d where
  g : V
  h : V
  i : V
  hg : C.color g = .reddish
  hh : C.color h = .blue
  hi : C.color i = .blue
  heg : G.Adj e g
  hdg : G.Adj d g
  hgh : G.Adj g h
  hhi : G.Adj h i
  hhd : h ≠ d

/-- Split the shared-neighbor case exactly as in Cases (3.1.1) and
(3.1.2) of the prose proof. -/
theorem lemma4_12_case3_shared_setup
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma4_12CoreConfiguration C a b c d)
    {g : V} (hg : C.color g = .reddish)
    (heg : G.Adj Q.e g) (hdg : G.Adj d g) :
    HasReachableReduction C ∨
      ∃ R : Lemma4_12SharedBlueConfiguration C a b c d,
        R.toLemma4_12CoreConfiguration = Q := by
  classical
  by_cases hNoOtherBlue :
      ∀ z, G.Adj g z → C.color z = .blue → z = d
  · exact Or.inl (lemma4_12_case3_shared_no_other_blue C hpath ha hb hc hd
      Q hg heg hdg hNoOtherBlue)
  · push Not at hNoOtherBlue
    obtain ⟨h, hgh, hh, hhd⟩ := hNoOtherBlue
    have hhCorrect := C.color_correct h
    rw [hh] at hhCorrect
    obtain ⟨_, i, hiSide, hhi⟩ := hhCorrect
    have hiSide' := (C.not_mem_redSide_iff i).1 hiSide
    have hi : C.color i = .blue := by
      rcases hiSide' with hi | hi
      · exact hi
      · exact (C.bluish_not_adj_blueSide hi (Or.inl hh) hhi.symm).elim
    exact Or.inr ⟨⟨Q, g, h, i, hg, hh, hi, heg, hdg, hgh, hhi, hhd⟩, rfl⟩

/-- Case (3.1.2.1): if neither endpoint of the blue edge `hi` has a red
neighbor, the color-reversed form of Lemma 4.4 applies. -/
theorem lemma4_12_case3_shared_blue_isolated
    (C : GoodColoring G) {a b c d : V}
    (R : Lemma4_12SharedBlueConfiguration C a b c d)
    (hNoRedH : ∀ z, G.Adj R.h z → C.color z ≠ .red)
    (hNoRedI : ∀ z, G.Adj R.i z → C.color z ≠ .red) :
    HasReachableReduction C := by
  have hOtherH : ∀ z, G.Adj R.h z → z ≠ R.i →
      C.swapSides.color z = .bluish := by
    intro z hhz hzi
    have hzSide := C.other_neighbor_of_blue_is_redSide
      R.hh R.hi R.hhi hhz hzi
    rcases hzSide with hz | hz
    · exact (hNoRedH z hhz hz).elim
    · simp [GoodColoring.swapSides, hz]
  have hOtherI : ∀ z, G.Adj R.i z → z ≠ R.h →
      C.swapSides.color z = .bluish := by
    intro z hiz hzh
    have hzSide := C.other_neighbor_of_blue_is_redSide
      R.hi R.hh R.hhi.symm hiz hzh
    rcases hzSide with hz | hz
    · exact (hNoRedI z hiz hz).elim
    · simp [GoodColoring.swapSides, hz]
  apply HasReachableReduction.of_current_ptr C
  apply (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
  exact lemma4_4 C.swapSides (by simp [R.hh]) (by simp [R.hi])
    R.hhi hOtherH hOtherI

end Subcubic
