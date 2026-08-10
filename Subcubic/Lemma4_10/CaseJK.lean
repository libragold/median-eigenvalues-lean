import Subcubic.Lemma4_10.BluishI

/-! Cases (3.2.2.3.1)--(3.2.2.3.2) of Lemma 4.10. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_10JConfiguration (C : GoodColoring G)
    (a b c d e f : V) extends
    Lemma4_10JKConfiguration C a b c d e f where
  hja : G.Adj j a

theorem lemma4_10_jk_cases
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (_he : C.color e = .red) (_hf : C.color f = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma4_10JKConfiguration C a b c d e f) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_10JConfiguration C a b c d e f) := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact Or.inl hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) := hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    (hedge x y).mp hxy
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have habV : a ≠ b := by simpa using hv (x := (0 : Fin 6)) (y := 1) (by decide)
  have hcdV : c ≠ d := by simpa using hv (x := (2 : Fin 6)) (y := 3) (by decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all
  by_cases hja : G.Adj Q.j a
  · exact Or.inr ⟨⟨Q, hja⟩⟩
  · by_cases hka : G.Adj Q.k a
    · let Q' : Lemma4_10JKConfiguration C a b c d e f := {
        toLemma4_10IConfiguration := Q.toLemma4_10IConfiguration
        j := Q.k
        k := Q.j
        hj := Q.hk
        hk := Q.hj
        hij := Q.hik
        hik := Q.hij
        hjc := Q.hkc
        hkc := Q.hjc
        hjk := Q.hjk.symm
        hid' := Q.hid'
        hih := Q.hih }
      exact Or.inr ⟨⟨Q', hka⟩⟩
    · have hbh : b ≠ Q.h := color_ne hb Q.hh (by decide)
      obtain ⟨l, hal, hlb, hlh⟩ :=
        C.exists_third_neighbor (degree_of_color (Or.inl ha)) hbh
      have hlSide := C.other_neighbor_of_red_is_blueSide ha hb hab hal hlb
      have hl : C.color l = .bluish := by
        rcases hlSide with hl | hl
        · exact (hNoBlueAtA l hal hl).elim
        · exact hl
      have hil : ¬ G.Adj Q.i l := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic
          Q.hci.symm Q.hij Q.hik
        · exact Q.hjc.symm
        · exact Q.hkc.symm
        · exact Q.hjk
        · exact color_ne hl hc (by decide)
        · intro h; subst l; exact hja hal.symm
        · intro h; subst l; exact hka hal.symm
      apply Or.inl
      apply HasReachableReduction.of_current_ptr C
      apply containsPositiveU C Q.hi ha hb Q.hj Q.hk Q.hh hl hc hd Q.hg
        Q.hij Q.hik Q.hci.symm hab Q.hha.symm hal hbc Q.hbg hcd
        Q.hih hil Q.hid' Q.hig
      have hjh : Q.j ≠ Q.h := by
        intro h; apply Q.hih; simpa [h] using Q.hij
      have hkh : Q.k ≠ Q.h := by
        intro h; apply Q.hih; simpa [h] using Q.hik
      have hjl : Q.j ≠ l := by
        intro h; apply hja; simpa [h] using hal.symm
      have hkl : Q.k ≠ l := by
        intro h; apply hka; simpa [h] using hal.symm
      have hjg : Q.j ≠ Q.g := by
        intro h; apply Q.hig; simpa [h] using Q.hij
      have hkg : Q.k ≠ Q.g := by
        intro h; apply Q.hig; simpa [h] using Q.hik
      have hhg : Q.h ≠ Q.g := by
        intro h
        apply Q.hhb
        simpa [h] using Q.hbg.symm
      have hlg : l ≠ Q.g := by intro h; subst l; exact Q.hga hal.symm
      simp [color_ne Q.hi ha (by decide), color_ne Q.hi hb (by decide),
        color_ne Q.hi Q.hj (by decide), color_ne Q.hi Q.hk (by decide),
        color_ne Q.hi Q.hh (by decide), color_ne Q.hi hl (by decide),
        color_ne Q.hi hc (by decide), color_ne Q.hi hd (by decide),
        color_ne Q.hi Q.hg (by decide), habV,
        color_ne ha Q.hj (by decide), color_ne ha Q.hk (by decide),
        color_ne ha Q.hh (by decide), color_ne ha hl (by decide),
        color_ne ha hc (by decide), color_ne ha hd (by decide),
        color_ne ha Q.hg (by decide), color_ne hb Q.hj (by decide),
        color_ne hb Q.hk (by decide), color_ne hb Q.hh (by decide),
        color_ne hb hl (by decide), color_ne hb hc (by decide),
        color_ne hb hd (by decide), color_ne hb Q.hg (by decide),
        Q.hjk, hjh, hjl, hjg, hkh, hkl, hkg, hlh.symm, hhg, hlg,
        color_ne Q.hj hc (by decide), color_ne Q.hj hd (by decide),
        color_ne Q.hk hc (by decide), color_ne Q.hk hd (by decide),
        color_ne Q.hh hc (by decide), color_ne Q.hh hd (by decide),
        color_ne hl hc (by decide), color_ne hl hd (by decide),
        color_ne hc Q.hg (by decide), color_ne hd Q.hg (by decide), hcdV]

end Subcubic
