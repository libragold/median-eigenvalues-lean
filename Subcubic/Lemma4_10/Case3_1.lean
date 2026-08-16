import Subcubic.Lemma4_10.Cases1And2Setup3

/-! Case (3.1) of Lemma 4.10. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_10Case3_2Configuration (C : MatchingCutColoring G)
    (a b c d e f : V) extends
    Lemma4_10Case3Configuration C a b c d e f where
  hga : ¬ G.Adj g a
  hhf : ¬ G.Adj h f

theorem lemma4_10_case_3_1
    (C : MatchingCutColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma4_10Case3Configuration C a b c d e f) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_10Case3_2Configuration C a b c d e f) := by
  classical
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
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have habV : a ≠ b := by simpa using hv (x := (0 : Fin 6)) (y := 1) (by decide)
  have haeV : a ≠ e := by simpa using hv (x := (0 : Fin 6)) (y := 4) (by decide)
  have hbeV : b ≠ e := by simpa using hv (x := (1 : Fin 6)) (y := 4) (by decide)
  have hcdV : c ≠ d := by simpa using hv (x := (2 : Fin 6)) (y := 3) (by decide)
  have hfeV : f ≠ e := by simpa using hv (x := (5 : Fin 6)) (y := 4) (by decide)
  have hfbV : f ≠ b := by simpa using hv (x := (5 : Fin 6)) (y := 1) (by decide)
  have hebV : e ≠ b := by simpa using hv (x := (4 : Fin 6)) (y := 1) (by decide)
  have hdcV : d ≠ c := by simpa using hv (x := (3 : Fin 6)) (y := 2) (by decide)
  have hec : ¬ G.Adj e c := by simpa using nonedge 4 2 (by native_decide)
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all
  by_cases hga : G.Adj Q.g a
  · left
    apply HasReachableReduction.of_current_ptr C
    apply containsPositiveN C ha hb he Q.hg Q.hh hc hd
      hab hga.symm Q.hha.symm Q.hbg hbc Q.heh hde.symm hcd
      (fun h => Q.hge h.symm) hec
    have hgh : Q.g ≠ Q.h := by
      intro h
      apply Q.hhb
      simpa [h] using Q.hbg.symm
    simp [habV, haeV, hbeV, hgh, hcdV,
      color_ne ha Q.hg (by decide), color_ne ha Q.hh (by decide),
      color_ne ha hc (by decide), color_ne ha hd (by decide),
      color_ne hb Q.hg (by decide), color_ne hb Q.hh (by decide),
      color_ne hb hc (by decide), color_ne hb hd (by decide),
      color_ne he Q.hg (by decide), color_ne he Q.hh (by decide),
      color_ne he hc (by decide), color_ne he hd (by decide),
      color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
      color_ne Q.hh hc (by decide), color_ne Q.hh hd (by decide)]
  · by_cases hhf : G.Adj Q.h f
    · left
      apply HasReachableReduction.of_current_ptr C
      apply containsPositiveN C hf he hb Q.hh Q.hg hd hc
        hef.symm hhf.symm Q.hgf.symm Q.heh hde.symm Q.hbg hbc hcd.symm
        (fun h => Q.hhb h.symm) hbd
      have hhg : Q.h ≠ Q.g := by
        intro h
        apply Q.hhb
        simpa [h] using Q.hbg.symm
      simp [hfeV, hfbV, hebV, hhg, hdcV,
        color_ne hf Q.hh (by decide), color_ne hf Q.hg (by decide),
        color_ne hf hd (by decide), color_ne hf hc (by decide),
        color_ne he Q.hh (by decide), color_ne he Q.hg (by decide),
        color_ne he hd (by decide), color_ne he hc (by decide),
        color_ne hb Q.hh (by decide), color_ne hb Q.hg (by decide),
        color_ne hb hd (by decide), color_ne hb hc (by decide),
        color_ne Q.hh hd (by decide), color_ne Q.hh hc (by decide),
        color_ne Q.hg hd (by decide), color_ne Q.hg hc (by decide)]
    · exact Or.inr ⟨⟨Q, hga, hhf⟩⟩

end Subcubic
