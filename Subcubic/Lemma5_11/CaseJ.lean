import Subcubic.Lemma5_11.CaseJK

/-! Lemma 5.11, Case (3.2.2.3.2): one bluish neighbor of `i` meets `a`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_11_case_j_adj_a
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_11JConfiguration C a b c d e f) :
    HasReachableNegativeReduction C := by
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
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all
  have hih := Q.hih
  have hid := Q.hid'
  have hig := Q.hig
  have habV : a ≠ b := hv (x := (0 : Fin 6)) (y := 1) (by decide)
  have hkj : Q.k ≠ Q.j := Q.hjk.symm
  have hcdV : c ≠ d := hv (x := (2 : Fin 6)) (y := 3) (by decide)
  have hn : [Q.i, a, b, Q.k, Q.j, Q.h, c, d, Q.g].Nodup := by
    have hjh : Q.j ≠ Q.h := by
      intro h; apply hih; simpa [h] using Q.hij
    have hkh : Q.k ≠ Q.h := by
      intro h; apply hih; simpa [h] using Q.hik
    have hjg : Q.j ≠ Q.g := by
      intro h; apply hig; simpa [h] using Q.hij
    have hkg : Q.k ≠ Q.g := by
      intro h; apply hig; simpa [h] using Q.hik
    have hhg : Q.h ≠ Q.g := by
      intro h
      apply Q.hhb
      simpa [h] using Q.hbg.symm
    simp [habV, hkj, hcdV, hjh, hkh, hjg, hkg, hhg,
      color_ne Q.hi ha (by decide), color_ne Q.hi hb (by decide),
      color_ne Q.hi Q.hj (by decide), color_ne Q.hi Q.hk (by decide),
      color_ne Q.hi Q.hh (by decide), color_ne Q.hi hc (by decide),
      color_ne Q.hi hd (by decide), color_ne Q.hi Q.hg (by decide),
      color_ne ha Q.hj (by decide), color_ne ha Q.hk (by decide),
      color_ne ha Q.hh (by decide), color_ne ha hc (by decide),
      color_ne ha hd (by decide), color_ne ha Q.hg (by decide),
      color_ne hb Q.hj (by decide), color_ne hb Q.hk (by decide),
      color_ne hb Q.hh (by decide), color_ne hb hc (by decide),
      color_ne hb hd (by decide), color_ne hb Q.hg (by decide),
      color_ne Q.hj hc (by decide), color_ne Q.hj hd (by decide),
      color_ne Q.hk hc (by decide), color_ne Q.hk hd (by decide),
      color_ne Q.hh hc (by decide), color_ne Q.hh hd (by decide),
      color_ne hc Q.hg (by decide), color_ne hd Q.hg (by decide)]
  apply HasReachableNegativeReduction.of_current_ntr C
  apply containsNegativeAa C Q.hi ha hb Q.hk Q.hj Q.hh hc hd Q.hg
    Q.hik Q.hij Q.hci.symm hab Q.hja.symm Q.hha.symm hbc Q.hbg hcd
    hih hid hig hn

end Subcubic
