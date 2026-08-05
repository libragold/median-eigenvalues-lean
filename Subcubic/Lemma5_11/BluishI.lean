import Subcubic.Lemma5_11.CaseBlueI
import Subcubic.NegativeTailReducerWitnesses

/-! Cases (3.2.2.1)--(3.2.2.3) of Lemma 5.11. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_11JKConfiguration (C : GoodColoring G)
    (a b c d e f : V) extends
    Lemma5_11IConfiguration C a b c d e f where
  j : V
  k : V
  hj : C.color j = .bluish
  hk : C.color k = .bluish
  hij : G.Adj i j
  hik : G.Adj i k
  hjc : j ≠ c
  hkc : k ≠ c
  hjk : j ≠ k
  hid' : ¬ G.Adj i d
  hih : ¬ G.Adj i h

theorem lemma5_11_bluish_i_cases
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_11IConfiguration C a b c d e f)
    (hOutsideBluish : ∀ z, G.Adj Q.i z → z ≠ c → z ≠ d →
      C.color z = .bluish) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_11JKConfiguration C a b c d e f) := by
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
  have hbeV : b ≠ e := by simpa using hv (x := (1 : Fin 6)) (y := 4) (by decide)
  have hcdV : c ≠ d := by simpa using hv (x := (2 : Fin 6)) (y := 3) (by decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all
  obtain ⟨x, y, hix, hiy, hxc, hyc, hxy⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hideg Q.hci.symm
  by_cases hid : G.Adj Q.i d
  · have choose : ∃ j, G.Adj Q.i j ∧ j ≠ c ∧ j ≠ d := by
      by_cases hxd : x = d
      · exact ⟨y, hiy, hyc, fun h => hxy (hxd.trans h.symm)⟩
      · exact ⟨x, hix, hxc, hxd⟩
    obtain ⟨j, hij, hjc, hjd⟩ := choose
    have hj := hOutsideBluish j hij hjc hjd
    by_cases hih : G.Adj Q.i Q.h
    · left
      have hie : ¬ G.Adj Q.i e :=
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
      have hia : ¬ G.Adj Q.i a :=
        C.reddish_not_adj_redSide Q.hi (Or.inl ha)
      have hea : ¬ G.Adj e a := by simpa using nonedge 4 0 (by native_decide)
      have hidBlue : ¬ G.Adj d Q.h :=
        C.bluish_not_adj_blueSide Q.hh (Or.inl hd) ∘ SimpleGraph.Adj.symm
      exact HasReachableNegativeReduction.of_current_ce C
        (containsCutEnhancerD_of C he Q.hi hd Q.hh ha hde.symm Q.heh
          hid hih Q.hha (fun h => hie h.symm) hea hia hidBlue
          (by simpa using nonedge 3 0 (by native_decide))
          (hv (x := (4 : Fin 6)) (y := 0) (by decide)))
    · left
      have hbi : ¬ G.Adj Q.i b :=
        C.reddish_not_adj_redSide Q.hi (Or.inl hb)
      have hie : ¬ G.Adj Q.i e :=
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
      have hbj : ¬ G.Adj b j := by
        apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
        · exact hv (x := (0 : Fin 6)) (y := 2) (by decide)
        · exact color_ne ha Q.hg (by decide)
        · exact color_ne hc Q.hg (by decide)
        · exact color_ne hj ha (by decide)
        · exact color_ne hj hc (by decide)
        · intro h; subst j; exact Q.hig hij
      have hej : ¬ G.Adj e j := by
        apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        · exact hv (x := (5 : Fin 6)) (y := 3) (by decide)
        · exact color_ne hf Q.hh (by decide)
        · exact color_ne hd Q.hh (by decide)
        · exact color_ne hj hf (by decide)
        · exact color_ne hj hd (by decide)
        · intro h; subst j; exact hih hij
      apply HasReachableNegativeReduction.of_current_ntr C
      apply containsNegativeQ C Q.hi hb he hj hc hd Q.hg Q.hh
        hij Q.hci.symm hid hbc Q.hbg hde.symm Q.heh hcd
        hbi hie Q.hig hih
        (by simpa using nonedge 1 4 (by native_decide)) hbj
        (fun h => Q.hhb h.symm) hej (fun h => Q.hge h.symm)
      have hjg : j ≠ Q.g := by intro h; subst j; exact Q.hig hij
      have hjh : j ≠ Q.h := by intro h; subst j; exact hih hij
      have hgh : Q.g ≠ Q.h := by
        intro h
        apply Q.hhb
        simpa [h] using Q.hbg.symm
      simp [color_ne Q.hi hb (by decide), color_ne Q.hi he (by decide),
        color_ne Q.hi hj (by decide), color_ne Q.hi hc (by decide),
        color_ne Q.hi hd (by decide), color_ne Q.hi Q.hg (by decide),
        color_ne Q.hi Q.hh (by decide),
        hbeV,
        color_ne hb hj (by decide), color_ne hb hc (by decide),
        color_ne hb hd (by decide), color_ne hb Q.hg (by decide),
        color_ne hb Q.hh (by decide), color_ne he hj (by decide),
        color_ne he hc (by decide), color_ne he hd (by decide),
        color_ne he Q.hg (by decide), color_ne he Q.hh (by decide),
        color_ne hj hc (by decide), color_ne hj hd (by decide), hjg, hjh,
        hcdV,
        color_ne hc Q.hg (by decide), color_ne hc Q.hh (by decide),
        color_ne hd Q.hg (by decide), color_ne hd Q.hh (by decide), hgh]
  · by_cases hih : G.Adj Q.i Q.h
    · have choose : ∃ j, G.Adj Q.i j ∧ j ≠ c ∧ j ≠ Q.h := by
        by_cases hxh : x = Q.h
        · exact ⟨y, hiy, hyc, fun h => hxy (hxh.trans h.symm)⟩
        · exact ⟨x, hix, hxc, hxh⟩
      obtain ⟨j, hij, hjc, hjh⟩ := choose
      have hjd : j ≠ d := by intro h; subst j; exact hid hij
      have hj := hOutsideBluish j hij hjc hjd
      have hie : ¬ G.Adj Q.i e :=
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
      have hbi : ¬ G.Adj Q.i b :=
        C.reddish_not_adj_redSide Q.hi (Or.inl hb)
      have hej : ¬ G.Adj e j := by
        apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.heh
        · exact hv (x := (5 : Fin 6)) (y := 3) (by decide)
        · exact color_ne hf Q.hh (by decide)
        · exact color_ne hd Q.hh (by decide)
        · exact color_ne hj hf (by decide)
        · exact color_ne hj hd (by decide)
        · exact hjh
      have hbj : ¬ G.Adj b j := by
        apply C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
        · exact hv (x := (0 : Fin 6)) (y := 2) (by decide)
        · exact color_ne ha Q.hg (by decide)
        · exact color_ne hc Q.hg (by decide)
        · exact color_ne hj ha (by decide)
        · exact color_ne hj hc (by decide)
        · intro h; subst j; exact Q.hig hij
      have hbd : ¬ G.Adj b d := by
        simpa using nonedge 1 3 (by native_decide)
      apply Or.inl
      apply HasReachableNegativeReduction.of_current_ntr C
      apply containsNegativeP C Q.hi he hb hj Q.hh hc hd Q.hg
        hij hih Q.hci.symm Q.heh hde.symm hbc Q.hbg hcd
        hie hbi hid Q.hig
        (by simpa using nonedge 4 1 (by native_decide)) hej
        (fun h => Q.hge h.symm) hbj (fun h => Q.hhb h.symm) hbd
      have hjg : j ≠ Q.g := by intro h; subst j; exact Q.hig hij
      have hgh : Q.h ≠ Q.g := by
        intro h
        apply Q.hhb
        simpa [h] using Q.hbg.symm
      simp [hbeV.symm, hcdV, hjh, hjg, hgh,
        color_ne Q.hi he (by decide), color_ne Q.hi hb (by decide),
        color_ne Q.hi hj (by decide), color_ne Q.hi Q.hh (by decide),
        color_ne Q.hi hc (by decide), color_ne Q.hi hd (by decide),
        color_ne Q.hi Q.hg (by decide), color_ne he hj (by decide),
        color_ne he Q.hh (by decide), color_ne he hc (by decide),
        color_ne he hd (by decide), color_ne he Q.hg (by decide),
        color_ne hb hj (by decide), color_ne hb Q.hh (by decide),
        color_ne hb hc (by decide), color_ne hb hd (by decide),
        color_ne hb Q.hg (by decide), color_ne hj hc (by decide),
        color_ne hj hd (by decide), color_ne Q.hh hc (by decide),
        color_ne Q.hh hd (by decide), color_ne hc Q.hg (by decide),
        color_ne hd Q.hg (by decide)]
    · have hxd : x ≠ d := by intro h; subst x; exact hid hix
      have hyd : y ≠ d := by intro h; subst y; exact hid hiy
      have hx := hOutsideBluish x hix hxc hxd
      have hy := hOutsideBluish y hiy hyc hyd
      exact Or.inr ⟨⟨Q, x, y, hx, hy, hix, hiy, hxc, hyc, hxy,
        hid, hih⟩⟩

end Subcubic
