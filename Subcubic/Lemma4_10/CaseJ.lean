import Subcubic.Lemma4_10.CaseJK

/-! Cases (3.2.2.3.2.1)--(3.2.2.3.2.3) of Lemma 4.10. -/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_10OtherRedConfiguration (C : MatchingCutColoring G)
    (a b c d e f : V) extends
    Lemma4_10JConfiguration C a b c d e f where
  l : V
  hl : C.color l = .red
  hjl : G.Adj j l
  hla : l ≠ a
  hjf : ¬ G.Adj j f

theorem lemma4_10_j_cases
    (C : MatchingCutColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (_he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma4_10JConfiguration C a b c d e f) :
    HasReachableReduction C ∨
      ∃ l, C.color l = .red ∧ G.Adj Q.j l ∧ l ≠ a ∧ ¬ G.Adj Q.j f := by
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
  have habV : a ≠ b := by
    simpa using hv (x := (0 : Fin 6)) (y := 1) (by decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro h
    subst y
    simp_all
  by_cases hjf : G.Adj Q.j f
  · left
    have haf : ¬ G.Adj a f := by simpa using nonedge 0 5 (by native_decide)
    have hafV : a ≠ f := by
      simpa using hv (x := (0 : Fin 6)) (y := 5) (by decide)
    have hfh : ¬ G.Adj f Q.h := fun h => Q.hhf h.symm
    apply HasReachableReduction.of_current_ptr C
    apply containsPositiveG C ha hf Q.hh Q.hj Q.hg Q.hha.symm Q.hja.symm
      hjf.symm Q.hgf.symm haf (by simpa [SimpleGraph.adj_comm] using Q.hga) hfh
    have hhj : Q.h ≠ Q.j := by
      intro h; apply Q.hih; simpa [h] using Q.hij
    have hhg : Q.h ≠ Q.g := by
      intro h; apply Q.hhb; simpa [h] using Q.hbg.symm
    have hjg : Q.j ≠ Q.g := by
      intro h; apply Q.hig; simpa [h] using Q.hij
    simp [hafV, color_ne ha Q.hh (by decide), color_ne ha Q.hj (by decide),
      color_ne ha Q.hg (by decide), color_ne hf Q.hh (by decide),
      color_ne hf Q.hj (by decide), color_ne hf Q.hg (by decide),
      hhj, hhg, hjg]
  · by_cases hother : ∃ l, G.Adj Q.j l ∧ C.color l = .red ∧ l ≠ a
    · obtain ⟨l, hjl, hl, hla⟩ := hother
      exact Or.inr ⟨l, hl, hjl, hla, hjf⟩
    · have hother' : ∀ l, G.Adj Q.j l → C.color l = .red → l = a := by
        intro l hjl hl
        by_contra hla
        exact hother ⟨l, hjl, hl, hla⟩
      have hia : Q.i ≠ a := color_ne Q.hi ha (by decide)
      by_cases hjdeg2 : vertexDegree G Q.j = 2
      · have hjc : ¬ G.Adj Q.j c :=
          C.bluish_not_adj_blueSide Q.hj (Or.inl hc)
        have hjb : ¬ G.Adj Q.j b := by
          simpa [SimpleGraph.adj_comm] using
            C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
              (hv (x := (0 : Fin 6)) (y := 2) (by decide))
              (color_ne ha Q.hg (by decide))
              (color_ne hc Q.hg (by decide))
              (color_ne Q.hj ha (by decide))
              (color_ne Q.hj hc (by decide))
              (by intro h; apply Q.hig; simpa [h] using Q.hij)
        have hca : ¬ G.Adj c a := by simpa using nonedge 2 0 (by native_decide)
        have hptrSwap := containsPositiveDcA C.swapSides
          (a := Q.j) (b := c) (c := Q.i) (d := a) (e := b)
          (by simp [Q.hj]) (by simp [hc]) (by simp [Q.hi])
          (by simp [ha]) (by simp [hb]) hjdeg2 Q.hij.symm Q.hja
          Q.hci hbc.symm hab hjc hjb hca
          (by
            simp [color_ne Q.hj hc (by decide), color_ne Q.hj Q.hi (by decide),
              color_ne Q.hj ha (by decide), color_ne Q.hj hb (by decide),
              color_ne hc Q.hi (by decide), color_ne hc ha (by decide),
              color_ne hc hb (by decide), color_ne Q.hi ha (by decide),
              color_ne Q.hi hb (by decide), habV])
        exact Or.inl (HasReachableReduction.of_current_ptr C
          ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptrSwap))
      · have lower : 2 ≤ vertexDegree G Q.j := by
          have hsubset : ({Q.i, a} : Set V) ⊆ G.neighborSet Q.j := by
            intro z hz
            simp only [mem_insert_iff, mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact Q.hij.symm
            · exact Q.hja
          unfold vertexDegree
          have hle := Set.ncard_le_ncard hsubset
          simpa [hia] using hle
        have hjdeg3 : vertexDegree G Q.j = 3 := by
          have upper := C.subcubic Q.j
          omega
        obtain ⟨x, y, hjx, hjy, hxi, hyi, hxy⟩ :=
          exists_two_other_neighbors_of_degree_three hjdeg3 Q.hij.symm
        have choose : ∃ l, G.Adj Q.j l ∧ l ≠ Q.i ∧ l ≠ a := by
          by_cases hxa : x = a
          · exact ⟨y, hjy, hyi, fun h => hxy (hxa.trans h.symm)⟩
          · exact ⟨x, hjx, hxi, hxa⟩
        obtain ⟨l, hjl, hli, hla⟩ := choose
        have hl : C.color l = .reddish := by
          cases hlc : C.color l with
          | red => exact (hla (hother' l hjl hlc)).elim
          | reddish => exact rfl
          | blue => exact (C.bluish_not_adj_blueSide Q.hj (Or.inl hlc) hjl).elim
          | bluish => exact (C.bluish_not_adj_blueSide Q.hj (Or.inr hlc) hjl).elim
        have hjc : ¬ G.Adj Q.j c :=
          C.bluish_not_adj_blueSide Q.hj (Or.inl hc)
        have hjb : ¬ G.Adj Q.j b := by
          simpa [SimpleGraph.adj_comm] using
            C.not_adj_fourth_neighbor (Or.inl hb) hab.symm hbc Q.hbg
              (hv (x := (0 : Fin 6)) (y := 2) (by decide))
              (color_ne ha Q.hg (by decide))
              (color_ne hc Q.hg (by decide))
              (color_ne Q.hj ha (by decide))
              (color_ne Q.hj hc (by decide))
              (by intro h; apply Q.hig; simpa [h] using Q.hij)
        have hcl : ¬ G.Adj c l := by
          apply C.not_adj_fourth_neighbor (Or.inr hc) hbc.symm hcd Q.hci
          · exact hv (x := (1 : Fin 6)) (y := 3) (by decide)
          · exact color_ne hb Q.hi (by decide)
          · exact color_ne hd Q.hi (by decide)
          · exact color_ne hl hb (by decide)
          · exact color_ne hl hd (by decide)
          · exact hli
        have hca : ¬ G.Adj c a := by simpa using nonedge 2 0 (by native_decide)
        have hptrSwap := containsPositiveM C.swapSides
          (a := Q.j) (b := c) (c := l) (d := Q.i) (e := a) (f := b)
          (by simp [Q.hj]) (by simp [hc]) (by simp [hl]) (by simp [Q.hi])
          (by simp [ha]) (by simp [hb]) hjl Q.hij.symm Q.hja Q.hci hbc.symm hab
          hjc hjb hcl hca
          (by
            simp [color_ne Q.hj hc (by decide), color_ne Q.hj hl (by decide),
              color_ne Q.hj Q.hi (by decide), color_ne Q.hj ha (by decide),
              color_ne Q.hj hb (by decide), color_ne hc hl (by decide),
              color_ne hc Q.hi (by decide), color_ne hc ha (by decide),
              color_ne hc hb (by decide), hli,
              color_ne hl ha (by decide), color_ne hl hb (by decide),
              color_ne Q.hi ha (by decide), color_ne Q.hi hb (by decide), habV])
        exact Or.inl (HasReachableReduction.of_current_ptr C
          ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 hptrSwap))

end Subcubic
