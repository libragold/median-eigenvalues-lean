import Subcubic.Lemma5_13.Case4ExactNoRed

/-!
# Lemma 5.13, the degree-two branch in Case (4.4.3.3)

The prose takes a third neighbor of the unique common reddish neighbor `h`.
When `h` instead has degree two, the vertices `{a, b, h}` give the
degree-guarded reddish version `ntr-dc-c`; the original red version is `ntr-l`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_exact_shared_h_degree_two
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (Q : Lemma5_13Case4Configuration C a b c d)
    {h : V} (hh : C.color h = .reddish)
    (hgh : G.Adj Q.g h) (hdh : G.Adj d h)
    (hdeg : vertexDegree G h = 2) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj u v) :
      G.Adj (![a, b, c, d] u) (![a, b, c, d] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e
    subst v
    simp_all
  have hgeD : Q.g ≠ d := color_ne Q.hg hd (by decide)
  have hhe : ¬ G.Adj h Q.e := by
    intro hhe
    rcases neighbor_eq_of_degree_two hdeg hgh.symm hdh.symm hgeD hhe with e | e
    · exact Q.hge e.symm
    · exact color_ne Q.he hd (by decide) e
  have hhc : ¬ G.Adj h c := by
    intro hhc
    rcases neighbor_eq_of_degree_two hdeg hgh.symm hdh.symm hgeD hhc with e | e
    · exact color_ne hc Q.hg (by decide) e
    · exact hcd.ne e
  have hn : [a, b, h, Q.e, Q.g, c, d].Nodup := by
    simp [hab.ne, Q.hge.symm, hcd.ne,
      color_ne ha hh (by decide), color_ne hb hh (by decide),
      color_ne ha Q.he (by decide), color_ne ha Q.hg (by decide),
      color_ne ha hc (by decide), color_ne ha hd (by decide),
      color_ne hb Q.he (by decide), color_ne hb Q.hg (by decide),
      color_ne hb hc (by decide), color_ne hb hd (by decide),
      color_ne hh Q.he (by decide), color_ne hh Q.hg (by decide),
      color_ne hh hc (by decide), color_ne hh hd (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he hd (by decide),
      color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide)]
  apply HasReachableNegativeReduction.of_current_ntr C
  apply containsNegativeDcC C ha hb hh Q.he Q.hg hc hd hdeg
    hab Q.heaEdge.symm Q.hag Q.hbe hbc hgh.symm hdh.symm hcd hhe hhc hn

end Subcubic
