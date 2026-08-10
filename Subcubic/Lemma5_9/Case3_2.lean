import Subcubic.Lemma5_9.Case3_1
import Subcubic.NegativeTailReducerWitnesses

/-! Lemma 5.9, Case (3.2): `a,b` share their bluish neighbor. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_shared_ab_neighbor
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_9Case3Configuration C a b c d e f g h)
    (hxy : Q.x = Q.y) : HasReachableNegativeReduction C := by
  classical
  rcases Q with ⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩
  change x = y at hxy
  subst y
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8) (huv : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) :=
    fun hG => huv ((hedge u v).mpr hG)
  have hab := edge 0 1 (by native_decide)
  have hbc := edge 1 2 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hex : ¬ G.Adj e x := by
    apply C.not_adj_fourth_neighbor (Or.inl he) hde.symm hef hej
    · exact hv (u := (3 : Fin 8)) (v := 5) (by decide)
    · exact vertex_ne_of_color_eq hd hj (by decide)
    · exact vertex_ne_of_color_eq hf hj (by decide)
    · exact vertex_ne_of_color_eq hx hd (by decide)
    · exact vertex_ne_of_color_eq hx hf (by decide)
    · exact hxj
  have hec : ¬ G.Adj e c := by simpa using nonedge 4 2 (by native_decide)
  have hn : [a, b, e, x, j, c, d].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    exact ⟨⟨hab.ne, hv (u := (0 : Fin 8)) (v := 4) (by decide),
        hya.symm, hja.ne.symm,
        hv (u := (0 : Fin 8)) (v := 2) (by decide),
        hv (u := (0 : Fin 8)) (v := 3) (by decide)⟩,
      ⟨hv (u := (1 : Fin 8)) (v := 4) (by decide), hby.ne,
        vertex_ne_of_color_eq hb hj (by decide), hbc.ne,
        hv (u := (1 : Fin 8)) (v := 3) (by decide)⟩,
      ⟨vertex_ne_of_color_eq he hx (by decide), hej.ne,
        hv (u := (4 : Fin 8)) (v := 2) (by decide), hde.ne.symm⟩,
      ⟨hxj, hyc, vertex_ne_of_color_eq hx hd (by decide)⟩,
      ⟨vertex_ne_of_color_eq hj hc (by decide),
        vertex_ne_of_color_eq hj hd (by decide)⟩, hcd.ne⟩
  have hntr := containsNegativeL C ha hb he hx hj hc hd
    hab hax hja.symm hby hbc hej hde.symm hcd hex hec hn
  exact HasReachableNegativeReduction.of_current_ntr C hntr

end Subcubic
