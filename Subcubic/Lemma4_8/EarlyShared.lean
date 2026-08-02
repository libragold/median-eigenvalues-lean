import Subcubic.Lemma4_8.Early
import Subcubic.PositiveTailReducerWitnesses

/-! The shared-neighbor case (3.2) of Lemma 4.8. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_case_shared_ab_neighbor
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma4_8DeepConfiguration C a b c d e f g h)
    (hxy : Q.x = Q.y) : HasReachableReduction C := by
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
  have edge (u v : Fin 8)
      (huv : (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4),
         (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 8)
      (huv : ¬ (graphOfEdges
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
    · intro hdj
      rw [← hdj] at hj
      simp [hd] at hj
    · intro hfj
      rw [← hfj] at hj
      simp [hf] at hj
    · intro hxe
      rw [hxe] at hx
      simp [hd] at hx
    · intro hxf
      rw [hxf] at hx
      simp [hf] at hx
    · exact hxj
  have hec : ¬ G.Adj e c := by
    simpa using nonedge 4 2 (by native_decide)
  have hn : [a, b, e, x, j, c, d].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    have hbjV : b ≠ j := by
      intro hbjV
      rw [← hbjV] at hj
      simp [hb] at hj
    have hexV : e ≠ x := by
      intro hexV
      rw [← hexV] at hx
      simp [he] at hx
    have hjcV : j ≠ c := by
      intro hjcV
      rw [hjcV] at hj
      simp [hc] at hj
    have hjdV : j ≠ d := by
      intro hjdV
      rw [hjdV] at hj
      simp [hd] at hj
    have hxdV : x ≠ d := by
      intro hxdV
      rw [hxdV] at hx
      simp [hd] at hx
    exact ⟨⟨hab.ne, hv (u := (0 : Fin 8)) (v := 4) (by decide),
        hya.symm, hja.ne.symm,
        hv (u := (0 : Fin 8)) (v := 2) (by decide),
        hv (u := (0 : Fin 8)) (v := 3) (by decide)⟩,
      ⟨hv (u := (1 : Fin 8)) (v := 4) (by decide), hby.ne, hbjV,
        hbc.ne, hv (u := (1 : Fin 8)) (v := 3) (by decide)⟩,
      ⟨hexV, hej.ne, hv (u := (4 : Fin 8)) (v := 2) (by decide),
        hde.ne.symm⟩,
      ⟨hxj, hyc, hxdV⟩, ⟨hjcV, hjdV⟩, hcd.ne⟩
  exact HasReachableReduction.of_current_ptr C
    (containsPositiveN C ha hb he hx hj hc hd hab hax hja.symm hby
      hbc hej hde.symm hcd hex hec hn)

end Subcubic
