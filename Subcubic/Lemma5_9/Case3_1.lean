import Subcubic.Lemma5_9.Cases1And2Setup3
import Subcubic.Lemma5_2

/-! Lemma 5.9, Case (3.1): `i ~ j`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_i_adj_j
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_9Case3Configuration C a b c d e f g h)
    (hij : G.Adj Q.i Q.j) : HasReachableNegativeReduction C := by
  classical
  rcases Q with ⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩
  change G.Adj i j at hij
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨_, hedge⟩
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
  have hef : G.Adj e f := by simpa using edge 4 5 (by native_decide)
  obtain ⟨M, hflip⟩ := exists_flipAt_of_local C
    he hd hf hc (Or.inl hj) (Or.inl hi) hef hde.symm hej hcd.symm hdi
  let D := M.toColoring
  have hie : i ≠ e := vertex_ne_of_color_eq hi he (by decide)
  have hid : i ≠ d := vertex_ne_of_color_eq hi hd (by decide)
  have hje : j ≠ e := vertex_ne_of_color_eq hj he (by decide)
  have hjd : j ≠ d := vertex_ne_of_color_eq hj hd (by decide)
  have hdD : D.color d = .red :=
    red_of_flipped_blue_with_reddish_neighbor C hflip hi hdi hie hid
  have hiD : D.color i = .red :=
    red_of_reddish_gains_flipped_blue C hflip hi hdi.symm hie hid
  have heD : D.color e = .blue :=
    blue_of_flipped_red_with_bluish_neighbor C hflip hj hej hje hjd
  have hjD : D.color j = .blue :=
    blue_of_bluish_gains_flipped_red C hflip hj hej.symm hje hjd
  have hmulti : 2 ≤ fourVertexCrossEdgeCount G d i e j := by
    unfold fourVertexCrossEdgeCount
    rw [if_pos hde, if_pos hij]
    omega
  exact HasReachableNegativeReduction.after_flip C hflip
    (lemma5_2 D d i e j hdi hdD hiD hej heD hjD hmulti)

end Subcubic
