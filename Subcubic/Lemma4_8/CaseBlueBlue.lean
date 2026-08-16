import Subcubic.Lemma4_8.SetupLM
import Subcubic.Lemma4_2

/-! Case (3.4.3.2): both exposed neighbors of `k` are blue. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_case_lm_blue
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (Q : Lemma4_8LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .blue) (hm : C.color Q.m = .blue) :
    HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  rcases Q with ⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, k, hk, hck, hkb, hkd, hkg, hkdeg⟩,
    hkj, hkh, l, m, hkl, hkm, hlc, hmc, hlmV, hlSide, hmSide⟩
  change C.color l = .blue at hl
  change C.color m = .blue at hm
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
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
  have hca : ¬ G.Adj c a := by
    intro hca
    exact (by native_decide : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj (2 : Fin 8) 0) ((hedge 2 0).mpr hca)
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
      (degree_of_color (Or.inl hb)) (degree_of_color (Or.inr hc))
      hab.symm hbc hcd
      with hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toColoring
    have hkc : k ≠ c := hck.ne.symm
    have hcD : D.color c = .red :=
      red_of_flipped_blue_with_reddish_neighbor C hflip hk hck hkb hkc
    have hkD : D.color k = .red :=
      red_of_reddish_gains_flipped_blue C hflip hk hck.symm hkb hkc
    have hdk : ¬ G.Adj d k := by
      apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
      · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
      · intro hci
        rw [← hci] at hi
        simp [hc] at hi
      · intro hei
        rw [← hei] at hi
        simp [he] at hi
      · exact hck.ne.symm
      · intro hke
        rw [hke] at hk
        simp [he] at hk
      · intro hki
        rw [hki] at hck
        exact hic hck.symm
    have blue_stays {z : V} (hz : C.color z = .blue)
        (hzc : ¬ G.Adj z c) (hzb : z ≠ b) (hzcV : z ≠ c) :
        D.color z = .blue := by
      have hzCorrect := C.color_correct z
      rw [hz] at hzCorrect
      obtain ⟨q, hqBlue, hzq⟩ := hzCorrect.2
      have hqb : q ≠ b := by
        intro hqb
        subst q
        exact hqBlue ((C.mem_redSide_iff b).2 (Or.inl hb))
      have hqc : q ≠ c := by
        intro hqc
        subst q
        exact hzc hzq
      exact blue_of_untouched_blue_edge C hflip (by simp [hz]) hqBlue hzq
        hzb hzcV hqb hqc
    have hlb : l ≠ b := by
      intro hlb
      rw [hlb] at hl
      simp [hb] at hl
    have hmb : m ≠ b := by
      intro hmb
      rw [hmb] at hm
      simp [hb] at hm
    have hld : l ≠ d := by
      intro hld
      rw [hld] at hkl
      exact hdk hkl.symm
    have hmd : m ≠ d := by
      intro hmd
      rw [hmd] at hkm
      exact hdk hkm.symm
    have hcl : ¬ G.Adj l c := by
      simpa [SimpleGraph.adj_comm] using C.not_adj_fourth_neighbor
        (v := c) (w := l) (Or.inr hc) hcd hck hbc.symm
        hkd.symm
        (hv (u := (3 : Fin 8)) (v := 1) (by decide)) hkb
        hld hkl.ne.symm hlb
    have hcm : ¬ G.Adj m c := by
      simpa [SimpleGraph.adj_comm] using C.not_adj_fourth_neighbor
        (v := c) (w := m) (Or.inr hc) hcd hck hbc.symm
        hkd.symm
        (hv (u := (3 : Fin 8)) (v := 1) (by decide)) hkb
        hmd hkm.ne.symm hmb
    have hlD := blue_stays hl hcl hlb hlc
    have hmD := blue_stays hm hcm hmb hmc
    by_cases hlm : G.Adj l m
    · have hmulti : 2 ≤ fourVertexCrossEdgeCount G c k l m := by
        unfold fourVertexCrossEdgeCount
        rw [if_pos hkl, if_pos hkm]
        omega
      have hout := lemma4_2 D c k l m
        hck hcD hkD hlm hlD hmD hmulti
      exact HasReachableReduction.after_flip C hflip
        (hout.elim (HasReachableReduction.of_current_ptr D)
          (HasReachableReduction.of_current_ce D))
    · exact HasReachableReduction.after_flip C hflip
        (HasReachableReduction.of_current_ce D
          (containsCutEnhancerA_of D hkD hlD hmD hkl hkm hlmV hlm))
  · exact HasReachableReduction.of_current_ce C hce

end Subcubic
