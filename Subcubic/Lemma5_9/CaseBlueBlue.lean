import Subcubic.Lemma5_9.SetupLM

/-! Lemma 5.9, Case (3.4.4.2): both other neighbors of `k` are blue. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_lm_blue
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (Q : Lemma5_9LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .blue) (hm : C.color Q.m = .blue) :
    HasReachableNegativeReduction C := by
  classical
  rcases Q with ⟨⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, hideg, t, ht, hit, htd, hth⟩,
    k, hk, hck, hkb, hkd, hkg, hkdeg⟩,
    hkj, hkh, l, m, hkl, hkm, hlc, hmc, hlmV, hlSide, hmSide⟩
  change C.color l = .blue at hl
  change C.color m = .blue at hm
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
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
  rcases exists_flipAt_or_cutEnhancer C hb hc ha hd hab.symm hbc hcd with
    ⟨M, hflip⟩ | hce
  · let D := M.toGoodColoring
    have hkc : k ≠ c := hck.ne.symm
    have hcD : D.color c = .red :=
      red_of_flipped_blue_with_reddish_neighbor C hflip hk hck hkb hkc
    have hkD : D.color k = .red :=
      red_of_reddish_gains_flipped_blue C hflip hk hck.symm hkb hkc
    have hdk : ¬ G.Adj d k := by
      intro q
      exact (C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
        (hv (u := (2 : Fin 8)) (v := 4) (by decide))
        (vertex_ne_of_color_eq hc hi (by decide))
        (vertex_ne_of_color_eq he hi (by decide)) hck.ne.symm
        (vertex_ne_of_color_eq hk he (by decide))
        (by intro z; apply hic; simpa [← z] using hck.symm)) q
    have blue_stays {z : V} (hz : C.color z = .blue)
        (hzc : ¬ G.Adj z c) (hzb : z ≠ b) (hzcV : z ≠ c) :
        D.color z = .blue := by
      have hzCorrect := C.color_correct z
      rw [hz] at hzCorrect
      obtain ⟨q, hqSide, hzq⟩ := hzCorrect.2
      have hqb : q ≠ b := by
        intro q'; subst q; exact hqSide ((C.mem_redSide_iff b).2 (Or.inl hb))
      have hqc : q ≠ c := by intro q'; subst q; exact hzc hzq
      exact blue_of_untouched_blue_edge C hflip (by simp [hz]) hqSide hzq
        hzb hzcV hqb hqc
    have hlb := vertex_ne_of_color_eq hl hb (by decide)
    have hmb := vertex_ne_of_color_eq hm hb (by decide)
    have hld : l ≠ d := by intro q; subst l; exact hdk hkl.symm
    have hmd : m ≠ d := by intro q; subst m; exact hdk hkm.symm
    have hcl : ¬ G.Adj l c := by
      intro q
      exact (C.not_adj_fourth_neighbor (Or.inr hc) hcd hck hbc.symm
        hkd.symm (hv (u := (3 : Fin 8)) (v := 1) (by decide)) hkb
        hld hkl.ne.symm hlb) q.symm
    have hcm : ¬ G.Adj m c := by
      intro q
      exact (C.not_adj_fourth_neighbor (Or.inr hc) hcd hck hbc.symm
        hkd.symm (hv (u := (3 : Fin 8)) (v := 1) (by decide)) hkb
        hmd hkm.ne.symm hmb) q.symm
    have hlD := blue_stays hl hcl hlb hlc
    have hmD := blue_stays hm hcm hmb hmc
    by_cases hlm : G.Adj l m
    · have hmulti : 2 ≤ fourVertexCrossEdgeCount G c k l m := by
        unfold fourVertexCrossEdgeCount
        rw [if_pos hkl, if_pos hkm]
        omega
      rcases lemma5_2 D c k l m hck hcD hkD hlm hlD hmD hmulti with hntr | hceD
      · exact HasReachableNegativeReduction.after_flip C hflip
          (HasReachableNegativeReduction.of_current_ntr D hntr)
      · exact HasReachableNegativeReduction.after_flip C hflip
          (HasReachableNegativeReduction.of_current_ce D hceD)
    · exact HasReachableNegativeReduction.after_flip C hflip
        (HasReachableNegativeReduction.of_current_ce D
          (containsCutEnhancerA_of D hkD hlD hmD hkl hkm hlmV hlm))
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
