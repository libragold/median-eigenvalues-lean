import Subcubic.Lemma5_9.CaseKJ
import Subcubic.Lemma5_4

/-!
# Lemma 5.9, Case (3.4.2): setup

Here the third neighbor `l` of `k` is blue.  Cut enhancers `e` and `b`
exclude `k-h` and every red neighbor of `l`.  We then expose the blue mate
`m` of `l`; the no-red-neighbor branch is isolated, while the other branch
is recorded for the flip `mn`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9KJBlueMConfiguration (C : MatchingCutColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9KJBlueConfiguration C a b c d e f g h where
  hkh : ¬ G.Adj k h
  hla : ¬ G.Adj l a
  m : V
  hm : C.color m = .blue
  hlm : G.Adj l m
  n : V
  hn : C.color n = .red
  hmn : G.Adj m n
  hma : ¬ G.Adj m a
  hmb : ¬ G.Adj m b
  hmf : ¬ G.Adj m f
  hme : ¬ G.Adj m e
  hmi : ¬ G.Adj m i
  hnl : ¬ G.Adj n l

theorem lemma5_9_case_kj_blue_setup
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_9KJBlueConfiguration C a b c d e f g h) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9KJBlueMConfiguration C a b c d e f g h) := by
  classical
  by_contra hfinal
  push Not at hfinal
  have noCE (hce : ContainsCutEnhancer C) : False :=
    hfinal.1 (HasReachableNegativeReduction.of_current_ce C hce)
  have noResult (hr : HasReachableNegativeReduction C) : False := hfinal.1 hr
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (noResult (.of_current_ntr C hntr)).elim
    · exact (noResult (.of_current_ce C hce)).elim
  rcases Q with ⟨⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, hideg, t, ht, hit, htd, hth⟩,
    k, hk, hck, hkb, hkd, hkg, hkdeg⟩,
    hkj, l, hl, hkl, hlc, hlj, hkdAdjStored⟩
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
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
  have hef : G.Adj e f := by simpa using edge 4 5 (by native_decide)
  have hfg : G.Adj f g := by simpa using edge 5 6 (by native_decide)
  have hgh : G.Adj g h := by simpa using edge 6 7 (by native_decide)
  have hkdAdj : ¬ G.Adj k d := by
    intro q
    exact (C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
      (hv (u := (2 : Fin 8)) (v := 4) (by decide))
      (vertex_ne_of_color_eq hc hi (by decide))
      (vertex_ne_of_color_eq he hi (by decide)) hck.ne.symm
      (vertex_ne_of_color_eq hk he (by decide))
      (by intro q; subst k; exact hic hck.symm)) q.symm

  have hkh : ¬ G.Adj k h := by
    intro hkh
    have hak : ¬ G.Adj a k :=
      fun q => C.reddish_not_adj_redSide hk (Or.inl ha) q.symm
    have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
    have hai : ¬ G.Adj a i :=
      fun q => C.reddish_not_adj_redSide hi (Or.inl ha) q.symm
    have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
    have hah : ¬ G.Adj a h := by simpa using nonedge 0 7 (by native_decide)
    have hke : ¬ G.Adj k e :=
      C.reddish_not_adj_redSide hk (Or.inl he)
    have hki : ¬ G.Adj k i :=
      C.reddish_not_adj_redSide hk (Or.inr hi)
    have hei : ¬ G.Adj e i :=
      fun q => C.reddish_not_adj_redSide hi (Or.inl he) q.symm
    have heh : ¬ G.Adj e h := by simpa using nonedge 4 7 (by native_decide)
    have hjd : ¬ G.Adj j d :=
      C.bluish_not_adj_blueSide hj (Or.inl hd)
    have hjh : ¬ G.Adj j h :=
      C.bluish_not_adj_blueSide hj (Or.inl hh)
    have hdh : ¬ G.Adj d h := by simpa using nonedge 3 7 (by native_decide)
    have hnCE : [a, k, e, i, j, d, h].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, not_false_eq_true, and_true]
      exact ⟨⟨vertex_ne_of_color_eq ha hk (by decide),
          hv (u := (0 : Fin 8)) (v := 4) (by decide),
          vertex_ne_of_color_eq ha hi (by decide), hja.ne.symm,
          hv (u := (0 : Fin 8)) (v := 3) (by decide),
          hv (u := (0 : Fin 8)) (v := 7) (by decide)⟩,
        ⟨vertex_ne_of_color_eq hk he (by decide),
          (by intro q; subst k; exact hic hck.symm), hkj.ne, hkd,
          hkh.ne⟩,
        ⟨vertex_ne_of_color_eq he hi (by decide), hej.ne,
          hde.ne.symm, hv (u := (4 : Fin 8)) (v := 7) (by decide)⟩,
        ⟨vertex_ne_of_color_eq hi hj (by decide), hdi.ne.symm, hih.ne⟩,
        ⟨vertex_ne_of_color_eq hj hd (by decide),
          vertex_ne_of_color_eq hj hh (by decide)⟩,
        hv (u := (3 : Fin 8)) (v := 7) (by decide)⟩
    exact noCE (containsCutEnhancerE_of C
      ha hk he hi hj hd hh hja.symm hkj hkh hej hde.symm
      hdi.symm hih hak hae hai had hah hke hki hkdAdj hei heh
      hij hjd hjh hdh hnCE)

  have hla : ¬ G.Adj l a := by
    intro hla
    exact hNoBlueAtA l hla.symm hl

  have hdlAdj : ¬ G.Adj d l := by
    apply C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
      (by simp [hl]) hcd.symm
    exact hlc.symm
  have hcl : ¬ G.Adj c l := by
    apply C.blueSide_not_adj_second_neighbor (by simp [hc]) (by simp [hd])
      (by simp [hl]) hcd
    intro q
    subst l
    exact hkdAdj hkl
  have hhlAdj : ¬ G.Adj h l := by
    apply C.blueSide_not_adj_second_neighbor (by simp [hh]) (by simp [hg])
      (by simp [hl]) hgh.symm
    intro q
    subst l
    exact hkg hkl
  have hgl : ¬ G.Adj g l := by
    apply C.blueSide_not_adj_second_neighbor (by simp [hg]) (by simp [hh])
      (by simp [hl]) hgh
    intro q
    subst l
    exact hkh hkl

  have lNoRed : ∀ z, G.Adj l z → C.color z ≠ .red := by
    intro z hlz hz
    have hkz : ¬ G.Adj k z :=
      C.reddish_not_adj_redSide hk (Or.inl hz)
    have hbl : ¬ G.Adj b l := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        hab.symm hbc hby
      · exact hv (u := (0 : Fin 8)) (v := 2) (by decide)
      · exact hya.symm
      · exact hyc.symm
      · exact vertex_ne_of_color_eq hl ha (by decide)
      · exact hlc
      · exact vertex_ne_of_color_eq hl hy (by decide)
    have hcz : ¬ G.Adj c z := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        hbc.symm hcd hck
      · exact hv (u := (1 : Fin 8)) (v := 3) (by decide)
      · exact hkb.symm
      · exact hkd.symm
      · intro q; subst z; exact hbl hlz.symm
      · exact vertex_ne_of_color_eq hz hd (by decide)
      · exact vertex_ne_of_color_eq hz hk (by decide)
    have hbz : ¬ G.Adj b z :=
      C.redSide_not_adj_second_neighbor (by simp [hb]) (by simp [ha])
        (by simp [hz]) hab.symm
        (by intro q; subst z; exact hla hlz)
    exact noCE (containsCutEnhancerB_of C hk hc hb hl hz
      hck.symm hkl hbc.symm hlz
      (C.reddish_not_adj_redSide hk (Or.inl hb)) hkz
      hcl hcz hbl hbz)

  obtain ⟨m, hm, hlm⟩ := C.exists_blue_mate hl
  by_cases hmHasRed : ∃ n, G.Adj m n ∧ C.color n = .red
  · rcases hmHasRed with ⟨n, hmn, hn⟩
    have hma : ¬ G.Adj m a := by
      intro q
      exact hNoBlueAtA m q.symm hm
    have hmb : ¬ G.Adj m b := by
      intro hmb
      apply (not_adj_fourth_neighbor_of_subcubic C.subcubic
        hab.symm hbc hby
        (hv (u := (0 : Fin 8)) (v := 2) (by decide)) hya.symm hyc.symm
        (vertex_ne_of_color_eq hm ha (by decide))
        (by
          intro q
          subst m
          exact hcl hlm.symm)
        (vertex_ne_of_color_eq hm hy (by decide)))
      exact hmb.symm
    have hmf : ¬ G.Adj m f := by
      obtain ⟨r, hfr, hre, hrg⟩ := C.exists_third_neighbor (degreeC (Or.inl hf))
        (hv (u := (4 : Fin 8)) (v := 6) (by decide))
      have hrSide := C.other_neighbor_of_red_is_blueSide hf he hef.symm hfr hre
      have hrh : r ≠ h := by intro q; subst r; exact (nonedge 5 7 (by native_decide)) hfr
      rcases lemma3_3 C hf hg hh hrSide hfg hfr hgh hrg.symm hrh.symm with hr | hce
      · intro hmf
        have hmg : m ≠ g := by
          intro q
          subst m
          exact hgl hlm.symm
        exact (not_adj_fourth_neighbor_of_subcubic C.subcubic
          hef.symm hfg hfr
          (hv (u := (4 : Fin 8)) (v := 6) (by decide)) hre.symm hrg.symm
          (vertex_ne_of_color_eq hm he (by decide)) hmg
          (vertex_ne_of_color_eq hm hr (by decide))) hmf.symm
      · exact (noCE hce).elim
    have hmi : ¬ G.Adj m i := by
      intro hmi
      have hcm : c ≠ m := by
        intro q
        subst m
        exact hcl hlm.symm
      have hgm : g ≠ m := by
        intro q
        subst m
        exact hgl hlm.symm
      have hdm : ¬ G.Adj d m :=
        C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
          (by simp [hm]) hcd.symm hcm
      have hhm : ¬ G.Adj h m :=
        C.blueSide_not_adj_second_neighbor (by simp [hh]) (by simp [hg])
          (by simp [hm]) hgh.symm hgm
      have hmd : m ≠ d := by
        intro q
        subst m
        exact hdlAdj hlm.symm
      have hmh : m ≠ h := by
        intro q
        subst m
        exact hhlAdj hlm.symm
      have hem : ¬ G.Adj e m := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic hde.symm hef hej
        · exact hv (u := (3 : Fin 8)) (v := 5) (by decide)
        · exact vertex_ne_of_color_eq hd hj (by decide)
        · exact vertex_ne_of_color_eq hf hj (by decide)
        · exact hmd
        · exact vertex_ne_of_color_eq hm hf (by decide)
        · exact vertex_ne_of_color_eq hm hj (by decide)
      have hceSwap := containsCutEnhancerC_of C.swapSides
        (a := d) (b := h) (c := e) (d := i) (e := m)
        (by simp [hd]) (by simp [hh]) (by simp [he]) (by simp [hi])
        (by simp [hm]) hde hdi hih.symm hmi.symm
        (by simpa using nonedge 3 7 (by native_decide))
        hdm
        (by simpa using nonedge 7 4 (by native_decide))
        hhm
        (fun q => C.reddish_not_adj_redSide hi (Or.inl he) q.symm)
        hem
        (hv (u := (3 : Fin 8)) (v := 7) (by decide))
        hmd.symm hmh.symm
      exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
    have hnl : ¬ G.Adj n l := by
      intro hnl
      have hkn : ¬ G.Adj k n :=
        C.reddish_not_adj_redSide hk (Or.inl hn)
      have hcn : ¬ G.Adj c n := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic hbc.symm hcd hck
        · exact hv (u := (1 : Fin 8)) (v := 3) (by decide)
        · exact hkb.symm
        · exact hkd.symm
        · intro q; subst n; exact hmb hmn
        · exact vertex_ne_of_color_eq hn hd (by decide)
        · exact vertex_ne_of_color_eq hn hk (by decide)
      have hbl : ¬ G.Adj b l := by
        intro q
        exact lNoRed b q.symm hb
      have hbn : ¬ G.Adj b n :=
        C.redSide_not_adj_second_neighbor (by simp [hb]) (by simp [ha])
          (by simp [hn]) hab.symm
          (by intro q; subst n; exact hma hmn)
      exact noCE (containsCutEnhancerB_of C hk hc hb hl hn
        hck.symm hkl hbc.symm hnl.symm
        (C.reddish_not_adj_redSide hk (Or.inl hb)) hkn
        hcl hcn hbl hbn)
    exact hfinal.2.false {
      toLemma5_9KJBlueConfiguration :=
        ⟨⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
          hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
          hic, hideg, t, ht, hit, htd, hth⟩,
          k, hk, hck, hkb, hkd, hkg, hkdeg⟩,
          hkj, l, hl, hkl, hlc, hlj, hkdAdjStored⟩
      hkh := hkh
      hla := hla
      m := m
      hm := hm
      hlm := hlm
      n := n
      hn := hn
      hmn := hmn
      hma := hma
      hmb := hmb
      hmf := hmf
      hme := by
        intro q
        exact (not_adj_fourth_neighbor_of_subcubic C.subcubic hde.symm hef hej
          (hv (u := (3 : Fin 8)) (v := 5) (by decide))
          (vertex_ne_of_color_eq hd hj (by decide))
          (vertex_ne_of_color_eq hf hj (by decide))
          (by intro q; subst m; exact hdlAdj hlm.symm)
          (vertex_ne_of_color_eq hm hf (by decide))
          (vertex_ne_of_color_eq hm hj (by decide))) q.symm
      hmi := hmi
      hnl := hnl }
  · have mNoRed : ∀ z, G.Adj m z → z ≠ l → C.color z = .reddish := by
      intro z hmz hzl
      have hzSide := C.other_neighbor_of_blue_is_redSide hm hl hlm.symm hmz hzl
      rcases hzSide with hz | hz
      · exact (hmHasRed ⟨z, hmz, hz⟩).elim
      · exact hz
    have lOther : ∀ z, G.Adj l z → z ≠ m → C.color z = .reddish := by
      intro z hlz hzm
      have hzSide := C.other_neighbor_of_blue_is_redSide hl hm hlm hlz hzm
      rcases hzSide with hz | hz
      · exact (lNoRed z hlz hz).elim
      · exact hz
    have hdoneSwap := lemma5_4 C.swapSides (by simp [hl]) (by simp [hm]) hlm
      (by intro z hlz hzm; simp [lOther z hlz hzm])
      (by intro z hmz hzl; simp [mNoRed z hmz hzl])
    exact noResult (HasReachableNegativeReduction.of_swapSides C hdoneSwap)

end Subcubic
