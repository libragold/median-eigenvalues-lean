import Subcubic.Lemma4_8.CaseBluishHard

/-! Case (3.4.3.3): one exposed neighbor of `k` is bluish and one is blue. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_8MixedPConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8LMConfiguration C a b c d e f g h where
  hl : C.color l = .bluish
  hm : C.color m = .blue
  n : V
  hn : C.color n = .blue
  hmn : G.Adj m n
  o : V
  ho : C.color o = .reddish
  hmo : G.Adj m o
  hok : o ≠ n
  hon : o ≠ k
  p : V
  hp : C.color p = .red
  hnp : G.Adj n p
  hma : ¬ G.Adj m a
  hna : ¬ G.Adj n a
  hmb : ¬ G.Adj m b
  hnb : ¬ G.Adj n b
  hmf : ¬ G.Adj m f
  hnf : ¬ G.Adj n f
  hmi : ¬ G.Adj m i
  hni : ¬ G.Adj n i
  hnc : n ≠ c
  hnd : n ≠ d
  hng : n ≠ g
  hnh : n ≠ h
  hpl : ¬ G.Adj p l
  hpg : ¬ G.Adj p g
  hph : ¬ G.Adj p h
  hpj : ¬ G.Adj p j

theorem lemma4_8_case_lm_mixed_setup
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .blue) :
    HasReachableReduction C ∨
      Nonempty (Lemma4_8MixedPConfiguration C a b c d e f g h) := by
  classical
  by_contra hgoal
  push Not at hgoal
  have noResult (h : HasReachableReduction C) : False := hgoal.1 h
  have noCE (hce : ContainsCutEnhancer C) : False :=
    noResult (HasReachableReduction.of_current_ce C hce)
  have noPTR (hptr : ContainsPositiveTailReducer C) : False :=
    noResult (HasReachableReduction.of_current_ptr C hptr)
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (noPTR hptr).elim
    · exact (noCE hce).elim
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
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  have hmCorrect := C.color_correct Q.m
  rw [hm] at hmCorrect
  obtain ⟨_, n, hnSide, hmn⟩ := hmCorrect
  have hnSide' := (C.not_mem_redSide_iff n).1 hnSide
  have hn : C.color n = .blue := by
    rcases hnSide' with hn | hn
    · exact hn
    · exact (C.bluish_not_adj_blueSide hn (Or.inl hm) hmn.symm).elim
  have hnk : n ≠ Q.k := color_ne hn Q.hk (by decide)
  obtain ⟨o, hmo, hok, hon⟩ :=
    C.exists_third_neighbor (degree_of_color (Or.inr hm)) hnk
  have hoSide := C.other_neighbor_of_blue_is_redSide hm hn hmn hmo hok
  have hdk : ¬ G.Adj d Q.k := by
    apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
    · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
    · exact color_ne hc Q.hi (by decide)
    · exact color_ne he Q.hi (by decide)
    · exact Q.hck.ne.symm
    · exact color_ne Q.hk he (by decide)
    · intro hki
      have : G.Adj c Q.i := by simpa [hki] using Q.hck
      exact Q.hic this.symm
  have hmd : Q.m ≠ d := by
    intro h
    apply hdk
    simpa [h] using Q.hkm.symm
  have hnc : n ≠ c := by
    intro h
    have hcm : G.Adj c Q.m := by simpa [h] using hmn.symm
    exact (C.blueSide_not_adj_second_neighbor
      (by simp [hc]) (by simp [hd]) (by simp [hm]) hcd hmd.symm) hcm
  have hmc : ¬ G.Adj Q.m c := by
    have := C.blueSide_not_adj_second_neighbor
      (by simp [hm]) (by simp [hn]) (by simp [hc]) hmn hnc
    exact this
  have hmg : Q.m ≠ g := by
    intro h
    apply Q.hkg
    simpa [h] using Q.hkm
  have hmh : Q.m ≠ h := by
    intro h
    apply Q.hkh
    simpa [h] using Q.hkm
  have hmb : ¬ G.Adj Q.m b := by
    intro hmb
    have hbd : d ≠ Q.m := by
      intro h
      exact (nonedge 1 3 (by native_decide)) (by simpa [h] using hmb.symm)
    rcases lemma3_3 C hb hc hd (Or.inl hm) hbc hmb.symm hcd Q.hmc.symm
        hbd with hbad | hce
    · simp [hm] at hbad
    · exact noCE hce
  have hmf : ¬ G.Adj Q.m f := by
    intro hmf
    rcases lemma3_3 C hf hg hh (Or.inl hm) hfg hmf.symm hgh
        hmg.symm hmh.symm with hbad | hce
    · simp [hm] at hbad
    · exact noCE hce
  have hnd : n ≠ d := by
    intro h
    have hdm : G.Adj d Q.m := by simpa [h] using hmn.symm
    exact (C.blueSide_not_adj_second_neighbor
      (by simp [hd]) (by simp [hc]) (by simp [hm]) hcd.symm Q.hmc.symm) hdm
  have hng : n ≠ g := by
    intro h
    have hgm : G.Adj g Q.m := by simpa [h] using hmn.symm
    exact (C.blueSide_not_adj_second_neighbor
      (by simp [hg]) (by simp [hh]) (by simp [hm]) hgh hmh.symm) hgm
  have hnh : n ≠ h := by
    intro hEq
    have hhm : G.Adj h Q.m := by simpa [hEq] using hmn.symm
    exact (C.blueSide_not_adj_second_neighbor
      (by simp [hh]) (by simp [hg]) (by simp [hm]) hgh.symm hmg.symm) hhm
  have hnb : ¬ G.Adj n b := by
    intro hnb
    rcases lemma3_3 C hb hc hd (Or.inl hn) hbc hnb.symm hcd hnc.symm
        hnd.symm with hbad | hce
    · simp [hn] at hbad
    · exact noCE hce
  have hnf : ¬ G.Adj n f := by
    intro hnf
    rcases lemma3_3 C hf hg hh (Or.inl hn) hfg hnf.symm hgh
        hng.symm hnh.symm with hbad | hce
    · simp [hn] at hbad
    · exact noCE hce
  have hma : ¬ G.Adj Q.m a := by
    rw [SimpleGraph.adj_comm]
    apply C.not_adj_fourth_neighbor (Or.inl ha) hab Q.hja.symm Q.hax
    · exact color_ne hb Q.hj (by decide)
    · exact color_ne hb Q.hx (by decide)
    · exact Q.hxj.symm
    · exact color_ne hm hb (by decide)
    · exact color_ne hm Q.hj (by decide)
    · exact color_ne hm Q.hx (by decide)
  have hna : ¬ G.Adj n a := by
    rw [SimpleGraph.adj_comm]
    apply C.not_adj_fourth_neighbor (Or.inl ha) hab Q.hja.symm Q.hax
    · exact color_ne hb Q.hj (by decide)
    · exact color_ne hb Q.hx (by decide)
    · exact Q.hxj.symm
    · exact color_ne hn hb (by decide)
    · exact color_ne hn Q.hj (by decide)
    · exact color_ne hn Q.hx (by decide)
  have not_adj_i_of_blue {z : V} (hz : C.color z = .blue)
      (hzc : z ≠ c) (hzd : z ≠ d) (hzg : z ≠ g) (hzh : z ≠ h) :
      ¬ G.Adj Q.i z := by
    intro hiz
    have hdh : ¬ G.Adj d h :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hd]) (by simp [hc]) (by simp [hh]) hcd.symm
        (hv (u := (2 : Fin 8)) (v := 7) (by decide))
    have hdz : ¬ G.Adj d z :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hd]) (by simp [hc]) (by simp [hz]) hcd.symm hzc.symm
    have hhe : ¬ G.Adj h e := by
      simpa using nonedge 7 4 (by native_decide)
    have hhz : ¬ G.Adj h z :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hh]) (by simp [hg]) (by simp [hz]) hgh.symm hzg.symm
    have hei : ¬ G.Adj e Q.i := by
      simpa [SimpleGraph.adj_comm] using
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
    have hez : ¬ G.Adj e z := by
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
      · exact color_ne hf Q.hj (by decide)
      · exact color_ne hd Q.hj (by decide)
      · exact color_ne hz hf (by decide)
      · exact hzd
      · exact color_ne hz Q.hj (by decide)
    have hceSwap := containsCutEnhancerC_of C.swapSides
      (by simp [hd]) (by simp [hh]) (by simp [he])
      (by simp [Q.hi]) (by simp [hz])
      hde Q.hdi Q.hih.symm hiz hdh hdz hhe hhz hei hez
      (hv (u := (3 : Fin 8)) (v := 7) (by decide))
      hzd.symm hzh.symm
    exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
  have hmi : ¬ G.Adj Q.m Q.i := by
    simpa [SimpleGraph.adj_comm] using
      not_adj_i_of_blue hm Q.hmc hmd hmg hmh
  have hni : ¬ G.Adj n Q.i := by
    simpa [SimpleGraph.adj_comm] using
      not_adj_i_of_blue hn hnc hnd hng hnh
  have ho : C.color o = .reddish := by
    rcases hoSide with ho | ho
    · have hkb : ¬ G.Adj Q.k b :=
        C.reddish_not_adj_redSide Q.hk (Or.inl hb)
      have hko : ¬ G.Adj Q.k o :=
        C.reddish_not_adj_redSide Q.hk (Or.inl ho)
      have hcm : ¬ G.Adj c Q.m := by simpa [SimpleGraph.adj_comm] using hmc
      have hco : ¬ G.Adj c o := by
        apply C.not_adj_fourth_neighbor (Or.inr hc) hcd Q.hck hbc.symm
        · exact Q.hkd.symm
        · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
        · exact Q.hkb
        · exact color_ne ho hd (by decide)
        · exact color_ne ho Q.hk (by decide)
        · intro h
          apply hmb
          simpa [h] using hmo
      have hoa : o ≠ a := by
        intro h
        apply hma
        simpa [h] using hmo
      have hbo : ¬ G.Adj b o :=
        C.redSide_not_adj_second_neighbor
          (by simp [hb]) (by simp [ha]) (by simp [ho]) hab.symm hoa.symm
      exact (noCE (containsCutEnhancerB_of C Q.hk hc hb hm ho
        Q.hck.symm Q.hkm hbc.symm hmo hkb hko hcm hco
        (by simpa [SimpleGraph.adj_comm] using hmb) hbo)).elim
    · exact ho
  by_cases hpred : ∃ p, G.Adj n p ∧ C.color p = .red
  · obtain ⟨p, hnp, hp⟩ := hpred
    have hpg : ¬ G.Adj p g := by
      intro hpg
      have hpe : p ≠ e := by
        intro h
        exact (nonedge 4 6 (by native_decide)) (by simpa [h] using hpg)
      have hpf : p ≠ f := by
        intro h
        apply hnf
        simpa [h] using hnp
      have hfp : ¬ G.Adj f p :=
        C.redSide_not_adj_second_neighbor
          (by simp [hf]) (by simp [he]) (by simp [hp]) hef.symm
          hpe.symm
      have hceSwap := containsCutEnhancerA_of C.swapSides
        (by simp [hg]) (by simp [hf]) (by simp [hp]) hfg.symm hpg.symm
        hpf.symm hfp
      exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
    have hph : ¬ G.Adj p h := by
      intro hph
      have hpeV : p ≠ e := by
        intro h
        exact (nonedge 4 7 (by native_decide)) (by simpa [h] using hph)
      have hpfV : p ≠ f := by
        intro h
        exact (nonedge 5 7 (by native_decide)) (by simpa [h] using hph)
      have hie : ¬ G.Adj Q.i e :=
        C.reddish_not_adj_redSide Q.hi (Or.inl he)
      have hip : ¬ G.Adj Q.i p :=
        C.reddish_not_adj_redSide Q.hi (Or.inl hp)
      have hdh : ¬ G.Adj d h :=
        C.blueSide_not_adj_second_neighbor
          (by simp [hd]) (by simp [hc]) (by simp [hh]) hcd.symm
          (hv (u := (2 : Fin 8)) (v := 7) (by decide))
      have hdp : ¬ G.Adj d p := by
        apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
        · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
        · exact color_ne hc Q.hi (by decide)
        · exact color_ne he Q.hi (by decide)
        · exact color_ne hp hc (by decide)
        · exact hpeV
        · exact color_ne hp Q.hi (by decide)
      have heh : ¬ G.Adj e h := by simpa using nonedge 4 7 (by native_decide)
      exact noCE (containsCutEnhancerB_of C Q.hi hd he hh hp
        Q.hdi.symm Q.hih hde hph.symm hie hip hdh hdp
        (by simpa [SimpleGraph.adj_comm] using heh)
        (C.redSide_not_adj_second_neighbor
          (by simp [he]) (by simp [hf]) (by simp [hp]) hef
          hpfV.symm))
    have hpj : ¬ G.Adj p Q.j := by
      intro hpj
      have hdn : ¬ G.Adj d n := by
        apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
        · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
        · exact color_ne hc Q.hi (by decide)
        · exact color_ne he Q.hi (by decide)
        · exact hnc
        · exact color_ne hn he (by decide)
        · exact color_ne hn Q.hi (by decide)
      have hdj : ¬ G.Adj d Q.j :=
        C.bluish_not_adj_blueSide Q.hj (Or.inl hd) ∘ SimpleGraph.Adj.symm
      have hen : ¬ G.Adj e n := by
        apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
        · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
        · exact color_ne hf Q.hj (by decide)
        · exact color_ne hd Q.hj (by decide)
        · exact color_ne hn hf (by decide)
        · exact hnd
        · exact color_ne hn Q.hj (by decide)
      have hep : ¬ G.Adj e p :=
        C.redSide_not_adj_second_neighbor
          (by simp [he]) (by simp [hf]) (by simp [hp]) hef
          (by
            intro h
            change f = p at h
            exact hnf (by simpa [h] using hnp))
      have hpeV : p ≠ e := by
        intro h
        apply hen
        simpa [h] using hnp.symm
      have hdp : ¬ G.Adj d p := by
        apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
        · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
        · exact color_ne hc Q.hi (by decide)
        · exact color_ne he Q.hi (by decide)
        · exact color_ne hp hc (by decide)
        · exact hpeV
        · exact color_ne hp Q.hi (by decide)
      have hjn : ¬ G.Adj Q.j n :=
        C.bluish_not_adj_blueSide Q.hj (Or.inl hn)
      have hceSwap := containsCutEnhancerB_of C.swapSides
        (by simp [Q.hj]) (by simp [he]) (by simp [hd])
        (by simp [hp]) (by simp [hn])
        Q.hej.symm hpj.symm hde.symm hnp.symm
        (by simpa [SimpleGraph.adj_comm] using hdj) hjn hep hen
        (by simpa [SimpleGraph.adj_comm] using hdp)
        (by simpa [SimpleGraph.adj_comm] using hdn)
      exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
    by_cases hpl : G.Adj p Q.l
    · have hpf : p ≠ f := by
        intro hpf
        subst p
        exact hpg hfg
      have hpe : ¬ G.Adj p e := by
        simpa [SimpleGraph.adj_comm] using
          C.redSide_not_adj_second_neighbor
            (by simp [he]) (by simp [hf]) (by simp [hp]) hef hpf.symm
      have hpCorrect := C.color_correct p
      rw [hp] at hpCorrect
      obtain ⟨_, q, hqSide, hpq⟩ := hpCorrect
      have hqSide' := (C.mem_redSide_iff q).1 hqSide
      have hq : C.color q = .red := by
        rcases hqSide' with hq | hq
        · exact hq
        · exact (C.reddish_not_adj_redSide hq (Or.inl hp) hpq.symm).elim
      have pnq : n ≠ q := color_ne hn hq (by decide)
      have plq : Q.l ≠ q := color_ne hl hq (by decide)
      have pnl : n ≠ Q.l := color_ne hn hl (by decide)
      have p_not_fourth {z : V} (hzn : z ≠ n) (hzl : z ≠ Q.l)
          (hzq : z ≠ q) : ¬ G.Adj p z :=
        C.not_adj_fourth_neighbor (Or.inl hp) hnp.symm hpl hpq
          pnl pnq plq hzn hzl hzq
      have hpm : ¬ G.Adj p Q.m := p_not_fourth
        hmn.ne
        Q.hlm.symm (color_ne hm hq (by decide))
      have hpc : ¬ G.Adj p c := p_not_fourth
        hnc.symm (color_ne hc hl (by decide))
        (color_ne hc hq (by decide))
      have hpd : ¬ G.Adj p d := p_not_fourth
        hnd.symm (color_ne hd hl (by decide))
        (color_ne hd hq (by decide))
      have hk_not {z : V} (hzc : z ≠ c) (hzl : z ≠ Q.l)
          (hzm : z ≠ Q.m) : ¬ G.Adj Q.k z :=
        not_adj_fourth_neighbor_of_subcubic C.subcubic Q.hck.symm Q.hkl Q.hkm
          Q.hlc.symm Q.hmc.symm Q.hlm hzc hzl hzm
      have he_not {z : V} (hzf : z ≠ f) (hzd : z ≠ d)
          (hzj : z ≠ Q.j) : ¬ G.Adj e z :=
        C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
          (hv (u := (5 : Fin 8)) (v := 3) (by decide))
          (color_ne hf Q.hj (by decide)) (color_ne hd Q.hj (by decide))
          hzf hzd hzj
      have hlj : Q.l ≠ Q.j := by
        intro h
        apply hpj
        simpa [h] using hpl
      have hpeV : p ≠ e := by
        intro h
        have hel : G.Adj e Q.l := by simpa [h] using hpl
        exact (he_not (color_ne hl hf (by decide))
          (color_ne hl hd (by decide)) hlj) hel
      have hptr := containsPositiveS C Q.hk hp he hl hm hn hc hd Q.hj
        Q.hkl Q.hkm Q.hck.symm hpl hnp.symm hde.symm Q.hej hmn hcd
        (C.reddish_not_adj_redSide Q.hk (Or.inl hp))
        (C.reddish_not_adj_redSide Q.hk (Or.inl he))
        (hk_not hnc (color_ne hn hl (by decide)) hmn.ne.symm)
        (by simpa [SimpleGraph.adj_comm] using hdk)
        (by simpa [SimpleGraph.adj_comm] using Q.hkj)
        hpe hpm hpc hpd hpj
        (he_not (color_ne hl hf (by decide)) (color_ne hl hd (by decide)) hlj)
        (he_not (color_ne hm hf (by decide)) hmd
          (color_ne hm Q.hj (by decide)))
        (he_not (color_ne hn hf (by decide)) hnd
          (color_ne hn Q.hj (by decide)))
        (he_not (color_ne hc hf (by decide)) hcd.ne
          (color_ne hc Q.hj (by decide)))
        (by
          simp [color_ne Q.hk hp (by decide), color_ne Q.hk he (by decide),
            color_ne Q.hk hl (by decide), color_ne Q.hk hm (by decide),
            color_ne Q.hk hn (by decide), color_ne Q.hk hc (by decide),
            color_ne Q.hk hd (by decide), color_ne Q.hk Q.hj (by decide),
            color_ne hp hl (by decide),
            color_ne hp hm (by decide), color_ne hp hn (by decide),
            color_ne hp hc (by decide), color_ne hp hd (by decide),
            color_ne hp Q.hj (by decide), color_ne he hl (by decide),
            color_ne he hm (by decide), color_ne he hn (by decide),
            color_ne he hc (by decide), color_ne he hd (by decide),
            color_ne he Q.hj (by decide), color_ne hl hm (by decide),
            color_ne hl hn (by decide), color_ne hl hc (by decide),
            color_ne hl hd (by decide), color_ne hm Q.hj (by decide),
            hmn.ne, color_ne hn Q.hj (by decide), color_ne hc Q.hj (by decide),
            color_ne hd Q.hj (by decide)]
          exact ⟨hpeV, hlj, ⟨Q.hmc, hmd⟩, ⟨hnc, hnd⟩, hcd.ne⟩)
      exact (noPTR hptr).elim
    · exact hgoal.2.false ⟨Q, hl, hm, n, hn, hmn, o, ho, hmo, hok, hon,
        p, hp, hnp, hma, hna, hmb, hnb, hmf, hnf, hmi, hni,
        hnc, hnd, hng, hnh, hpl, hpg, hph, hpj⟩
  · have m_other : ∀ z, G.Adj Q.m z → z ≠ n → C.swapSides.color z = .bluish := by
      intro z hmz hzn
      have hz := C.neighbor_eq_of_three_neighbors (Or.inr hm)
        hmn Q.hkm.symm hmo (color_ne hn Q.hk (by decide))
        (color_ne hn ho (by decide)) hon.symm hmz
      rcases hz with rfl | rfl | rfl
      · exact (hzn rfl).elim
      · simp [Q.hk]
      · simp [ho]
    have n_other : ∀ z, G.Adj n z → z ≠ Q.m → C.swapSides.color z = .bluish := by
      intro z hnz hzm
      have hzSide := C.other_neighbor_of_blue_is_redSide hn hm hmn.symm hnz hzm
      rcases hzSide with hz | hz
      · exact (hpred ⟨z, hnz, hz⟩).elim
      · simp [hz]
    have hptrSwap := lemma4_4 C.swapSides (by simp [hm]) (by simp [hn]) hmn
      (degree_of_color (Or.inr hm)) (degree_of_color (Or.inr hn))
      m_other n_other
    exact (noPTR ((containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
      hptrSwap)).elim

/-- Case (3.4.3.3.2.2).  Flip `np`, recompute only the colors needed by
the local argument, and restart Case (3.4.3.1). -/
theorem lemma4_8_case_lm_mixed_complete
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma4_8MixedPConfiguration C a b c d e f g h) :
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
  dsimp [FormsInducedPath8] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hpPath : FormsInducedPath8 G a b c d e f g h := ⟨hinj, hedge⟩
  have hv {u v : Fin 8} (huv : u ≠ v) :
      (![a, b, c, d, e, f, g, h] u) ≠
        (![a, b, c, d, e, f, g, h] v) := hinj.ne huv
  have edge (u v : Fin 8) (huv : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7)]).Adj u v) :
      G.Adj (![a, b, c, d, e, f, g, h] u)
        (![a, b, c, d, e, f, g, h] v) := (hedge u v).mp huv
  have hab := edge 0 1 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
    intro hxyV
    subst y
    simp_all
  have hpCorrect := C.color_correct Q.p
  rw [Q.hp] at hpCorrect
  obtain ⟨_, q, hqSide, hpq⟩ := hpCorrect
  have hqSide' := (C.mem_redSide_iff q).1 hqSide
  have hq : C.color q = .red := by
    rcases hqSide' with hq | hq
    · exact hq
    · exact (C.reddish_not_adj_redSide hq (Or.inl Q.hp) hpq.symm).elim
  rcases exists_flipAt_or_cutEnhancer C Q.hp Q.hn hq Q.hm
      (degree_of_color (Or.inl Q.hp)) (degree_of_color (Or.inr Q.hn))
      hpq Q.hnp.symm Q.hmn.symm with hflip | hce
  · obtain ⟨M, hflip⟩ := hflip
    let D := M.toGoodColoring
    have hen : ¬ G.Adj e Q.n := by
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
      · exact color_ne hf Q.hj (by decide)
      · exact color_ne hd Q.hj (by decide)
      · exact color_ne Q.hn hf (by decide)
      · exact Q.hnd
      · exact color_ne Q.hn Q.hj (by decide)
    have hap : a ≠ Q.p := by
      intro h
      apply Q.hna
      simpa [h] using Q.hnp
    have hbp : b ≠ Q.p := by
      intro h
      apply Q.hnb
      simpa [h] using Q.hnp
    have hepV : e ≠ Q.p := by
      intro h
      apply hen
      simpa [h] using Q.hnp.symm
    have hfp : f ≠ Q.p := by
      intro h
      apply Q.hnf
      simpa [h] using Q.hnp
    have haD : D.color a = .red := by
      exact red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hap (color_ne ha Q.hn (by decide)) hbp (color_ne hb Q.hn (by decide))
    have hbD : D.color b = .red := by
      exact red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hbp (color_ne hb Q.hn (by decide)) hap (color_ne ha Q.hn (by decide))
    have hcD : D.color c = .blue := by
      exact blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (color_ne hc Q.hp (by decide)) Q.hnc.symm
        (color_ne hd Q.hp (by decide)) Q.hnd.symm
    have hdD : D.color d = .blue := by
      exact blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (color_ne hd Q.hp (by decide)) Q.hnd.symm
        (color_ne hc Q.hp (by decide)) Q.hnc.symm
    have heD : D.color e = .red := by
      exact red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf]) hef
        hepV (color_ne he Q.hn (by decide)) hfp (color_ne hf Q.hn (by decide))
    have hfD : D.color f = .red := by
      exact red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he]) hef.symm
        hfp (color_ne hf Q.hn (by decide)) hepV (color_ne he Q.hn (by decide))
    have hgD : D.color g = .blue := by
      exact blue_of_untouched_blue_edge C hflip (by simp [hg]) (by simp [hh]) hgh
        (color_ne hg Q.hp (by decide)) Q.hng.symm
        (color_ne hh Q.hp (by decide)) Q.hnh.symm
    have hhD : D.color h = .blue := by
      exact blue_of_untouched_blue_edge C hflip (by simp [hh]) (by simp [hg]) hgh.symm
        (color_ne hh Q.hp (by decide)) Q.hnh.symm
        (color_ne hg Q.hp (by decide)) Q.hng.symm
    have hiD : D.color Q.i = .reddish := by
      apply reddish_of_untouched_reddish C hflip Q.hi
        (by simpa [SimpleGraph.adj_comm] using Q.hni)
      · exact color_ne Q.hi Q.hp (by decide)
      · exact color_ne Q.hi Q.hn (by decide)
    have hjD : D.color Q.j = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hj
        (by simpa [SimpleGraph.adj_comm] using Q.hpj)
      · exact color_ne Q.hj Q.hp (by decide)
      · exact color_ne Q.hj Q.hn (by decide)
    have hkn : ¬ G.Adj Q.k Q.n := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hck.symm Q.hkl Q.hkm Q.hlc.symm Q.hmc.symm Q.hlm
      · exact Q.hnc
      · exact color_ne Q.hn Q.hl (by decide)
      · exact Q.hmn.ne.symm
    have hkD : D.color Q.k = .reddish := by
      apply reddish_of_untouched_reddish C hflip Q.hk hkn
      · exact color_ne Q.hk Q.hp (by decide)
      · exact color_ne Q.hk Q.hn (by decide)
    have hlD : D.color Q.l = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hl
        (by simpa [SimpleGraph.adj_comm] using Q.hpl)
      · exact color_ne Q.hl Q.hp (by decide)
      · exact color_ne Q.hl Q.hn (by decide)
    have hmp : ¬ G.Adj Q.m Q.p := by
      apply C.not_adj_fourth_neighbor (Or.inr Q.hm) Q.hmn Q.hkm.symm Q.hmo
      · exact color_ne Q.hn Q.hk (by decide)
      · exact Q.hok.symm
      · exact Q.hon.symm
      · exact Q.hnp.ne.symm
      · exact color_ne Q.hp Q.hk (by decide)
      · exact color_ne Q.hp Q.ho (by decide)
    have hmD : D.color Q.m = .bluish := by
      apply bluish_of_blue_loses_flipped_mate C hflip Q.hm Q.hmn
        (by simpa [SimpleGraph.adj_comm] using hmp)
      · exact color_ne Q.hm Q.hp (by decide)
      · exact Q.hmn.ne
    have hresult := lemma4_8_case_lm_bluish_restart C D hpPath
      haD hbD hcD hdD heD hfD hgD hhD Q.toLemma4_8LMConfiguration
      hiD hjD hkD hlD hmD
    exact HasReachableReduction.after_flip C hflip hresult
  · exact HasReachableReduction.of_current_ce C hce

end Subcubic
