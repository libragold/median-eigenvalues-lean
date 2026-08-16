import Subcubic.Lemma5_9.CaseBluish
import Subcubic.Lemma5_4

/-! Case (3.4.3.3): one exposed neighbor of `k` is bluish and one is blue. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9MixedPConfiguration (C : MatchingCutColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9LMConfiguration C a b c d e f g h where
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
  hpg : ¬ G.Adj p g
  hph : ¬ G.Adj p h
  hpj : ¬ G.Adj p j

theorem lemma5_9_case_lm_mixed_setup
    (C : MatchingCutColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma5_9LMConfiguration C a b c d e f g h)
    (hl : C.color Q.l = .bluish) (hm : C.color Q.m = .blue) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9MixedPConfiguration C a b c d e f g h) := by
  classical
  by_contra hgoal
  push Not at hgoal
  have noResult (h : HasReachableNegativeReduction C) : False := hgoal.1 h
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (noResult (.of_current_ntr C hntr)).elim
    · exact (noResult (.of_current_ce C hce)).elim
  have noCE (hce : ContainsCutEnhancer C) : False :=
    noResult (HasReachableNegativeReduction.of_current_ce C hce)
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
    C.exists_third_neighbor (degreeC (Or.inr hm)) hnk
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
    exact hgoal.2.false ⟨Q, hl, hm, n, hn, hmn, o, ho, hmo, hok, hon,
        p, hp, hnp, hma, hna, hmb, hnb, hmf, hnf, hmi, hni,
        hnc, hnd, hng, hnh, hpg, hph, hpj⟩
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
    have hresultSwap := lemma5_4 C.swapSides (by simp [hm]) (by simp [hn]) hmn
      m_other n_other
    exact (noResult (HasReachableNegativeReduction.of_swapSides C hresultSwap)).elim

end Subcubic
