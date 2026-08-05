import Subcubic.Lemma5_9.CaseMixedSetup

/-! Lemma 5.9, Case (3.4.4.3.2.1): the red neighbor `p` meets `l`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_lm_mixed_adjacent
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma5_9MixedPConfiguration C a b c d e f g h)
    (hpl : G.Adj Q.p Q.l) :
    HasReachableNegativeReduction C := by
  classical
  by_contra hgoal
  have noResult (hr : HasReachableNegativeReduction C) : False := hgoal hr
  have noCE (hce : ContainsCutEnhancer C) : False :=
    noResult (HasReachableNegativeReduction.of_current_ce C hce)
  have noNTR (hntr : ContainsNegativeTailReducer C) : False :=
    noResult (HasReachableNegativeReduction.of_current_ntr C hntr)
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

  have hla : ¬ G.Adj Q.l a := by
    intro hla
    have hdj : ¬ G.Adj d Q.j :=
      C.bluish_not_adj_blueSide Q.hj (Or.inl hd) ∘ SimpleGraph.Adj.symm
    have hdl : ¬ G.Adj d Q.l :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hd) ∘ SimpleGraph.Adj.symm
    have hdn : ¬ G.Adj d Q.n :=
      C.blueSide_not_adj_second_neighbor
        (by simp [hd]) (by simp [hc]) (by simp [Q.hn]) hcd.symm Q.hnc.symm
    have hda : ¬ G.Adj d a := by simpa using nonedge 3 0 (by native_decide)
    have hne : ¬ G.Adj Q.n e := by
      rw [SimpleGraph.adj_comm]
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
      · exact color_ne hf Q.hj (by decide)
      · exact color_ne hd Q.hj (by decide)
      · exact color_ne Q.hn hf (by decide)
      · exact Q.hnd
      · exact color_ne Q.hn Q.hj (by decide)
    have hdp : ¬ G.Adj d Q.p := by
      apply C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde Q.hdi
      · exact hv (u := (2 : Fin 8)) (v := 4) (by decide)
      · exact color_ne hc Q.hi (by decide)
      · exact color_ne he Q.hi (by decide)
      · exact color_ne Q.hp hc (by decide)
      · intro h
        change Q.p = e at h
        apply hne
        convert Q.hnp using 1
        exact h.symm
      · exact color_ne Q.hp Q.hi (by decide)
    have hjl : ¬ G.Adj Q.j Q.l :=
      C.bluish_not_adj_blueSide Q.hj (Or.inr Q.hl)
    have hjn : ¬ G.Adj Q.j Q.n :=
      C.bluish_not_adj_blueSide Q.hj (Or.inl Q.hn)
    have hln : ¬ G.Adj Q.l Q.n :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hn)
    have hle : ¬ G.Adj Q.l e := by
      rw [SimpleGraph.adj_comm]
      apply C.not_adj_fourth_neighbor (Or.inl he) hef hde.symm Q.hej
      · exact hv (u := (5 : Fin 8)) (v := 3) (by decide)
      · exact color_ne hf Q.hj (by decide)
      · exact color_ne hd Q.hj (by decide)
      · exact color_ne Q.hl hf (by decide)
      · exact color_ne Q.hl hd (by decide)
      · exact fun h => Q.hkj (by simpa [h] using Q.hkl)
    have hea : ¬ G.Adj e a := by simpa using nonedge 4 0 (by native_decide)
    have hep : ¬ G.Adj e Q.p :=
      C.redSide_not_adj_second_neighbor
        (by simp [he]) (by simp [hf]) (by simp [Q.hp]) hef
        (by
          intro h
          change f = Q.p at h
          apply Q.hnf
          convert Q.hnp using 1)
    have hap : ¬ G.Adj a Q.p :=
      C.redSide_not_adj_second_neighbor
        (by simp [ha]) (by simp [hb]) (by simp [Q.hp]) hab
        (by
          intro h
          change b = Q.p at h
          apply Q.hnb
          convert Q.hnp using 1)
    have hjlV : Q.j ≠ Q.l := by
      intro h
      apply Q.hkj
      simpa [h] using Q.hkl
    have hepV : e ≠ Q.p := by
      intro h
      change e = Q.p at h
      apply hne
      convert Q.hnp using 1
    have hapV : a ≠ Q.p := by
      intro h
      change a = Q.p at h
      apply Q.hna
      convert Q.hnp using 1
    have heaV : e ≠ a := (hv (u := (0 : Fin 8)) (v := 4) (by decide)).symm
    have hnodup : [d, Q.j, Q.l, Q.n, e, a, Q.p].Nodup := by
      simp [color_ne hd Q.hj (by decide), color_ne hd Q.hl (by decide),
        Q.hnd.symm, color_ne hd he (by decide), color_ne hd ha (by decide),
        color_ne hd Q.hp (by decide),
        hjlV,
        color_ne Q.hj Q.hn (by decide), color_ne Q.hj he (by decide),
        color_ne Q.hj ha (by decide), color_ne Q.hj Q.hp (by decide),
        color_ne Q.hl Q.hn (by decide), color_ne Q.hl he (by decide),
        color_ne Q.hl ha (by decide), color_ne Q.hl Q.hp (by decide),
        color_ne Q.hn he (by decide), color_ne Q.hn ha (by decide),
        color_ne Q.hn Q.hp (by decide),
        heaV, hepV, hapV]
    have hceSwap := containsCutEnhancerF_of C.swapSides
      (by simp [hd]) (by simp [Q.hj]) (by simp [Q.hl])
      (by simp [Q.hn]) (by simp [he]) (by simp [ha]) (by simp [Q.hp])
      hde Q.hej.symm Q.hja hla hpl.symm Q.hnp
      (by simpa [SimpleGraph.adj_comm] using hdj)
      (by simpa [SimpleGraph.adj_comm] using hdl) hdn
      (by simpa [SimpleGraph.adj_comm] using hda)
      (by simpa [SimpleGraph.adj_comm] using hdp) hjl hjn
      (by simpa [SimpleGraph.adj_comm] using Q.hpj) hln hle
      hne (by simpa [SimpleGraph.adj_comm] using Q.hna)
      hea hep hap hnodup
    exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)

  have hapV : a ≠ Q.p := by
    intro hap
    have hna : G.Adj Q.n a := by
      convert Q.hnp using 1
    exact Q.hna hna
  have hbp : ¬ G.Adj b Q.p :=
    C.redSide_not_adj_second_neighbor
      (by simp [hb]) (by simp [ha]) (by simp [Q.hp]) hab.symm hapV
  have hbpV : b ≠ Q.p := by
    intro h
    apply Q.hnb
    convert Q.hnp using 1
  have hcp : ¬ G.Adj c Q.p := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hck
    · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
    · exact color_ne hd Q.hk (by decide)
    · exact color_ne hb Q.hk (by decide)
    · exact color_ne Q.hp hd (by decide)
    · exact hbpV.symm
    · exact color_ne Q.hp Q.hk (by decide)
  have hcn : ¬ G.Adj c Q.n :=
    C.blueSide_not_adj_second_neighbor
      (by simp [hc]) (by simp [hd]) (by simp [Q.hn]) hcd Q.hnd.symm
  have hlb : ¬ G.Adj Q.l b := by
    intro hlb
    have hlc : ¬ G.Adj Q.l c :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hc)
    have hln : ¬ G.Adj Q.l Q.n :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hn)
    have hceSwap := containsCutEnhancerB_of C.swapSides
      (by simp [Q.hl]) (by simp [hb]) (by simp [hc])
      (by simp [Q.hp]) (by simp [Q.hn])
      hlb hpl.symm hbc Q.hnp.symm
      (by simpa [SimpleGraph.adj_comm] using hlc) hln
      (by simpa [SimpleGraph.adj_comm] using hbp)
      (by simpa [SimpleGraph.adj_comm] using Q.hnb) hcp hcn
    exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
  have hfpV : f ≠ Q.p := by
    intro h
    apply Q.hnf
    convert Q.hnp using 1
  have hfp : ¬ G.Adj f Q.p :=
    C.redSide_not_adj_second_neighbor
      (by simp [hf]) (by simp [he]) (by simp [Q.hp]) hef.symm
      (by
        intro hep
        apply Q.hpj
        convert Q.hej using 1
        exact hep.symm)
  have hgn : ¬ G.Adj g Q.n :=
    C.blueSide_not_adj_second_neighbor
      (by simp [hg]) (by simp [hh]) (by simp [Q.hn]) hgh Q.hnh.symm
  have hlf : ¬ G.Adj Q.l f := by
    intro hlf
    have hlg : ¬ G.Adj Q.l g :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl hg)
    have hln : ¬ G.Adj Q.l Q.n :=
      C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hn)
    have hceSwap := containsCutEnhancerB_of C.swapSides
      (by simp [Q.hl]) (by simp [hf]) (by simp [hg])
      (by simp [Q.hp]) (by simp [Q.hn])
      hlf hpl.symm hfg Q.hnp.symm
      (by simpa [SimpleGraph.adj_comm] using hlg) hln
      (by simpa [SimpleGraph.adj_comm] using hfp)
      (by simpa [SimpleGraph.adj_comm] using Q.hnf)
      (by simpa [SimpleGraph.adj_comm] using Q.hpg) hgn
    exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)

  -- The rest of this branch starts by exposing the third neighbor of `l`.
  rcases lemma3_5 C.swapSides (by simp [Q.hn]) (by simp [Q.hp])
      (by simp [Q.hl]) Q.hnp hpl with hldeg | hce
  · obtain ⟨q, hlq, hqk, hqp⟩ :=
      exists_third_neighbor_of_degree_three hldeg
        (color_ne Q.hk Q.hp (by decide))
    have hqSide : C.color q = .red ∨ C.color q = .reddish := by
      rw [← C.mem_redSide_iff]
      by_contra hqMem
      exact C.bluish_not_adj_blueSide Q.hl
        ((C.not_mem_redSide_iff q).1 hqMem) hlq
    -- The red and reddish alternatives are completed below.
    rcases hqSide with hq | hq
    · have hqa : q ≠ a := by
        intro h
        apply hla
        convert hlq using 1
        exact h.symm
      have hqb : ¬ G.Adj q b :=
        by simpa [SimpleGraph.adj_comm] using
          C.redSide_not_adj_second_neighbor
            (by simp [hb]) (by simp [ha]) (by simp [hq]) hab.symm hqa.symm
      have hqbV : q ≠ b := by
        intro h
        apply hlb
        convert hlq using 1
        exact h.symm
      have hmp : ¬ G.Adj Q.m Q.p := by
        apply C.not_adj_fourth_neighbor (Or.inr Q.hm)
          Q.hmn Q.hkm.symm Q.hmo
        · exact color_ne Q.hn Q.hk (by decide)
        · exact color_ne Q.hn Q.ho (by decide)
        · exact Q.hon.symm
        · exact Q.hnp.ne.symm
        · exact color_ne Q.hp Q.hk (by decide)
        · exact color_ne Q.hp Q.ho (by decide)
      have hmq : ¬ G.Adj Q.m q := by
        apply C.not_adj_fourth_neighbor (Or.inr Q.hm)
          Q.hmn Q.hkm.symm Q.hmo
        · exact color_ne Q.hn Q.hk (by decide)
        · exact color_ne Q.hn Q.ho (by decide)
        · exact Q.hon.symm
        · exact color_ne hq Q.hn (by decide)
        · exact color_ne hq Q.hk (by decide)
        · exact color_ne hq Q.ho (by decide)
      have hcq : ¬ G.Adj c q := by
        apply C.not_adj_fourth_neighbor (Or.inr hc) hcd hbc.symm Q.hck
        · exact hv (u := (3 : Fin 8)) (v := 1) (by decide)
        · exact color_ne hd Q.hk (by decide)
        · exact color_ne hb Q.hk (by decide)
        · exact color_ne hq hd (by decide)
        · exact hqbV
        · exact color_ne hq Q.hk (by decide)
      have hmc : ¬ G.Adj Q.m c :=
        C.blueSide_not_adj_second_neighbor
          (by simp [Q.hm]) (by simp [Q.hn]) (by simp [hc]) Q.hmn Q.hnc
      have hkp : ¬ G.Adj Q.k Q.p :=
        C.reddish_not_adj_redSide Q.hk (Or.inl Q.hp)
      have hkq : ¬ G.Adj Q.k q :=
        C.reddish_not_adj_redSide Q.hk (Or.inl hq)
      have hkb : ¬ G.Adj Q.k b :=
        C.reddish_not_adj_redSide Q.hk (Or.inl hb)
      have hlm : ¬ G.Adj Q.l Q.m :=
        C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hm)
      have hlc : ¬ G.Adj Q.l c :=
        C.bluish_not_adj_blueSide Q.hl (Or.inl hc)
      by_cases hpq : G.Adj Q.p q
      · have hlo : ¬ G.Adj Q.l Q.o := by
          apply not_adj_fourth_neighbor_of_degree_three hldeg
            Q.hkl.symm hpl.symm hlq
          · exact color_ne Q.hk Q.hp (by decide)
          · exact hqk.symm
          · exact hqp.symm
          · exact Q.hon
          · exact color_ne Q.ho Q.hp (by decide)
          · exact color_ne Q.ho hq (by decide)
        have hntrSwap := containsNegativeH C.swapSides
          (by simp [Q.hm]) (by simp [Q.hl]) (by simp [Q.ho])
          (by simp [Q.hk]) (by simp [Q.hp]) (by simp [hq])
          Q.hmo Q.hkm.symm Q.hkl.symm hpl.symm hlq hpq
          (by simpa [SimpleGraph.adj_comm] using hlm)
          (by simpa [SimpleGraph.adj_comm] using hmp)
          (by simpa [SimpleGraph.adj_comm] using hmq) hlo
          (by
            simp [color_ne Q.hm Q.hl (by decide),
              color_ne Q.hm Q.ho (by decide), color_ne Q.hm Q.hk (by decide),
              color_ne Q.hm Q.hp (by decide), color_ne Q.hm hq (by decide),
              color_ne Q.hl Q.ho (by decide), color_ne Q.hl Q.hk (by decide),
              color_ne Q.hl Q.hp (by decide), color_ne Q.hl hq (by decide),
              color_ne Q.ho Q.hp (by decide), color_ne Q.ho hq (by decide),
              Q.hon, color_ne Q.hk Q.hp (by decide),
              color_ne Q.hk hq (by decide), hpq.ne])
        exact noNTR ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
          hntrSwap)
      · have hnodup : [Q.p, q, Q.k, b, Q.l, Q.m, c].Nodup := by
          simp [hqp.symm, hbpV.symm, hqbV, color_ne Q.hp Q.hk (by decide),
            color_ne Q.hp Q.hl (by decide), color_ne Q.hp Q.hm (by decide),
            color_ne Q.hp hc (by decide), color_ne hq Q.hk (by decide),
            color_ne hq Q.hl (by decide), color_ne hq Q.hm (by decide),
            color_ne hq hc (by decide), color_ne Q.hk hb (by decide),
            color_ne Q.hk Q.hl (by decide), color_ne Q.hk Q.hm (by decide),
            color_ne Q.hk hc (by decide), color_ne hb Q.hl (by decide),
            color_ne hb Q.hm (by decide), color_ne hb hc (by decide),
            color_ne Q.hl Q.hm (by decide), color_ne Q.hl hc (by decide),
            Q.hmc]
        exact noCE (containsCutEnhancerG_of C Q.hp hq Q.hk hb Q.hl Q.hm hc
          hpl hlq.symm Q.hkl Q.hkm Q.hck.symm hbc
          hpq (by simpa [SimpleGraph.adj_comm] using hkp)
          (by simpa [SimpleGraph.adj_comm] using hbp)
          (by simpa [SimpleGraph.adj_comm] using hmp)
          (by simpa [SimpleGraph.adj_comm] using hcp)
          (by simpa [SimpleGraph.adj_comm] using hkq) hqb
          (by simpa [SimpleGraph.adj_comm] using hmq)
          (by simpa [SimpleGraph.adj_comm] using hcq) hkb
          (by simpa [SimpleGraph.adj_comm] using hlb)
          (by simpa [SimpleGraph.adj_comm] using Q.hmb)
          hlm hlc hmc hnodup)
    · -- This is the prose's third neighbor `q` of `n` (named `r` here
      -- because `q` already denotes the third neighbor of `l`).
      obtain ⟨r, hnr, hrm, hrp⟩ :=
        C.exists_third_neighbor (Or.inr Q.hn)
          (color_ne Q.hm Q.hp (by decide))
      have hrSide : C.color r = .red ∨ C.color r = .reddish :=
        C.other_neighbor_of_blue_is_redSide Q.hn Q.hm Q.hmn.symm hnr hrm
      have hr : C.color r = .reddish := by
        rcases hrSide with hr | hr
        · -- If `r` were red, `n,p,r` induce reversed negative `a1`
          -- when `p ~ r`, and reversed cut enhancer `a` otherwise.
          by_cases hpr : G.Adj Q.p r
          · have hntrSwap := containsNegativeA1 C.swapSides
              (by simp [Q.hn]) (by simp [Q.hp]) (by simp [hr])
              Q.hnp hnr hpr
              (by
                simp [color_ne Q.hn Q.hp (by decide),
                  color_ne Q.hn hr (by decide), hpr.ne])
            exact (noNTR ((containsInducedUpToSwap_swapSides
              IsNegativeTailReducer C).1 hntrSwap)).elim
          · have hceSwap := containsCutEnhancerA_of C.swapSides
              (by simp [Q.hn]) (by simp [Q.hp]) (by simp [hr])
              Q.hnp hnr hrp.symm hpr
            exact (noCE ((containsInducedUpToSwap_swapSides
              IsCutEnhancer C).1 hceSwap)).elim
        · exact hr
      have hmp : ¬ G.Adj Q.m Q.p := by
        apply C.not_adj_fourth_neighbor (Or.inr Q.hm)
          Q.hmn Q.hkm.symm Q.hmo
        · exact color_ne Q.hn Q.hk (by decide)
        · exact color_ne Q.hn Q.ho (by decide)
        · exact Q.hon.symm
        · exact Q.hnp.ne.symm
        · exact color_ne Q.hp Q.hk (by decide)
        · exact color_ne Q.hp Q.ho (by decide)
      have hnl : ¬ G.Adj Q.n Q.l :=
        by simpa [SimpleGraph.adj_comm] using
          C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hn)
      have hml : ¬ G.Adj Q.m Q.l :=
        by simpa [SimpleGraph.adj_comm] using
          C.bluish_not_adj_blueSide Q.hl (Or.inl Q.hm)
      have hkn : ¬ G.Adj Q.k Q.n := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic
          Q.hck.symm Q.hkl Q.hkm
        · exact Q.hlc.symm
        · exact Q.hmc.symm
        · exact Q.hlm
        · exact Q.hnc
        · exact color_ne Q.hn Q.hl (by decide)
        · exact Q.hmn.ne.symm
      have hnk : ¬ G.Adj Q.n Q.k := by
        simpa [SimpleGraph.adj_comm] using hkn
      have hpk : ¬ G.Adj Q.p Q.k :=
        by simpa [SimpleGraph.adj_comm] using
          C.reddish_not_adj_redSide Q.hk (Or.inl Q.hp)
      have hlm' : ¬ G.Adj Q.l Q.m := by
        simpa [SimpleGraph.adj_comm] using hml
      have hkp : ¬ G.Adj Q.k Q.p := by
        simpa [SimpleGraph.adj_comm] using hpk
      have hpentagon : FormsInducedPentagon G Q.n Q.m Q.l Q.p Q.k := by
        unfold FormsInducedPentagon
        have hn : [Q.n, Q.m, Q.l, Q.p, Q.k].Nodup := by
          simp [Q.hmn.ne.symm, color_ne Q.hn Q.hl (by decide),
            color_ne Q.hn Q.hp (by decide), color_ne Q.hn Q.hk (by decide),
            color_ne Q.hm Q.hl (by decide), color_ne Q.hm Q.hp (by decide),
            color_ne Q.hm Q.hk (by decide), color_ne Q.hl Q.hp (by decide),
            color_ne Q.hl Q.hk (by decide), color_ne Q.hp Q.hk (by decide)]
        constructor
        · intro u v huv
          apply hn.injective_get
          fin_cases u <;> fin_cases v <;> exact huv
        · intro u v
          fin_cases u <;> fin_cases v <;>
            simp [graphOfEdges, G.adj_comm, Q.hmn.symm, Q.hnp,
              Q.hkm, hpl.symm, Q.hkl, hnl, hkn, hlm', hmp, hkp]
      have nNoBlue : ∀ v, G.Adj Q.n v → v ≠ Q.p → v ≠ Q.k →
          C.swapSides.color v ≠ .blue := by
        intro v hnv hvp _hvk
        have hvCases := C.neighbor_eq_of_three_neighbors (Or.inr Q.hn)
          Q.hmn.symm Q.hnp hnr
          (color_ne Q.hm Q.hp (by decide)) hrm.symm hrp.symm hnv
        rcases hvCases with rfl | rfl | rfl
        · simp [Q.hm]
        · exact (hvp rfl).elim
        · simp [hr]
      have mNoBlue : ∀ v, G.Adj Q.m v → v ≠ Q.p → v ≠ Q.k →
          C.swapSides.color v ≠ .blue := by
        intro v hmv _hvp hvk
        have hvCases := C.neighbor_eq_of_three_neighbors (Or.inr Q.hm)
          Q.hmn Q.hkm.symm Q.hmo
          (color_ne Q.hn Q.hk (by decide))
          (color_ne Q.hn Q.ho (by decide)) Q.hon.symm hmv
        rcases hvCases with rfl | rfl | rfl
        · simp [Q.hn]
        · exact (hvk rfl).elim
        · simp [Q.ho]
      have lNoBlue : ∀ v, G.Adj Q.l v → v ≠ Q.p → v ≠ Q.k →
          C.swapSides.color v ≠ .blue := by
        intro v hlv hvp hvk
        by_cases hvq : v = q
        · subst v
          simp [hq]
        · exact (not_adj_fourth_neighbor_of_degree_three hldeg
            Q.hkl.symm hpl.symm hlq
            (color_ne Q.hk Q.hp (by decide)) hqk.symm hqp.symm
            hvk hvp hvq hlv).elim
      rcases lemma5_5 C.swapSides hpentagon
          (by simp [Q.hn]) (by simp [Q.hm]) (by simp [Q.hl])
          (by simp [Q.hp]) (Or.inr (by simp [Q.hk]))
          nNoBlue mNoBlue lNoBlue with hntr | hce
      · exact noNTR ((containsInducedUpToSwap_swapSides
          IsNegativeTailReducer C).1 hntr)
      · exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hce)
  · exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hce)

end Subcubic
