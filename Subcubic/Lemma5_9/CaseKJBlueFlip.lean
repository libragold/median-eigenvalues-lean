import Subcubic.Lemma5_9.CaseKJBlueSetup

/-!
# Lemma 5.9, Case (3.4.2): flip the blue edge's red neighbor

After flipping `mn`, the former blue vertex `l` is bluish.  The vertex `j`
stays bluish because its three neighbors `a,e,k` exclude adjacency to the
flipped red vertex `n`.  Cut enhancer `b` then forces the third neighbor of
`a` to be bluish, and Lemma 3.3 does the same for the third neighbor of `b`.
The resulting induced pentagon is passed to Lemma 5.5.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem restart_kj_with_bluish_l
    (C₀ C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_9KJBlueConfiguration C₀ a b c d e f g h)
    (hk : C.color Q.k = .reddish)
    (hl : C.color Q.l = .bluish)
    (hj : C.color Q.j = .bluish) :
    HasReachableNegativeReduction C := by
  classical
  rcases Q with ⟨⟨⟨⟨⟨i, j, x, y, _, _, _, _, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, hideg, t, ht, hit, htd, hth⟩,
    k, _, hck, hkb, hkd, hkg, hkdeg⟩,
    hkj, l, _, hkl, hlc, hlj, hkdAdj⟩
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
  have haj : G.Adj a j := hja.symm
  have hdjV : d ≠ j := by
    intro q
    apply (nonedge 3 0 (by native_decide))
    rw [q]
    exact hja
  have hcjV : c ≠ j := by
    intro q
    apply (nonedge 0 2 (by native_decide))
    rw [q]
    exact haj

  have finish (hx : C.color x = .bluish) (hy : C.color y = .bluish) :
      HasReachableNegativeReduction C := by
    have hbk : ¬ G.Adj b k :=
      fun q => C.reddish_not_adj_redSide hk (Or.inl hb) q.symm
    have hak : ¬ G.Adj a k :=
      fun q => C.reddish_not_adj_redSide hk (Or.inl ha) q.symm
    have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
    have hcj : ¬ G.Adj c j :=
      fun q => C.bluish_not_adj_blueSide hj (Or.inl hc) q.symm
    have hbj : ¬ G.Adj b j := fun q => hjb q.symm
    have hn : [b, a, k, c, j].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, not_false_eq_true, and_true]
      exact ⟨⟨hab.ne.symm, hkb.symm, hbc.ne,
          vertex_ne_of_color_eq hb hj (by decide)⟩,
        ⟨vertex_ne_of_color_eq ha hk (by decide),
          hv (u := (0 : Fin 8)) (v := 2) (by decide), hja.ne.symm⟩,
        ⟨hck.ne.symm, hkj.ne⟩,
        hcjV⟩
    have hpent : FormsInducedPentagon G b a k c j := by
      refine ⟨?_, ?_⟩
      · intro u v huv
        apply hn.injective_get
        fin_cases u <;> fin_cases v <;> exact huv
      intro u v
      fin_cases u <;> fin_cases v <;>
        simp [graphOfEdges, G.adj_comm, hab, hbc, hck, hkj,
          haj, hbk, hbj, hak, hac, hcj]
    have hbNoBlue :
        ∀ v, G.Adj b v → v ≠ c → v ≠ j → C.color v ≠ .blue := by
      intro v hbv hvc hvj hvblue
      rcases C.neighbor_eq_of_three_neighbors (Or.inl hb)
          hab.symm hbc hby
          (hv (u := (0 : Fin 8)) (v := 2) (by decide)) hya.symm hyc.symm hbv with
        rfl | rfl | rfl
      · simp [ha] at hvblue
      · exact (hvc rfl).elim
      · simp [hy] at hvblue
    have haNoBlue :
        ∀ v, G.Adj a v → v ≠ c → v ≠ j → C.color v ≠ .blue := by
      intro v hav hvc hvj hvblue
      have hbjV : b ≠ j := vertex_ne_of_color_eq hb hj (by decide)
      rcases C.neighbor_eq_of_three_neighbors (Or.inl ha)
          hab hja.symm hax
          hbjV hxb.symm hxj.symm hav with rfl | rfl | rfl
      · simp [hb] at hvblue
      · exact (hvj rfl).elim
      · simp [hx] at hvblue
    have hkNoBlue :
        ∀ v, G.Adj k v → v ≠ c → v ≠ j → C.color v ≠ .blue := by
      intro v hkv hvc hvj hvblue
      by_cases hvc' : v = c
      · exact (hvc hvc').elim
      by_cases hvj' : v = j
      · exact (hvj hvj').elim
      by_cases hvl' : v = l
      · subst v; simp [hl] at hvblue
      exact (not_adj_fourth_neighbor_of_degree_three hkdeg
        hck.symm hkj hkl
        hcjV
        hlc.symm hlj.symm hvc' hvj' hvl') hkv |>.elim
    exact lemma5_5 C hpent hb ha hk hc (Or.inr hj)
      hbNoBlue haNoBlue hkNoBlue

  have hxSide := C.other_neighbor_of_red_is_blueSide ha hb hab hax hxb
  rcases hxSide with hx | hx
  · have hjx : ¬ G.Adj j x :=
        C.bluish_not_adj_blueSide hj (Or.inl hx)
    have hjd : ¬ G.Adj j d := C.bluish_not_adj_blueSide hj (Or.inl hd)
    have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
    have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
    have hxe : ¬ G.Adj x e := by
      intro hxe
      exact (C.not_adj_fourth_neighbor (Or.inl he)
        hef hde.symm hej
        (hv (u := (5 : Fin 8)) (v := 3) (by decide))
        (vertex_ne_of_color_eq hf hj (by decide))
        (vertex_ne_of_color_eq hd hj (by decide))
        (by intro q; subst x; exact (nonedge 0 5 (by native_decide)) hax)
        (by intro q; subst x; exact (nonedge 0 3 (by native_decide)) hax)
        hxj) hxe.symm
    have hxc : x ≠ c := by
      intro q; subst x; exact (nonedge 0 2 (by native_decide)) hax
    have hxd : ¬ G.Adj x d := by
      simpa [SimpleGraph.adj_comm] using
        C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
          (by simp [hx]) hcd.symm hxc.symm
    have hceSwap := containsCutEnhancerB_of C.swapSides
      (by simp [hj]) (by simp [ha]) (by simp [hx])
      (by simp [he]) (by simp [hd])
      hja hej.symm hax hde.symm hjx hjd hae had hxe hxd
    exact HasReachableNegativeReduction.of_current_ce C
      ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
  · have hySide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hby hya
    have hyd : y ≠ d := by
      intro q; subst y; exact (nonedge 1 3 (by native_decide)) hby
    rcases lemma3_3 C hb hc hd hySide hbc hby hcd hyc.symm hyd.symm with
      hy | hce
    · exact finish hx hy
    · exact HasReachableNegativeReduction.of_current_ce C hce

theorem lemma5_9_case_kj_blue_flip
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (Q : Lemma5_9KJBlueMConfiguration C a b c d e f g h) :
    HasReachableNegativeReduction C := by
  classical
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  rcases Q with ⟨Q, hkh, hla, m, hm, hlm, n, hn, hmn,
    hma, hmb, hmf, hme, hmi, hnl⟩
  have hnCorrect := C.color_correct n
  rw [hn] at hnCorrect
  obtain ⟨_, r, hrSide, hnr⟩ := hnCorrect
  have hr : C.color r = .red := by
    rcases (C.mem_redSide_iff r).1 hrSide with hr | hr
    · exact hr
    · exact (C.reddish_not_adj_redSide hr (Or.inl hn) hnr.symm).elim
  rcases exists_flipAt_or_cutEnhancer C hn hm hr Q.hl
      (degreeC (Or.inl hn)) (degreeC (Or.inr hm)) hnr hmn.symm hlm.symm with
    ⟨M, hflip⟩ | hce
  · let D := M.toGoodColoring
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
    have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
    have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
    have hde : G.Adj d e := by simpa using edge 3 4 (by native_decide)
    have hef : G.Adj e f := by simpa using edge 4 5 (by native_decide)
    have hnA : n ≠ a := by intro q; subst n; exact hma hmn
    have hnB : n ≠ b := by intro q; subst n; exact hmb hmn
    have hnE : n ≠ e := by intro q; subst n; exact hme hmn
    have hnF : n ≠ f := by intro q; subst n; exact hmf hmn
    have hmA := vertex_ne_of_color_eq hm ha (by decide)
    have hmB := vertex_ne_of_color_eq hm hb (by decide)
    have hmE := vertex_ne_of_color_eq hm he (by decide)
    have hmF := vertex_ne_of_color_eq hm hf (by decide)
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hnA.symm hmA.symm hnB.symm hmB.symm
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hnB.symm hmB.symm hnA.symm hmA.symm
    have heD : D.color e = .red :=
      red_of_untouched_red_edge C hflip (by simp [he]) (by simp [hf])
        hef
        hnE.symm hmE.symm hnF.symm hmF.symm
    have hfD : D.color f = .red :=
      red_of_untouched_red_edge C hflip (by simp [hf]) (by simp [he])
        hef.symm
        hnF.symm hmF.symm hnE.symm hmE.symm
    have hdlV : d ≠ Q.l := by
      intro q
      apply Q.hkdAdj
      simpa [q] using Q.hkl
    have hcl : ¬ G.Adj c Q.l := by
      apply C.blueSide_not_adj_second_neighbor (by simp [hc]) (by simp [hd])
        (by simp [Q.hl]) hcd
      exact hdlV
    have hcM : c ≠ m := by intro q; subst m; exact hcl hlm.symm
    have hdM : d ≠ m := by
      intro q; subst m
      have hdl := C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
        (by simp [Q.hl]) hcd.symm Q.hlc.symm
      exact hdl hlm.symm
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (vertex_ne_of_color_eq hc hn (by decide)) hcM
        (vertex_ne_of_color_eq hd hn (by decide)) hdM
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (vertex_ne_of_color_eq hd hn (by decide)) hdM
        (vertex_ne_of_color_eq hc hn (by decide)) hcM
    have hkm : ¬ G.Adj Q.k m := by
      apply not_adj_fourth_neighbor_of_degree_three Q.hkdeg Q.hck.symm Q.hkj Q.hkl
      · exact vertex_ne_of_color_eq hc Q.hj (by decide)
      · exact Q.hlc.symm
      · exact Q.hlj.symm
      · exact hcM.symm
      · exact vertex_ne_of_color_eq hm Q.hj (by decide)
      · exact hlm.ne.symm
    have hkD : D.color Q.k = .reddish :=
      reddish_of_untouched_reddish C hflip Q.hk hkm
        (vertex_ne_of_color_eq Q.hk hn (by decide))
        (vertex_ne_of_color_eq Q.hk hm (by decide))
    have hlD : D.color Q.l = .bluish :=
      bluish_of_blue_loses_flipped_mate C hflip Q.hl hlm
        (fun q => hnl q.symm)
        (vertex_ne_of_color_eq Q.hl hn (by decide)) hlm.ne
    have hjn : ¬ G.Adj Q.j n := by
      apply not_adj_fourth_neighbor_of_subcubic C.subcubic
        Q.hej.symm Q.hja Q.hkj.symm
      · exact hv (u := (4 : Fin 8)) (v := 0) (by decide)
      · exact vertex_ne_of_color_eq he Q.hk (by decide)
      · exact vertex_ne_of_color_eq ha Q.hk (by decide)
      · exact hnE
      · exact hnA
      · exact vertex_ne_of_color_eq hn Q.hk (by decide)
    have hjD : D.color Q.j = .bluish := by
      apply bluish_of_untouched_bluish C hflip Q.hj hjn
      · exact vertex_ne_of_color_eq Q.hj hn (by decide)
      · exact vertex_ne_of_color_eq Q.hj hm (by decide)
    have hdone := restart_kj_with_bluish_l C D hp haD hbD hcD hdD heD hfD
      Q hkD hlD hjD
    exact HasReachableNegativeReduction.after_flip C hflip hdone
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
