import Subcubic.Lemma4_8.Case3_1

/-! The `ptr-w` case (3.3) of Lemma 4.8. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma4_8_case_w
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red) (hg : C.color g = .blue)
    (hh : C.color h = .blue)
    (Q : Lemma4_8Case3Configuration C a b c d e f g h)
    (hxy : Q.x ≠ Q.y) (hij : ¬ G.Adj Q.i Q.j)
    (hic : G.Adj Q.i c) (hjf : G.Adj Q.j f) :
    HasReachableReduction C := by
  classical
  rcases Q with ⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩
  change x ≠ y at hxy
  change ¬ G.Adj i j at hij
  change G.Adj i c at hic
  change G.Adj j f at hjf
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
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hfg : G.Adj f g := by simpa using edge 5 6 (by native_decide)
  have hgh : G.Adj g h := by simpa using edge 6 7 (by native_decide)
  have hfi : ¬ G.Adj f i :=
    C.reddish_not_adj_redSide hi (Or.inl hf) ∘ SimpleGraph.Adj.symm
  have hfx : ¬ G.Adj f x := by
    apply C.not_adj_fourth_neighbor (v := f) (x := e) (y := g)
      (z := j) (w := x) (Or.inl hf)
      (by simpa using (edge 4 5 (by native_decide)).symm) hfg hjf.symm
    · exact hv (u := (4 : Fin 8)) (v := 6) (by decide)
    · intro hejV
      rw [← hejV] at hj
      simp [he] at hj
    · intro hgj
      rw [← hgj] at hj
      simp [hg] at hj
    · intro hxe
      rw [hxe] at hx
      simp [he] at hx
    · intro hxg
      rw [hxg] at hx
      simp [hg] at hx
    · exact hxj
  have hyj : y ≠ j := by
    intro hyj
    rw [hyj] at hby
    exact hjb hby.symm
  have hfy : ¬ G.Adj f y := by
    apply C.not_adj_fourth_neighbor (v := f) (x := e) (y := g)
      (z := j) (w := y) (Or.inl hf)
      (by simpa using (edge 4 5 (by native_decide)).symm) hfg hjf.symm
    · exact hv (u := (4 : Fin 8)) (v := 6) (by decide)
    · intro hejV
      rw [← hejV] at hj
      simp [he] at hj
    · intro hgj
      rw [← hgj] at hj
      simp [hg] at hj
    · intro hye
      rw [hye] at hy
      simp [he] at hy
    · intro hyg
      rw [hyg] at hy
      simp [hg] at hy
    · exact hyj
  have hfd : ¬ G.Adj f d := by
    simpa using nonedge 5 3 (by native_decide)
  have hfh : ¬ G.Adj f h := by
    simpa using nonedge 5 7 (by native_decide)
  have hix : ¬ G.Adj i x := by
    apply not_adj_fourth_neighbor_of_subcubic C.subcubic hdi.symm hic hih
    · exact hv (u := (3 : Fin 8)) (v := 2) (by decide)
    · exact hv (u := (3 : Fin 8)) (v := 7) (by decide)
    · exact hv (u := (2 : Fin 8)) (v := 7) (by decide)
    · intro hxd; rw [hxd] at hx; simp [hd] at hx
    · intro hxc; rw [hxc] at hx; simp [hc] at hx
    · intro hxh; rw [hxh] at hx; simp [hh] at hx
  have hiy : ¬ G.Adj i y := by
    apply not_adj_fourth_neighbor_of_subcubic C.subcubic hdi.symm hic hih
    · exact hv (u := (3 : Fin 8)) (v := 2) (by decide)
    · exact hv (u := (3 : Fin 8)) (v := 7) (by decide)
    · exact hv (u := (2 : Fin 8)) (v := 7) (by decide)
    · intro hyd; rw [hyd] at hy; simp [hd] at hy
    · exact hyc
    · intro hyh; rw [hyh] at hy; simp [hh] at hy
  have hn : [a, b, f, i, x, y, j, c, d, g, h].Nodup := by
    have hbase : [a, b, c, d, e, f, g, h].Nodup := by
      simpa using List.nodup_ofFn_ofInjective hinj
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true] at hbase
    rcases hbase with ⟨⟨habV, hacV, hadV, haeV, hafV, hagV, hahV⟩,
      ⟨hbcV, hbdV, hbeV, hbfV, hbgV, hbhV⟩,
      ⟨hcdV, hceV, hcfV, hcgV, hchV⟩,
      ⟨hdeV, hdfV, hdgV, hdhV⟩,
      ⟨hefV, hegV, hehV⟩, ⟨hfgV, hfhV⟩, hghV⟩
    have color_ne {u v : V} {cu cv : Color}
        (hu : C.color u = cu) (hv' : C.color v = cv)
        (hne : cu ≠ cv) : u ≠ v := by
      intro huv
      subst v
      exact hne (hu.symm.trans hv')
    have hai := color_ne ha hi (by decide)
    have haxV := color_ne ha hx (by decide)
    have hay := color_ne ha hy (by decide)
    have haj := color_ne ha hj (by decide)
    have hbi := color_ne hb hi (by decide)
    have hbx := color_ne hb hx (by decide)
    have hbyV := color_ne hb hy (by decide)
    have hbj := color_ne hb hj (by decide)
    have hfiV := color_ne hf hi (by decide)
    have hfxV := color_ne hf hx (by decide)
    have hfyV := color_ne hf hy (by decide)
    have hfj := color_ne hf hj (by decide)
    have hfc := color_ne hf hc (by decide)
    have hfdV := color_ne hf hd (by decide)
    have hixV := color_ne hi hx (by decide)
    have hiyV := color_ne hi hy (by decide)
    have hijV := color_ne hi hj (by decide)
    have hicV := color_ne hi hc (by decide)
    have hidV := color_ne hi hd (by decide)
    have higV := color_ne hi hg (by decide)
    have hihV := color_ne hi hh (by decide)
    have hxc := color_ne hx hc (by decide)
    have hxd := color_ne hx hd (by decide)
    have hxg := color_ne hx hg (by decide)
    have hxh := color_ne hx hh (by decide)
    have hyd := color_ne hy hd (by decide)
    have hyg := color_ne hy hg (by decide)
    have hyh := color_ne hy hh (by decide)
    have hjc := color_ne hj hc (by decide)
    have hjd := color_ne hj hd (by decide)
    have hjg := color_ne hj hg (by decide)
    have hjh := color_ne hj hh (by decide)
    simp [habV, hacV, hadV, hafV, hagV, hahV,
      hbcV, hbdV, hbfV, hbgV, hbhV,
      hcdV, hcgV, hchV, hdgV, hdhV,
      hfgV, hfhV, hghV,
      hai, haxV, hay, haj, hbi, hbx, hbyV, hbj,
      hfiV, hfxV, hfyV, hfj, hfc, hfdV,
      hixV, hiyV, hijV, hicV, hidV, higV, hihV,
      hxc, hxd, hxg, hxh, hyd, hyg, hyh, hjc, hjd, hjg, hjh,
      hxy, hxj, hyj, hyc]
  exact HasReachableReduction.of_current_ptr C
    (containsPositiveX C ha hb hf hi hx hy hj hc hd hg hh
      hab hax hja.symm hby hbc hjf.symm hfg hic hdi.symm hih hcd hgh
      hfi hfx hfy hfd hfh hix hiy hij hig hn)

end Subcubic
