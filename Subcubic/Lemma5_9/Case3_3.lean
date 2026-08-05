import Subcubic.Lemma5_9.Case3_2

/-! Lemma 5.9, Case (3.3): Figure 5(aa). -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_9_case_aa
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (he : C.color e = .red)
    (hf : C.color f = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma5_9Case3Configuration C a b c d e f g h)
    (hxy : Q.x ≠ Q.y) (hij : ¬ G.Adj Q.i Q.j)
    (hic : G.Adj Q.i c) (hjf : G.Adj Q.j f) :
    HasReachableNegativeReduction C := by
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
  have hef := edge 4 5 (by native_decide)
  have hfg := edge 5 6 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hfx : ¬ G.Adj f x := by
    apply not_adj_fourth_neighbor_of_subcubic C.subcubic hef.symm hfg hjf.symm
    · exact hv (u := (4 : Fin 8)) (v := 6) (by decide)
    · exact vertex_ne_of_color_eq he hj (by decide)
    · exact vertex_ne_of_color_eq hg hj (by decide)
    · exact vertex_ne_of_color_eq hx he (by decide)
    · exact vertex_ne_of_color_eq hx hg (by decide)
    · exact hxj
  have hix : ¬ G.Adj i x := by
    apply not_adj_fourth_neighbor_of_subcubic C.subcubic hdi.symm hih hic
    · exact hv (u := (3 : Fin 8)) (v := 7) (by decide)
    · exact hv (u := (3 : Fin 8)) (v := 2) (by decide)
    · exact hv (u := (7 : Fin 8)) (v := 2) (by decide)
    · exact vertex_ne_of_color_eq hx hd (by decide)
    · exact vertex_ne_of_color_eq hx hh (by decide)
    · exact vertex_ne_of_color_eq hx hc (by decide)
  have hn : [a, f, i, x, j, g, h, c, d].Nodup := by
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
        (hu : C.color u = cu) (hv' : C.color v = cv) (hne : cu ≠ cv) :
        u ≠ v := vertex_ne_of_color_eq hu hv' hne
    simp [hafV, hagV, hahV, hacV, hadV,
      hfgV, hfhV, Ne.symm hcfV, Ne.symm hdfV,
      hghV, Ne.symm hcgV, Ne.symm hdgV,
      Ne.symm hchV, Ne.symm hdhV, hcdV,
      color_ne ha hi (by decide), color_ne ha hx (by decide),
      color_ne ha hj (by decide), color_ne hf hi (by decide),
      color_ne hf hx (by decide), color_ne hf hj (by decide),
      color_ne hi hx (by decide), color_ne hi hj (by decide),
      color_ne hi hg (by decide), color_ne hi hh (by decide),
      color_ne hi hc (by decide), color_ne hi hd (by decide),
      color_ne hx hg (by decide), color_ne hx hh (by decide),
      color_ne hx hc (by decide), color_ne hx hd (by decide),
      color_ne hj hg (by decide), color_ne hj hh (by decide),
      color_ne hj hc (by decide), color_ne hj hd (by decide), hxj]
  have hntr := containsNegativeAa C ha hf hi hx hj hg hh hc hd
    hax hja.symm hjf.symm hfg hih hic hdi.symm hgh hcd
    (by simpa using nonedge 0 5 (by native_decide))
    (C.reddish_not_adj_redSide hi (Or.inl ha) ∘ SimpleGraph.Adj.symm)
    (by simpa using nonedge 0 6 (by native_decide))
    (by simpa using nonedge 0 7 (by native_decide))
    (by simpa using nonedge 0 2 (by native_decide))
    (by simpa using nonedge 0 3 (by native_decide))
    (C.reddish_not_adj_redSide hi (Or.inl hf) ∘ SimpleGraph.Adj.symm)
    hfx
    (by simpa using nonedge 5 7 (by native_decide))
    (by simpa using nonedge 5 2 (by native_decide))
    (by simpa using nonedge 5 3 (by native_decide))
    hix hij hig hn
  exact HasReachableNegativeReduction.of_current_ntr C hntr

end Subcubic
