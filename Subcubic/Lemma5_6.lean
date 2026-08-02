import Subcubic.Lemma5_5
import Subcubic.Lemma4_10.Basic

/-!
# Lemma 5.6

For the induced path `a-b-c-d-e-f`, the middle red vertices `b,e` cannot
share a neighbor unless a negative tail reducer or a cut enhancer is already
present.  The paper's distance bound is omitted.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem color_ne {C : GoodColoring G} {x y : V} {cx cy : Color}
    (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
  intro h
  subst y
  simp_all

/-- Figure 5(j), oriented so that the shared bluish neighbor also meets the
right endpoint of the path. -/
private theorem lemma5_6_endpoint_case
    (C : GoodColoring G) {a b c d e f g : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .bluish) (hgdeg : vertexDegree G g = 3)
    (hbg : G.Adj b g) (heg : G.Adj e g) (hgf : G.Adj g f) :
    ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  dsimp [FormsInducedPath6] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) := hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    (hedge x y).mp hxy
  have nonedge (x y : Fin 6) (hxy : ¬ (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      ¬ G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    fun h => hxy ((hedge x y).mpr h)
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
  have hce : ¬ G.Adj c e := by simpa using nonedge 2 4 (by native_decide)
  have hcf : ¬ G.Adj c f := by simpa using nonedge 2 5 (by native_decide)
  have hbeV : b ≠ e := hv (x := (1 : Fin 6)) (y := 4) (by decide)
  have hbfV : b ≠ f := hv (x := (1 : Fin 6)) (y := 5) (by decide)
  have hefV : e ≠ f := hv (x := (4 : Fin 6)) (y := 5) (by decide)
  have hbdV : b ≠ d := hv (x := (1 : Fin 6)) (y := 3) (by decide)
  obtain ⟨h, hch, hhb, hhd⟩ := C.exists_third_neighbor (Or.inr hc) hbdV
  have hhSide := C.other_neighbor_of_blue_is_redSide hc hd hcd hch hhd
  have hha : h ≠ a := by
    intro hha
    subst h
    exact hac hch.symm
  rcases lemma3_3_reversed C hc hb ha hhSide hbc.symm hch hab.symm
      hhb.symm hha.symm with hh | hceFound
  · left
    have hcg : ¬ G.Adj c g :=
      fun h => C.bluish_not_adj_blueSide hg (Or.inl hc) h.symm
    have hgh : ¬ G.Adj g h := by
      apply not_adj_fourth_neighbor_of_degree_three hgdeg hbg.symm heg.symm hgf
      · exact hbeV
      · exact hbfV
      · exact hefV
      · exact hhb
      · exact color_ne hh he (by decide)
      · exact color_ne hh hf (by decide)
    have hga : ¬ G.Adj g a := by
      apply not_adj_fourth_neighbor_of_degree_three hgdeg hbg.symm heg.symm hgf
      · exact hbeV
      · exact hbfV
      · exact hefV
      · exact hv (x := (0 : Fin 6)) (y := 1) (by decide)
      · exact hv (x := (0 : Fin 6)) (y := 4) (by decide)
      · exact hv (x := (0 : Fin 6)) (y := 5) (by decide)
    have habV : a ≠ b := hv (x := (0 : Fin 6)) (y := 1) (by decide)
    have haeV : a ≠ e := hv (x := (0 : Fin 6)) (y := 4) (by decide)
    have hafV : a ≠ f := hv (x := (0 : Fin 6)) (y := 5) (by decide)
    have hn : [c, g, h, a, b, e, f].Nodup := by
      simp [habV, haeV, hafV, hbeV, hbfV, hefV,
        color_ne hc hg (by decide),
        color_ne hc hh (by decide), color_ne hc ha (by decide),
        color_ne hc hb (by decide), color_ne hc he (by decide),
        color_ne hc hf (by decide), color_ne hg hh (by decide),
        color_ne hg ha (by decide), color_ne hg hb (by decide),
        color_ne hg he (by decide), color_ne hg hf (by decide),
        color_ne hh ha (by decide), color_ne hh hb (by decide),
        color_ne hh he (by decide), color_ne hh hf (by decide)]
    have hntrSwap := containsNegativeJ C.swapSides
      (by simp [hc]) (by simp [hg]) (by simp [hh])
      (by simp [ha]) (by simp [hb]) (by simp [he]) (by simp [hf])
      hch hbc.symm hbg.symm heg.symm hgf hab hef
      hcg (fun q => hac q.symm) hce hcf hgh hga hn
    exact (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap
  · exact Or.inr hceFound

/-- **Lemma 5.6.**  In the displayed induced path, either `b,e` have no
common neighbor, or the graph contains a negative tail reducer or a cut
enhancer. -/
theorem lemma5_6
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsInducedPath6 G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red) :
    (¬ ∃ g, G.Adj b g ∧ G.Adj e g) ∨
      ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  by_cases hshared : ∃ g, G.Adj b g ∧ G.Adj e g
  · right
    rcases hshared with ⟨g, hbg, heg⟩
    dsimp [FormsInducedPath6] at hpath
    rcases hpath with ⟨hinj, hedge⟩
    have hp : FormsInducedPath6 G a b c d e f := ⟨hinj, hedge⟩
    have hv {x y : Fin 6} (hxy : x ≠ y) :
        (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) := hinj.ne hxy
    have edge (x y : Fin 6) (hxy : (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
        G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
      (hedge x y).mp hxy
    have nonedge (x y : Fin 6) (hxy : ¬ (graphOfEdges
        [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
        ¬ G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
      fun h => hxy ((hedge x y).mpr h)
    have hab : G.Adj a b := edge 0 1 (by native_decide)
    have hbc : G.Adj b c := edge 1 2 (by native_decide)
    have hcd : G.Adj c d := edge 2 3 (by native_decide)
    have hde : G.Adj d e := edge 3 4 (by native_decide)
    have hef : G.Adj e f := edge 4 5 (by native_decide)
    have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
    have hbe : ¬ G.Adj b e := by simpa using nonedge 1 4 (by native_decide)
    have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
    have hce : ¬ G.Adj c e := by simpa using nonedge 2 4 (by native_decide)
    have hgdV : g ≠ d := by intro h; subst g; exact hbd hbg
    have hgSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbg
      (by intro h; subst g; exact hae heg.symm)
    rcases lemma3_3 C hb hc hd hgSide hbc hbg hcd
        (by intro h; subst g; exact hce heg.symm)
        hgdV.symm with hg | hceFound
    · rcases lemma3_5 C.swapSides (by simp [hc]) (by simp [hb])
          (by simp [hg]) hbc.symm hbg with hgdeg | hceFound
      · by_cases hgf : G.Adj g f
        · exact lemma5_6_endpoint_case C hp ha hb hc hd he hf hg hgdeg
            hbg heg hgf
        · by_cases hga : G.Adj g a
          · exact lemma5_6_endpoint_case C hp.reverse hf he hd hc hb ha hg
              hgdeg heg hbg hga
          · have hceV : c ≠ e := hv (x := (2 : Fin 6)) (y := 4) (by decide)
            have hcg : ¬ G.Adj c g :=
              fun h => C.bluish_not_adj_blueSide hg (Or.inl hc) h.symm
            have hgd : ¬ G.Adj g d :=
              C.bluish_not_adj_blueSide hg (Or.inl hd)
            have hdg : ¬ G.Adj d g := fun q => hgd q.symm
            obtain ⟨i, hci, hib, hid⟩ := C.exists_third_neighbor (Or.inr hc)
              (hv (x := (1 : Fin 6)) (y := 3) (by decide))
            have hiSide := C.other_neighbor_of_blue_is_redSide hc hd hcd hci hid
            have hia : i ≠ a := by intro h; subst i; exact (nonedge 0 2 (by native_decide)) hci.symm
            rcases lemma3_3_reversed C hc hb ha hiSide hbc.symm hci hab.symm
                hib.symm hia.symm with hi | hceFound
            · obtain ⟨j, hdj, hjc, hje⟩ := C.exists_third_neighbor (Or.inr hd) hceV
              have hjSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdj hjc
              have hjf : j ≠ f := by intro h; subst j; exact (nonedge 3 5 (by native_decide)) hdj
              rcases lemma3_3_reversed C hd he hf hjSide hde hdj hef
                  hje.symm hjf.symm with hj | hceFound
              · obtain ⟨h, hgh, hhb, hhe⟩ :=
                  exists_third_neighbor_of_degree_three hgdeg
                    (hv (x := (1 : Fin 6)) (y := 4) (by decide))
                have hhSide : C.color h = .red ∨ C.color h = .reddish := by
                  rw [← C.mem_redSide_iff]
                  by_contra hhmem
                  exact (C.bluish_not_adj_blueSide hg
                    ((C.not_mem_redSide_iff h).1 hhmem) hgh).elim
                rcases hhSide with hh | hh
                · right
                  have hha : h ≠ a := by intro hha; subst h; exact hga hgh
                  have hhf : h ≠ f := by intro hhf; subst h; exact hgf hgh
                  have hbh : ¬ G.Adj b h :=
                    C.redSide_not_adj_second_neighbor
                      (by simp [hb]) (by simp [ha]) (by simp [hh]) hab.symm
                      hha.symm
                  have heh : ¬ G.Adj e h :=
                    C.redSide_not_adj_second_neighbor
                      (by simp [he]) (by simp [hf]) (by simp [hh]) hef
                      hhf.symm
                  have hch : ¬ G.Adj c h := by
                    apply not_adj_fourth_neighbor_of_degree_three
                      (C.red_or_blue_degree c (Or.inr hc)) hbc.symm hcd hci
                    · exact (hv (x := (1 : Fin 6)) (y := 3) (by decide))
                    · exact hib.symm
                    · exact hid.symm
                    · exact hhb
                    · exact color_ne hh hd (by decide)
                    · exact color_ne hh hi (by decide)
                  exact containsCutEnhancerC_of C hb he hc hg hh
                    hbc hbg heg hgh hbe hbh (fun h => hce h.symm) heh hcg hch
                    (hv (x := (1 : Fin 6)) (y := 4) (by decide))
                    hhb.symm hhe.symm
                · have pentagon : FormsInducedPentagon G c d g b e := by
                    have hbeV : b ≠ e :=
                      hv (x := (1 : Fin 6)) (y := 4) (by decide)
                    have hn : [c, d, g, b, e].Nodup := by
                      simp [hcd.ne, hbeV, color_ne hc hg (by decide),
                        color_ne hc hb (by decide), color_ne hc he (by decide),
                        color_ne hd hg (by decide), color_ne hd hb (by decide),
                        color_ne hd he (by decide), color_ne hg hb (by decide),
                        color_ne hg he (by decide)]
                    refine ⟨?_, ?_⟩
                    · intro x y hxy
                      apply hn.injective_get
                      fin_cases x <;> fin_cases y <;> exact hxy
                    · intro x y
                      fin_cases x <;> fin_cases y <;>
                        simp [graphOfEdges, G.adj_comm, hcd, hbc, hde,
                          hbg, heg, hcg, hdg, hce, hbd, hbe]
                  have noRedAtC : ∀ v, G.Adj c v → v ≠ b → v ≠ e →
                      C.color v ≠ .red := by
                    intro v hcv hvb _ hvred
                    exact (not_adj_fourth_neighbor_of_degree_three
                      (C.red_or_blue_degree c (Or.inr hc)) hbc.symm hcd hci
                      (hv (x := (1 : Fin 6)) (y := 3) (by decide))
                      hib.symm hid.symm hvb
                      (color_ne hvred hd (by decide))
                      (color_ne hvred hi (by decide))) hcv
                  have noRedAtD : ∀ v, G.Adj d v → v ≠ b → v ≠ e →
                      C.color v ≠ .red := by
                    intro v hdv _ hve hvred
                    exact (not_adj_fourth_neighbor_of_degree_three
                      (C.red_or_blue_degree d (Or.inr hd)) hcd.symm hde hdj
                      hceV hjc.symm hje.symm
                      (color_ne hvred hc (by decide)) hve
                      (color_ne hvred hj (by decide))) hdv
                  have noRedAtG : ∀ v, G.Adj g v → v ≠ b → v ≠ e →
                      C.color v ≠ .red := by
                    intro v hgv hvb hve hvred
                    exact (not_adj_fourth_neighbor_of_degree_three hgdeg
                      hbg.symm heg.symm hgh
                      (hv (x := (1 : Fin 6)) (y := 4) (by decide))
                      hhb.symm hhe.symm hvb hve
                      (color_ne hvred hh (by decide))) hgv
                  have hresult := lemma5_5 C.swapSides pentagon
                    (by simp [hc]) (by simp [hd]) (by simp [hg])
                    (by simp [hb]) (Or.inl (by simp [he]))
                    (by simpa using noRedAtC) (by simpa using noRedAtD)
                    (by simpa using noRedAtG)
                  rcases hresult with hntr | hceResult
                  · left
                    exact (containsInducedUpToSwap_swapSides
                      IsNegativeTailReducer C).1 hntr
                  · right
                    exact (containsInducedUpToSwap_swapSides
                      IsCutEnhancer C).1 hceResult
              · exact Or.inr hceFound
            · exact Or.inr hceFound
      · exact Or.inr ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceFound)
    · exact Or.inr hceFound
  · exact Or.inl hshared

end Subcubic
