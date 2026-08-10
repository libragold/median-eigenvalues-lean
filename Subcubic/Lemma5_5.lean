import Subcubic.NegativeTailReducerWitnesses
import Subcubic.Lemma3_5
import Subcubic.NegativeReduction

/-!
# Lemma 5.5

The displayed pentagon has edges `ab`, `ad`, `be`, `cd`, and `ce`.
The proof below follows the overlap split in the paper.
-/

namespace Subcubic

set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The five displayed vertices induce exactly the pentagon
`a-b-e-c-d-a`. -/
def FormsInducedPentagon (G : SimpleGraph V) (a b c d e : V) : Prop :=
  let p : Fin 5 → V := ![a, b, c, d, e]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges [(0, 1), (0, 3), (1, 4), (2, 3), (2, 4)]).Adj x y ↔
      G.Adj (p x) (p y)

private theorem bluish_third_of_no_blue_outside
    (C : GoodColoring G) {v mate d e x : V}
    (hv : C.color v = .red) (hmate : C.color mate = .red)
    (hvmate : G.Adj v mate) (hvx : G.Adj v x) (hxmate : x ≠ mate)
    (hxd : x ≠ d) (hxe : x ≠ e)
    (hnoBlue : ∀ w, G.Adj v w → w ≠ d → w ≠ e → C.color w ≠ .blue) :
    C.color x = .bluish := by
  rcases C.other_neighbor_of_red_is_blueSide hv hmate hvmate hvx hxmate with
    hx | hx
  · exact (hnoBlue x hvx hxd hxe hx).elim
  · exact hx

private theorem blue_mate
    (C : GoodColoring G) {v : V} (hv : C.color v = .blue) :
    ∃ m, C.color m = .blue ∧ G.Adj v m := by
  have hcorrect := C.color_correct v
  rw [hv] at hcorrect
  obtain ⟨_, m, hmSide, hvm⟩ := hcorrect
  have hmCases := (C.not_mem_redSide_iff m).1 hmSide
  rcases hmCases with hm | hm
  · exact ⟨m, hm, hvm⟩
  · exact (C.bluish_not_adj_blueSide hm (Or.inl hv) hvm.symm).elim

/-- **Lemma 5.5.**  The induced pentagon contains a negative tail reducer or
a cut enhancer.  The paper's distance bound is omitted. -/
private theorem lemma5_5_current
    (C : GoodColoring G) {a b c d e : V}
    (hpentagon : FormsInducedPentagon G a b c d e)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish) (hd : C.color d = .blue)
    (he : C.color e = .blue ∨ C.color e = .bluish)
    (haNoBlue : ∀ v, G.Adj a v → v ≠ d → v ≠ e → C.color v ≠ .blue)
    (hbNoBlue : ∀ v, G.Adj b v → v ≠ d → v ≠ e → C.color v ≠ .blue)
    (hcNoBlue : ∀ v, G.Adj c v → v ≠ d → v ≠ e → C.color v ≠ .blue)
    (hNoReach : ¬ HasReachableNegativeReduction C) :
    ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C := by
  classical
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hNoReach (.of_current_ntr C hntr)).elim
    · exact (hNoReach (.of_current_ce C hce)).elim
  dsimp [FormsInducedPentagon] at hpentagon
  rcases hpentagon with ⟨hinj, hedge⟩
  have hv {u v : Fin 5} (huv : u ≠ v) :
      (![a, b, c, d, e] u) ≠ (![a, b, c, d, e] v) := hinj.ne huv
  have edge (u v : Fin 5)
      (huv : (graphOfEdges [(0, 1), (0, 3), (1, 4), (2, 3), (2, 4)]).Adj u v) :
      G.Adj (![a, b, c, d, e] u) (![a, b, c, d, e] v) :=
    (hedge u v).mp huv
  have nonedge (u v : Fin 5)
      (huv : ¬ (graphOfEdges [(0, 1), (0, 3), (1, 4), (2, 3), (2, 4)]).Adj u v) :
      ¬ G.Adj (![a, b, c, d, e] u) (![a, b, c, d, e] v) :=
    fun h => huv ((hedge u v).mpr h)
  have hab := edge 0 1 (by native_decide)
  have had := edge 0 3 (by native_decide)
  have hbe := edge 1 4 (by native_decide)
  have hcd := edge 2 3 (by native_decide)
  have hce := edge 2 4 (by native_decide)
  have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
  have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
  have hbc : ¬ G.Adj b c := by simpa using nonedge 1 2 (by native_decide)
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have hde : ¬ G.Adj d e := by simpa using nonedge 3 4 (by native_decide)
  have hbdV : b ≠ d := hv (u := (1 : Fin 5)) (v := 3) (by decide)
  have haeV : a ≠ e := hv (u := (0 : Fin 5)) (v := 4) (by decide)
  have hdeV : d ≠ e := hv (u := (3 : Fin 5)) (v := 4) (by decide)

  rcases lemma3_5 C ha hd hc had hcd.symm with hcdeg | hfound
  · obtain ⟨x, hax, hxb, hxd⟩ :=
      C.exists_third_neighbor (degree_of_color (Or.inl ha)) hbdV
    have hxe : x ≠ e := by intro h; subst x; exact hae hax
    have hx := bluish_third_of_no_blue_outside C ha hb hab hax hxb hxd hxe haNoBlue
    obtain ⟨y, hby, hya, hye⟩ :=
      C.exists_third_neighbor (degree_of_color (Or.inl hb)) haeV
    have hyd : y ≠ d := by intro h; subst y; exact hbd hby
    have hy := bluish_third_of_no_blue_outside C hb ha hab.symm hby hya hyd hye hbNoBlue
    obtain ⟨f, hcf, hfd, hfe⟩ :=
      exists_third_neighbor_of_degree_three hcdeg hdeV
    have hf : C.color f = .bluish := by
      cases hfc : C.color f with
      | red => exact (C.reddish_not_adj_redSide hc (Or.inl hfc) hcf).elim
      | reddish => exact (C.reddish_not_adj_redSide hc (Or.inr hfc) hcf).elim
      | blue => exact (hcNoBlue f hcf hfd hfe hfc).elim
      | bluish => rfl
    rcases blue_mate C hd with ⟨dm, hdm, hddm⟩
    have hdmd : dm ≠ d := hddm.ne.symm
    have hdme : dm ≠ e := by intro h; subst dm; exact hde hddm
    have hcdm : ¬ G.Adj c dm := by
      apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
      · exact hdeV
      · exact hfd.symm
      · exact hfe.symm
      · exact hdmd
      · exact hdme
      · exact vertex_ne_of_color_eq hdm hf (by decide)
    have hadm : ¬ G.Adj a dm := by
      apply C.not_adj_fourth_neighbor (Or.inl ha) hab had hax
      · exact (hv (u := (1 : Fin 5)) (v := 3) (by decide))
      · exact hxb.symm
      · exact hxd.symm
      · exact vertex_ne_of_color_eq hdm hb (by decide)
      · exact hdmd
      · exact vertex_ne_of_color_eq hdm hx (by decide)

    rcases he with he | he
    · -- Case (2): `e` is blue.
      rcases blue_mate C he with ⟨em, hem, heem⟩
      by_cases hfa : G.Adj f a
      · right
        have hdf : ¬ G.Adj d f :=
          fun h => C.bluish_not_adj_blueSide hf (Or.inl hd) h.symm
        have hfe' : ¬ G.Adj f e := C.bluish_not_adj_blueSide hf (Or.inl he)
        have hswap := containsCutEnhancerD_of (C := C.swapSides)
          (a := d) (b := f) (c := a) (d := c) (e := e)
          (by simp [hd]) (by simp [hf]) (by simp [ha]) (by simp [hc])
          (by simp [he]) had.symm hcd.symm hfa hcf.symm hce
          hdf hde hfe' hac hae hdeV
        exact (containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hswap
      · by_cases hfb : G.Adj f b
        · right
          have hef : ¬ G.Adj e f :=
            fun h => C.bluish_not_adj_blueSide hf (Or.inl he) h.symm
          have hfd' : ¬ G.Adj f d := C.bluish_not_adj_blueSide hf (Or.inl hd)
          have hswap := containsCutEnhancerD_of (C := C.swapSides)
            (a := e) (b := f) (c := b) (d := c) (e := d)
            (by simp [he]) (by simp [hf]) (by simp [hb]) (by simp [hc])
            (by simp [hd]) hbe.symm hce.symm hfb hcf.symm hcd
            hef (fun h => hde h.symm) hfd' hbc hbd hdeV.symm
          exact (containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hswap
        · by_cases hxy : x = y
          · subst y
            have hemE : em ≠ e := heem.ne.symm
            have hemD : em ≠ d := by intro h; subst em; exact hde heem.symm
            have hcem : ¬ G.Adj c em := by
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hemD
              · exact hemE
              · exact vertex_ne_of_color_eq hem hf (by decide)
            have hcx : ¬ G.Adj c x := by
              have hxf : x ≠ f := by intro h; subst f; exact hfa hax.symm
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hxd
              · exact hxe
              · exact hxf
            have hxf : x ≠ f := by intro h; subst f; exact hfa hax.symm
            have hdmem : dm ≠ em := by
              intro h
              subst em
              exact (C.blueSide_not_adj_second_neighbor
                (by simp [hdm]) (by simp [hd]) (by simp [he])
                hddm.symm hdeV) heem.symm
            left
            apply containsNegativeY C ha hb hc hx hdm hd he hem hf
              hab hax had hby hbe hcd hce hcf hddm.symm heem hcx hcdm hcem
            simp [hab.ne, hax.ne, had.ne, hbe.ne, hcd.ne, hce.ne, hcf.ne,
              hddm.ne, heem.ne, hcx, hcdm, hcem, hfa, hfb,
              vertex_ne_of_color_eq ha hc (by decide),
              vertex_ne_of_color_eq ha hx (by decide),
              vertex_ne_of_color_eq ha hdm (by decide),
              vertex_ne_of_color_eq ha hd (by decide),
              vertex_ne_of_color_eq ha he (by decide),
              vertex_ne_of_color_eq ha hem (by decide),
              vertex_ne_of_color_eq ha hf (by decide),
              vertex_ne_of_color_eq hb hc (by decide),
              vertex_ne_of_color_eq hb hx (by decide),
              vertex_ne_of_color_eq hb hdm (by decide),
              vertex_ne_of_color_eq hb hd (by decide),
              vertex_ne_of_color_eq hb he (by decide),
              vertex_ne_of_color_eq hb hem (by decide),
              vertex_ne_of_color_eq hb hf (by decide),
              vertex_ne_of_color_eq hc hx (by decide),
              vertex_ne_of_color_eq hc hdm (by decide),
              vertex_ne_of_color_eq hc hd (by decide),
              vertex_ne_of_color_eq hc he (by decide),
              vertex_ne_of_color_eq hc hem (by decide),
              vertex_ne_of_color_eq hc hf (by decide),
              vertex_ne_of_color_eq hx hdm (by decide),
              vertex_ne_of_color_eq hx hd (by decide),
              vertex_ne_of_color_eq hx he (by decide),
              vertex_ne_of_color_eq hx hem (by decide),
              vertex_ne_of_color_eq hdm hf (by decide),
              vertex_ne_of_color_eq hd hf (by decide),
              vertex_ne_of_color_eq he hf (by decide),
              vertex_ne_of_color_eq hem hf (by decide), hdeV, hdme, hemD,
              hab.ne, hxf, hdmd, hdmem, hemD.symm]
            exact hab.ne
          · have hemE : em ≠ e := heem.ne.symm
            have hemD : em ≠ d := by intro h; subst em; exact hde heem.symm
            have hxf : x ≠ f := by intro h; subst f; exact hfa hax.symm
            have hyf : y ≠ f := by intro h; subst f; exact hfb hby.symm
            have hdmem : dm ≠ em := by
              intro h
              subst em
              exact (C.blueSide_not_adj_second_neighbor
                (by simp [hdm]) (by simp [hd]) (by simp [he])
                hddm.symm hdeV) heem.symm
            have hcx : ¬ G.Adj c x := by
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hxd
              · exact hxe
              · exact hxf
            have hcy : ¬ G.Adj c y := by
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hyd
              · exact hye
              · exact hyf
            have hcem : ¬ G.Adj c em := by
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hemD
              · exact hemE
              · exact vertex_ne_of_color_eq hem hf (by decide)
            left
            apply containsNegativeAf C ha hb hc hy hx hdm hd he hem hf
              hab hax had hby hbe hcd hce hcf hddm.symm heem
              hcy hcx hcdm hcem
            simp [hab.ne, hax.ne, had.ne, hby.ne, hbe.ne, hcd.ne, hce.ne,
              hcf.ne, hddm.ne, heem.ne, hxy, hcx, hcy, hcdm, hcem,
              vertex_ne_of_color_eq ha hc (by decide),
              vertex_ne_of_color_eq ha hy (by decide),
              vertex_ne_of_color_eq ha hx (by decide),
              vertex_ne_of_color_eq ha hdm (by decide),
              vertex_ne_of_color_eq ha hd (by decide),
              vertex_ne_of_color_eq ha he (by decide),
              vertex_ne_of_color_eq ha hem (by decide),
              vertex_ne_of_color_eq ha hf (by decide),
              vertex_ne_of_color_eq hb hc (by decide),
              vertex_ne_of_color_eq hb hy (by decide),
              vertex_ne_of_color_eq hb hx (by decide),
              vertex_ne_of_color_eq hb hdm (by decide),
              vertex_ne_of_color_eq hb hd (by decide),
              vertex_ne_of_color_eq hb he (by decide),
              vertex_ne_of_color_eq hb hem (by decide),
              vertex_ne_of_color_eq hb hf (by decide),
              vertex_ne_of_color_eq hc hy (by decide),
              vertex_ne_of_color_eq hc hx (by decide),
              vertex_ne_of_color_eq hc hdm (by decide),
              vertex_ne_of_color_eq hc hd (by decide),
              vertex_ne_of_color_eq hc he (by decide),
              vertex_ne_of_color_eq hc hem (by decide),
              vertex_ne_of_color_eq hc hf (by decide),
              vertex_ne_of_color_eq hy hdm (by decide),
              vertex_ne_of_color_eq hy hd (by decide),
              vertex_ne_of_color_eq hy he (by decide),
              vertex_ne_of_color_eq hy hem (by decide),
              vertex_ne_of_color_eq hx hdm (by decide),
              vertex_ne_of_color_eq hx hd (by decide),
              vertex_ne_of_color_eq hx he (by decide),
              vertex_ne_of_color_eq hx hem (by decide),
              vertex_ne_of_color_eq hdm hf (by decide),
              vertex_ne_of_color_eq hd hf (by decide),
              vertex_ne_of_color_eq he hf (by decide),
              vertex_ne_of_color_eq hem hf (by decide), hdeV, hdme, hemD,
              hab.ne, hxy, hxy ∘ Eq.symm, hxf, hyf, hdmd, hdmem, hemD.symm]
            exact ⟨hab.ne, fun h => hxy h.symm⟩
    · -- Case (1): `e` is bluish.
      by_cases hxf : x = f
      · subst f
        left
        apply containsNegativeI C ha hc hdm hd hx he had hax hcd hcf hce hddm.symm
          hac hadm hae hcdm
        simp [had.ne, hax.ne, hcd.ne, hce.ne, hddm.ne, hac, hae,
          hadm, hcdm, vertex_ne_of_color_eq ha hc (by decide),
          vertex_ne_of_color_eq ha hdm (by decide),
          vertex_ne_of_color_eq hc hdm (by decide),
          vertex_ne_of_color_eq hc hd (by decide),
          vertex_ne_of_color_eq hc he (by decide),
          vertex_ne_of_color_eq hdm hx (by decide),
          vertex_ne_of_color_eq hdm he (by decide),
          vertex_ne_of_color_eq hd hx (by decide),
          vertex_ne_of_color_eq hd he (by decide), had.ne, haeV, hcf.ne,
          hdmd, hfe]
        exact had.ne
      · have hcx : ¬ G.Adj c x := by
          apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
          · exact hdeV
          · exact hfd.symm
          · exact hfe.symm
          · exact hxd
          · exact hxe
          · exact hxf
        by_cases hyx : y = x
        · subst y
          left
          apply containsNegativeS C hb ha hc he hx hd hdm hf
            hab.symm hbe hby hax had hce hcd hcf hddm hcx hcdm
          have hex : e ≠ x := by intro h; subst x; exact hae hax
          simp [hab.ne, hbe.ne, hax.ne, hcd.ne, hce.ne, hcf.ne, hddm.ne,
            hxf, hcx, hcdm, vertex_ne_of_color_eq ha hc (by decide),
            vertex_ne_of_color_eq ha he (by decide),
            vertex_ne_of_color_eq ha hd (by decide),
            vertex_ne_of_color_eq ha hdm (by decide),
            vertex_ne_of_color_eq hc he (by decide),
            vertex_ne_of_color_eq hc hx (by decide),
            vertex_ne_of_color_eq hc hd (by decide),
            vertex_ne_of_color_eq hc hdm (by decide),
            vertex_ne_of_color_eq he hd (by decide),
            vertex_ne_of_color_eq he hdm (by decide),
            vertex_ne_of_color_eq hx hd (by decide),
            vertex_ne_of_color_eq hx hdm (by decide),
            vertex_ne_of_color_eq hd hf (by decide),
            vertex_ne_of_color_eq hdm hf (by decide), hab.ne.symm, hbc,
            hbe.ne, hby.ne, hbdV, hex, hfe.symm]
          exact ⟨⟨hab.ne.symm, vertex_ne_of_color_eq hb hc (by decide),
            hbe.ne, vertex_ne_of_color_eq hb hdm (by decide),
            vertex_ne_of_color_eq hb hf (by decide)⟩,
            vertex_ne_of_color_eq ha hf (by decide)⟩
        · by_cases hyf : y = f
          · subst y
            left
            apply containsNegativeU C hb ha hc he hx hd hdm hf
              hab.symm hbe hby hax had hce hcd hcf hddm hcx hcdm
            have hex : e ≠ x := by intro h; subst x; exact hae hax
            simp [hab.ne, hbe.ne, hax.ne, hcd.ne, hce.ne, hcf.ne, hddm.ne,
              hxf, hyx, hcx, hcdm,
              vertex_ne_of_color_eq ha hc (by decide),
              vertex_ne_of_color_eq ha he (by decide),
              vertex_ne_of_color_eq ha hd (by decide),
              vertex_ne_of_color_eq ha hdm (by decide),
              vertex_ne_of_color_eq hc he (by decide),
              vertex_ne_of_color_eq hc hx (by decide),
              vertex_ne_of_color_eq hc hd (by decide),
              vertex_ne_of_color_eq hc hdm (by decide),
              vertex_ne_of_color_eq he hd (by decide),
              vertex_ne_of_color_eq he hdm (by decide),
              vertex_ne_of_color_eq hx hd (by decide),
              vertex_ne_of_color_eq hx hdm (by decide),
              vertex_ne_of_color_eq hd hf (by decide),
              vertex_ne_of_color_eq hdm hf (by decide), hab.ne.symm, hbc,
              hbe.ne, hby.ne, hbdV, hex, hfe.symm]
            exact ⟨⟨hab.ne.symm, vertex_ne_of_color_eq hb hc (by decide),
              hbe.ne, hxb.symm, vertex_ne_of_color_eq hb hdm (by decide)⟩,
              vertex_ne_of_color_eq ha hf (by decide)⟩
          · have hcy : ¬ G.Adj c y := by
              apply not_adj_fourth_neighbor_of_degree_three hcdeg hcd hce hcf
              · exact hdeV
              · exact hfd.symm
              · exact hfe.symm
              · exact hyd
              · exact hye
              · exact hyf
            left
            apply containsNegativeAa C hc hb ha hf he hy hd hdm hx
              hcf hce hcd hab.symm hbe hby had hax hddm hcy hcdm hcx
            simp [hab.ne, had.ne, hbe.ne, hcd.ne, hce.ne, hax.ne, hby.ne,
              hcf.ne, hddm.ne, hxf, hyx, hyf, hcx, hcy, hcdm,
              vertex_ne_of_color_eq hc hb (by decide),
              vertex_ne_of_color_eq hc ha (by decide),
              vertex_ne_of_color_eq hc hf (by decide),
              vertex_ne_of_color_eq hc he (by decide),
              vertex_ne_of_color_eq hc hy (by decide),
              vertex_ne_of_color_eq hc hd (by decide),
              vertex_ne_of_color_eq hc hdm (by decide),
              vertex_ne_of_color_eq hc hx (by decide),
              vertex_ne_of_color_eq hb he (by decide),
              vertex_ne_of_color_eq hb hy (by decide),
              vertex_ne_of_color_eq hb hd (by decide),
              vertex_ne_of_color_eq hb hdm (by decide),
              vertex_ne_of_color_eq hb hx (by decide),
              vertex_ne_of_color_eq ha hf (by decide),
              vertex_ne_of_color_eq ha he (by decide),
              vertex_ne_of_color_eq ha hy (by decide),
              vertex_ne_of_color_eq ha hd (by decide),
              vertex_ne_of_color_eq ha hdm (by decide),
              vertex_ne_of_color_eq ha hx (by decide),
              vertex_ne_of_color_eq hf hd (by decide),
              vertex_ne_of_color_eq hf hdm (by decide),
              vertex_ne_of_color_eq he hd (by decide),
              vertex_ne_of_color_eq he hdm (by decide),
              vertex_ne_of_color_eq hy hd (by decide),
              vertex_ne_of_color_eq hy hdm (by decide),
              vertex_ne_of_color_eq hd hx (by decide),
              vertex_ne_of_color_eq hdm hx (by decide), hab.ne.symm,
              hfe, hye.symm, hxe.symm]
            exact ⟨⟨hab.ne.symm, vertex_ne_of_color_eq hb hf (by decide)⟩,
              (fun h => hyf h.symm), fun h => hxf h.symm⟩
  · exact (hNoReach (.of_lemma3_4 C hfound)).elim

/-- **Lemma 5.5.** The pentagon configuration reaches a negative tail
reducer or a cut enhancer. -/
theorem lemma5_5
    (C : GoodColoring G) {a b c d e : V}
    (hpentagon : FormsInducedPentagon G a b c d e)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .reddish) (hd : C.color d = .blue)
    (he : C.color e = .blue ∨ C.color e = .bluish)
    (haNoBlue : ∀ v, G.Adj a v → v ≠ d → v ≠ e → C.color v ≠ .blue)
    (hbNoBlue : ∀ v, G.Adj b v → v ≠ d → v ≠ e → C.color v ≠ .blue)
    (hcNoBlue : ∀ v, G.Adj c v → v ≠ d → v ≠ e → C.color v ≠ .blue) :
    HasReachableNegativeReduction C := by
  by_cases hdone : HasReachableNegativeReduction C
  · exact hdone
  rcases lemma5_5_current C hpentagon ha hb hc hd he
      haNoBlue hbNoBlue hcNoBlue hdone with hntr | hce
  · exact .of_current_ntr C hntr
  · exact .of_current_ce C hce

end Subcubic
