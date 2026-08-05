import Subcubic.Lemma5_11
import Subcubic.Lemma5_9
import Subcubic.Lemma5_8
import Subcubic.Lemma5_7
import Subcubic.Lemma5_3
import Subcubic.Lemma5_2
import Subcubic.Lemma4_6
import Subcubic.Lemma4_7

/-!
# The distance-free Lemma 5.12 step used inside Lemma 4.12

The paper phrases this step as extending three alternating monochromatic
edges.  This file first records the completely local part: unless Lemma 5.2
already applies, the six displayed vertices induce the expected path.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Six distinct vertices containing the displayed path; extra edges are
allowed. -/
def FormsPath6Subgraph (G : SimpleGraph V)
    (a b c d e f : V) : Prop :=
  let p : Fin 6 → V := ![a, b, c, d, e, f]
  Function.Injective p ∧
    ∀ x y, (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y →
        G.Adj (p x) (p y)

/-- The chord analysis at the start of the inlined Lemma 5.12 argument.
Every possible extra crossing between consecutive monochromatic edges gives
Lemma 5.2; matching on each side excludes all remaining chords. -/
theorem path6_induced_or_negative_reduction
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsPath6Subgraph G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red) :
    HasReachableNegativeReduction C ∨ FormsInducedPath6 G a b c d e f := by
  classical
  dsimp [FormsPath6Subgraph] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {x y : Fin 6} (hxy : x ≠ y) :
      (![a, b, c, d, e, f] x) ≠ (![a, b, c, d, e, f] y) :=
    hinj.ne hxy
  have edge (x y : Fin 6) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f] x) (![a, b, c, d, e, f] y) :=
    hedge x y hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have current (hout : ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C) :
      HasReachableNegativeReduction C :=
    hout.elim (HasReachableNegativeReduction.of_current_ntr C)
      (HasReachableNegativeReduction.of_current_ce C)
  by_cases hac : G.Adj a c
  · exact Or.inl (current (lemma5_2 C a b c d hab ha hb hcd hc hd (by
      simp [fourVertexCrossEdgeCount, hac, hbc]
      omega)))
  by_cases had : G.Adj a d
  · exact Or.inl (current (lemma5_2 C a b c d hab ha hb hcd hc hd (by
      simp [fourVertexCrossEdgeCount, had, hbc]
      omega)))
  by_cases hbd : G.Adj b d
  · exact Or.inl (current (lemma5_2 C a b c d hab ha hb hcd hc hd (by
      simp [fourVertexCrossEdgeCount, hbc, hbd])))
  by_cases hce : G.Adj c e
  · exact Or.inl (current (lemma5_2 C e f c d hef he hf hcd hc hd (by
      simp [fourVertexCrossEdgeCount, SimpleGraph.adj_comm, hce, hde]
      omega)))
  by_cases hcf : G.Adj c f
  · exact Or.inl (current (lemma5_2 C e f c d hef he hf hcd hc hd (by
      simp [fourVertexCrossEdgeCount, SimpleGraph.adj_comm, hcf, hde]
      omega)))
  by_cases hdf : G.Adj d f
  · exact Or.inl (current (lemma5_2 C e f c d hef he hf hcd hc hd (by
      simp [fourVertexCrossEdgeCount, SimpleGraph.adj_comm, hde, hdf]
      omega)))
  have redNonedge {x mate y : V}
      (hx : C.color x = .red) (hm : C.color mate = .red)
      (hy : C.color y = .red) (hxm : G.Adj x mate) (hmy : mate ≠ y) :
      ¬ G.Adj x y := by
    exact C.redSide_not_adj_second_neighbor
      (by simp [hx]) (by simp [hm]) (by simp [hy]) hxm hmy
  have hae : ¬ G.Adj a e := redNonedge ha hb he hab
    (hv (x := (1 : Fin 6)) (y := 4) (by decide))
  have haf : ¬ G.Adj a f := redNonedge ha hb hf hab
    (hv (x := (1 : Fin 6)) (y := 5) (by decide))
  have hbe : ¬ G.Adj b e := redNonedge hb ha he hab.symm
    (hv (x := (0 : Fin 6)) (y := 4) (by decide))
  have hbf : ¬ G.Adj b f := redNonedge hb ha hf hab.symm
    (hv (x := (0 : Fin 6)) (y := 5) (by decide))
  apply Or.inr
  refine ⟨hinj, ?_⟩
  intro x y
  fin_cases x <;> fin_cases y <;>
    simp [graphOfEdges, SimpleGraph.adj_comm, hab, hbc, hcd, hde, hef,
      hac, had, hbd, hce, hcf, hdf, hae, haf, hbe, hbf]

/-- If the path-extension process stops at both ends, Lemma 4.10 is the
required inlined conclusion. -/
theorem path6_subgraph_with_clean_ends_negative
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsPath6Subgraph G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoBlueAtF : ∀ v, G.Adj f v → C.color v ≠ .blue) :
    HasReachableNegativeReduction C := by
  rcases path6_induced_or_negative_reduction C hpath ha hb hc hd he hf with
    hresult | hinduced
  · exact hresult
  · exact lemma5_11 C hinduced ha hb hc hd he hf hNoBlueAtA hNoBlueAtF

set_option maxHeartbeats 1000000
/-- The distance-free content of the paper's Lemma 5.12, expanded in terms
of Lemmas 5.2, 5.7, 5.8, 5.9, and 5.11. -/
theorem lemma5_12_inline
    (C : GoodColoring G) {a b c d e f : V}
    (hpath : FormsPath6Subgraph G a b c d e f)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red) :
    HasReachableNegativeReduction C := by
  classical
  by_contra hresult
  have noResult (hout : HasReachableNegativeReduction C) : False := hresult hout
  have noOutcome (hout : ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C) :
      False :=
    noResult (hout.elim (HasReachableNegativeReduction.of_current_ntr C)
      (HasReachableNegativeReduction.of_current_ce C))
  have noCE (hce : ContainsCutEnhancer C) : False :=
    noOutcome (Or.inr hce)
  rcases path6_induced_or_negative_reduction C hpath ha hb hc hd he hf with
    hout | hinduced
  · exact noResult hout
  · have extendRight {a b c d e f : V}
        (hp : FormsInducedPath6 G a b c d e f)
        (ha : C.color a = .red) (hb : C.color b = .red)
        (hc : C.color c = .blue) (hd : C.color d = .blue)
        (he : C.color e = .red) (hf : C.color f = .red)
        (hBlueF : ∃ x, G.Adj f x ∧ C.color x = .blue) : False := by
      obtain ⟨x, hfx, hx⟩ := hBlueF
      have hxCorrect := C.color_correct x
      rw [hx] at hxCorrect
      obtain ⟨_, y, hySide, hxy⟩ := hxCorrect
      have hySide' := (C.not_mem_redSide_iff y).1 hySide
      have hy : C.color y = .blue := by
        rcases hySide' with hy | hy
        · exact hy
        · exact (C.bluish_not_adj_blueSide hy (Or.inl hx) hxy.symm).elim
      dsimp [FormsInducedPath6] at hp
      rcases hp with ⟨hinj, hedge⟩
      have hp0 : FormsInducedPath6 G a b c d e f := ⟨hinj, hedge⟩
      have hv {i j : Fin 6} (hij : i ≠ j) :
          (![a, b, c, d, e, f] i) ≠ (![a, b, c, d, e, f] j) :=
        hinj.ne hij
      have edge (i j : Fin 6) (hij : (graphOfEdges
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj i j) :
          G.Adj (![a, b, c, d, e, f] i) (![a, b, c, d, e, f] j) :=
        (hedge i j).mp hij
      have nonedge (i j : Fin 6) (hij : ¬ (graphOfEdges
          [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5)]).Adj i j) :
          ¬ G.Adj (![a, b, c, d, e, f] i) (![a, b, c, d, e, f] j) :=
        fun h => hij ((hedge i j).mpr h)
      have hab : G.Adj a b := edge 0 1 (by native_decide)
      have hbc : G.Adj b c := edge 1 2 (by native_decide)
      have hcd : G.Adj c d := edge 2 3 (by native_decide)
      have hde : G.Adj d e := edge 3 4 (by native_decide)
      have hef : G.Adj e f := edge 4 5 (by native_decide)
      have hae : ¬ G.Adj a e := by simpa using nonedge 0 4 (by native_decide)
      have haf : ¬ G.Adj a f := by simpa using nonedge 0 5 (by native_decide)
      have hbe : ¬ G.Adj b e := by simpa using nonedge 1 4 (by native_decide)
      have hbf : ¬ G.Adj b f := by simpa using nonedge 1 5 (by native_decide)
      have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
      have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
      have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
      have hce : ¬ G.Adj c e := by simpa using nonedge 2 4 (by native_decide)
      have hcf : ¬ G.Adj c f := by simpa using nonedge 2 5 (by native_decide)
      have hdf : ¬ G.Adj d f := by simpa using nonedge 3 5 (by native_decide)
      have color_ne {u v : V} {cu cv : Color}
          (hu : C.color u = cu) (hv : C.color v = cv) (h : cu ≠ cv) :
          u ≠ v := by intro huv; subst v; simp_all
      have hxc : x ≠ c := by
        intro h
        subst x
        apply noOutcome
        apply lemma5_2 C e f c d hef he hf hcd hc hd
        have hed : G.Adj e d := hde.symm
        have hfc : G.Adj f c := hfx
        simp [fourVertexCrossEdgeCount, hed, hfc]
        omega
      have hxd : x ≠ d := by
        intro h
        subst x
        apply noOutcome
        apply lemma5_2 C e f c d hef he hf hcd hc hd
        have hed : G.Adj e d := hde.symm
        have hfd : G.Adj f d := hfx
        simp [fourVertexCrossEdgeCount, hed, hfd]
        omega
      have hyc : y ≠ c := by
        intro h
        have hnot := C.blueSide_not_adj_second_neighbor
          (by simp [hc]) (by simp [hd]) (by simp [hx]) hcd hxd.symm
        exact hnot (by simpa [h] using hxy.symm)
      have hyd : y ≠ d := by
        intro h
        have hnot := C.blueSide_not_adj_second_neighbor
          (by simp [hd]) (by simp [hc]) (by simp [hx]) hcd.symm hxc.symm
        exact hnot (by simpa [h] using hxy.symm)
      have blueNonedge {u mate v : V}
          (hu : C.color u = .blue) (hm : C.color mate = .blue)
          (hv : C.color v = .blue) (hum : G.Adj u mate) (hmv : mate ≠ v) :
          ¬ G.Adj u v := by
        exact C.blueSide_not_adj_second_neighbor
          (by simp [hu]) (by simp [hm]) (by simp [hv]) hum hmv
      have hxcN : ¬ G.Adj x c := blueNonedge hx hy hc hxy hyc
      have hxdN : ¬ G.Adj x d := blueNonedge hx hy hd hxy hyd
      have hycN : ¬ G.Adj y c := blueNonedge hy hx hc hxy.symm hxc
      have hydN : ¬ G.Adj y d := blueNonedge hy hx hd hxy.symm hxd
      have hex : ¬ G.Adj e x := by
        intro hex
        apply noOutcome
        apply lemma5_2 C e f x y hef he hf hxy hx hy
        simp [fourVertexCrossEdgeCount, hex, hfx]
        omega
      have hey : ¬ G.Adj e y := by
        intro hey
        apply noOutcome
        apply lemma5_2 C e f x y hef he hf hxy hx hy
        simp [fourVertexCrossEdgeCount, hey, hfx]
        omega
      have hfy : ¬ G.Adj f y := by
        intro hfy
        apply noOutcome
        apply lemma5_2 C e f x y hef he hf hxy hx hy
        simp [fourVertexCrossEdgeCount, hfy, hfx]
      have hxa : ¬ G.Adj x a := by
        intro hxa
        have hceSwap := containsCutEnhancerA_of C.swapSides
          (by simp [hx]) (by simp [hf]) (by simp [ha])
          hfx.symm hxa (hv (i := (5 : Fin 6)) (j := 0) (by decide))
          (by simpa [SimpleGraph.adj_comm] using haf)
        exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
      have hxb : ¬ G.Adj x b := by
        intro hxb
        have hceSwap := containsCutEnhancerA_of C.swapSides
          (by simp [hx]) (by simp [hf]) (by simp [hb])
          hfx.symm hxb (hv (i := (5 : Fin 6)) (j := 1) (by decide))
          (by simpa [SimpleGraph.adj_comm] using hbf)
        exact noCE ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
      have hyb : ¬ G.Adj y b := by
        intro hyb
        exact noCE (containsCutEnhancerA_of C hb hc hy hbc hyb.symm
          hyc.symm (by simpa [SimpleGraph.adj_comm] using hycN))
      have hcoreNodup : [a, b, c, d, e, f].Nodup := by
        simpa using List.nodup_ofFn_ofInjective hinj
      have hxOutside : x ∉ [a, b, c, d, e, f] := by
        simp [color_ne hx ha (by decide), color_ne hx hb (by decide),
          hxc, hxd, color_ne hx he (by decide), color_ne hx hf (by decide)]
      have hyOutside : y ∉ [a, b, c, d, e, f] := by
        simp [color_ne hy ha (by decide), color_ne hy hb (by decide),
          hyc, hyd, color_ne hy he (by decide), color_ne hy hf (by decide)]
      have hnodup8 : [a, b, c, d, e, f, x, y].Nodup := by
        rw [show [a, b, c, d, e, f, x, y] = [a, b, c, d, e, f] ++ [x, y] by rfl,
          List.nodup_append']
        refine ⟨hcoreNodup, by simp [hxy.ne], ?_⟩
        rw [List.disjoint_left]
        intro u hu huv
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at huv
        rcases huv with rfl | rfl
        · exact hxOutside hu
        · exact hyOutside hu
      have hax : ¬ G.Adj a x := fun h => hxa h.symm
      have hbx : ¬ G.Adj b x := fun h => hxb h.symm
      have hby : ¬ G.Adj b y := fun h => hyb h.symm
      have hcx : ¬ G.Adj c x := fun h => hxcN h.symm
      have hdx : ¬ G.Adj d x := fun h => hxdN h.symm
      have hcy : ¬ G.Adj c y := fun h => hycN h.symm
      have hdy : ¬ G.Adj d y := fun h => hydN h.symm
      have hxe : ¬ G.Adj x e := fun h => hex h.symm
      have hye : ¬ G.Adj y e := fun h => hey h.symm
      have hyf : ¬ G.Adj y f := fun h => hfy h.symm
      have hba : G.Adj b a := hab.symm
      have hcb : G.Adj c b := hbc.symm
      have hdc : G.Adj d c := hcd.symm
      have hed : G.Adj e d := hde.symm
      have hfe : G.Adj f e := hef.symm
      have hxf : G.Adj x f := hfx.symm
      have hyx : G.Adj y x := hxy.symm
      have hca : ¬ G.Adj c a := fun h => hac h.symm
      have hda : ¬ G.Adj d a := fun h => had h.symm
      have hdb : ¬ G.Adj d b := fun h => hbd h.symm
      have hea : ¬ G.Adj e a := fun h => hae h.symm
      have heb : ¬ G.Adj e b := fun h => hbe h.symm
      have hfa : ¬ G.Adj f a := fun h => haf h.symm
      have hfb : ¬ G.Adj f b := fun h => hbf h.symm
      have hec : ¬ G.Adj e c := fun h => hce h.symm
      have hfc : ¬ G.Adj f c := fun h => hcf h.symm
      have hfd : ¬ G.Adj f d := fun h => hdf h.symm
      have hya : ¬ G.Adj y a := by
        intro hya
        have hayEdge : G.Adj a y := hya.symm
        have hcycle : FormsInducedCycle8 G a b c d e f x y := by
          refine ⟨?_, ?_⟩
          · have hvec : (![a, b, c, d, e, f, x, y] : Fin 8 → V) =
                [a, b, c, d, e, f, x, y].get := by
              funext i; fin_cases i <;> rfl
            rw [hvec]
            exact hnodup8.injective_get
          · intro i j
            fin_cases i <;> fin_cases j <;>
              simp [graphOfEdges] at ⊢
            all_goals assumption
        exact noResult (lemma5_8 C hcycle ha hb hc hd he hf hx hy)
      have hay : ¬ G.Adj a y := fun h => hya h.symm
      have hp8 : FormsInducedPath8 G a b c d e f x y := by
        refine ⟨?_, ?_⟩
        · have hvec : (![a, b, c, d, e, f, x, y] : Fin 8 → V) =
              [a, b, c, d, e, f, x, y].get := by
            funext i; fin_cases i <;> rfl
          rw [hvec]
          exact hnodup8.injective_get
        · intro i j
          fin_cases i <;> fin_cases j <;>
            simp [graphOfEdges] at ⊢
          all_goals assumption
      by_cases hNoRedY : ∀ z, G.Adj y z → C.color z ≠ .red
      · by_cases hNoBlueA : ∀ z, G.Adj a z → C.color z ≠ .blue
        · exact noResult (lemma5_9 C hp8 ha hb hc hd he hf hx hy
            hNoBlueA hNoRedY)
        · push Not at hNoBlueA
          obtain ⟨p, hap, hp⟩ := hNoBlueA
          have hpCorrect := C.color_correct p
          rw [hp] at hpCorrect
          obtain ⟨_, q, hqSide, hpq⟩ := hpCorrect
          have hqSide' := (C.not_mem_redSide_iff q).1 hqSide
          have hq : C.color q = .blue := by
            rcases hqSide' with hq | hq
            · exact hq
            · exact (C.bluish_not_adj_blueSide hq (Or.inl hp) hpq.symm).elim
          have hpc : p ≠ c := by
            intro h
            subst p
            apply noOutcome
            apply lemma5_2 C a b c d hab ha hb hcd hc hd
            simp [fourVertexCrossEdgeCount, hbc, hap]
            omega
          have hpd : p ≠ d := by
            intro h
            subst p
            apply noOutcome
            apply lemma5_2 C a b c d hab ha hb hcd hc hd
            simp [fourVertexCrossEdgeCount, hbc, hap]
            omega
          have hpx : p ≠ x := by
            intro h
            have hceSwap := containsCutEnhancerA_of C.swapSides
              (by simp [hx]) (by simp [hf]) (by simp [ha]) hfx.symm
              (by simpa [h] using hap.symm)
              (hv (i := (5 : Fin 6)) (j := 0) (by decide))
              (by simpa [SimpleGraph.adj_comm] using haf)
            exact noCE
              ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
          have hpy : p ≠ y := fun h => hya (by simpa [h] using hap.symm)
          have hqc : q ≠ c := by
            intro h
            have hnot := C.blueSide_not_adj_second_neighbor
              (by simp [hc]) (by simp [hd]) (by simp [hp]) hcd hpd.symm
            exact hnot (by simpa [h] using hpq.symm)
          have hqd : q ≠ d := by
            intro h
            have hnot := C.blueSide_not_adj_second_neighbor
              (by simp [hd]) (by simp [hc]) (by simp [hp]) hcd.symm hpc.symm
            exact hnot (by simpa [h] using hpq.symm)
          have hqx : q ≠ x := by
            intro h
            have hnot := C.blueSide_not_adj_second_neighbor
              (by simp [hx]) (by simp [hy]) (by simp [hp]) hxy hpy.symm
            exact hnot (by simpa [h] using hpq.symm)
          have hqy : q ≠ y := by
            intro h
            have hnot := C.blueSide_not_adj_second_neighbor
              (by simp [hy]) (by simp [hx]) (by simp [hp]) hxy.symm hpx.symm
            exact hnot (by simpa [h] using hpq.symm)
          have hnodup10 : [q, p, a, b, c, d, e, f, x, y].Nodup := by
            have hpOutside : p ∉ [a, b, c, d, e, f, x, y] := by
              simp [color_ne hp ha (by decide), color_ne hp hb (by decide),
                hpc, hpd, color_ne hp he (by decide), color_ne hp hf (by decide),
                hpx, hpy]
            have hqOutside : q ∉ [a, b, c, d, e, f, x, y] := by
              simp [color_ne hq ha (by decide), color_ne hq hb (by decide),
                hqc, hqd, color_ne hq he (by decide), color_ne hq hf (by decide),
                hqx, hqy]
            rw [show [q, p, a, b, c, d, e, f, x, y] =
              [q, p] ++ [a, b, c, d, e, f, x, y] by rfl,
              List.nodup_append']
            refine ⟨by simp [hpq.ne.symm], hnodup8, ?_⟩
            rw [List.disjoint_left]
            intro u hu huCore
            simp only [List.mem_cons, List.not_mem_nil,
              or_false] at hu
            rcases hu with rfl | rfl
            · exact hqOutside huCore
            · exact hpOutside huCore
          have hsub10 : FormsPath10Subgraph G q p a b c d e f x y := by
            refine ⟨?_, ?_⟩
            · have hvec : (![q, p, a, b, c, d, e, f, x, y] : Fin 10 → V) =
                  [q, p, a, b, c, d, e, f, x, y].get := by
                funext i; fin_cases i <;> rfl
              rw [hvec]
              exact hnodup10.injective_get
            · intro i j hij
              have hqp := hpq.symm
              have hpa := hap.symm
              fin_cases i <;> fin_cases j <;> simp [graphOfEdges] at hij
              all_goals assumption
          exact noResult (HasReachableNegativeReduction.of_swapSides C
            (lemma5_10_inline C.swapSides hsub10
              (by simp [hq]) (by simp [hp]) (by simp [ha]) (by simp [hb])
              (by simp [hc]) (by simp [hd]) (by simp [he]) (by simp [hf])
              (by simp [hx]) (by simp [hy])))
      · push Not at hNoRedY
        obtain ⟨z, hyz, hz⟩ := hNoRedY
        have hzCorrect := C.color_correct z
        rw [hz] at hzCorrect
        obtain ⟨_, w, hwSide, hzw⟩ := hzCorrect
        have hwSide' := (C.mem_redSide_iff w).1 hwSide
        have hw : C.color w = .red := by
          rcases hwSide' with hw | hw
          · exact hw
          · exact (C.reddish_not_adj_redSide hw (Or.inl hz) hzw.symm).elim
        have hza : z ≠ a := fun h => hya (by simpa [h] using hyz)
        have hzb : z ≠ b := fun h => hyb (by simpa [h] using hyz)
        have hze : z ≠ e := fun h => hey (by simpa [h] using hyz.symm)
        have hzf : z ≠ f := fun h => hfy (by simpa [h] using hyz.symm)
        have hwa : w ≠ a := by
          intro h
          have hnot := C.redSide_not_adj_second_neighbor
            (by simp [ha]) (by simp [hb]) (by simp [hz]) hab hzb.symm
          exact hnot (by simpa [h] using hzw.symm)
        have hwb : w ≠ b := by
          intro h
          have hnot := C.redSide_not_adj_second_neighbor
            (by simp [hb]) (by simp [ha]) (by simp [hz]) hab.symm hza.symm
          exact hnot (by simpa [h] using hzw.symm)
        have hwe : w ≠ e := by
          intro h
          have hnot := C.redSide_not_adj_second_neighbor
            (by simp [he]) (by simp [hf]) (by simp [hz]) hef hzf.symm
          exact hnot (by simpa [h] using hzw.symm)
        have hwf : w ≠ f := by
          intro h
          have hnot := C.redSide_not_adj_second_neighbor
            (by simp [hf]) (by simp [he]) (by simp [hz]) hef.symm hze.symm
          exact hnot (by simpa [h] using hzw.symm)
        have hnodup10 : [a, b, c, d, e, f, x, y, z, w].Nodup := by
          have hzOutside : z ∉ [a, b, c, d, e, f, x, y] := by
            simp [hza, hzb, color_ne hz hc (by decide), color_ne hz hd (by decide),
              hze, hzf, color_ne hz hx (by decide), color_ne hz hy (by decide)]
          have hwOutside : w ∉ [a, b, c, d, e, f, x, y] := by
            simp [hwa, hwb, color_ne hw hc (by decide), color_ne hw hd (by decide),
              hwe, hwf, color_ne hw hx (by decide), color_ne hw hy (by decide)]
          rw [show [a, b, c, d, e, f, x, y, z, w] =
            [a, b, c, d, e, f, x, y] ++ [z, w] by rfl,
            List.nodup_append']
          refine ⟨hnodup8, by simp [hzw.ne], ?_⟩
          rw [List.disjoint_left]
          intro u hu huv
          simp only [List.mem_cons, List.not_mem_nil,
            or_false] at huv
          rcases huv with rfl | rfl
          · exact hzOutside hu
          · exact hwOutside hu
        have hsub10 : FormsPath10Subgraph G a b c d e f x y z w := by
          refine ⟨?_, ?_⟩
          · have hvec : (![a, b, c, d, e, f, x, y, z, w] : Fin 10 → V) =
                [a, b, c, d, e, f, x, y, z, w].get := by
              funext i; fin_cases i <;> rfl
            rw [hvec]
            exact hnodup10.injective_get
          · intro i j hij
            have hzy := hyz.symm
            have hwz := hzw.symm
            fin_cases i <;> fin_cases j <;> simp [graphOfEdges] at hij
            all_goals assumption
        exact noResult (lemma5_10_inline C hsub10 ha hb hc hd he hf hx hy hz hw)
    by_cases hBlueF : ∃ x, G.Adj f x ∧ C.color x = .blue
    · exact (extendRight hinduced ha hb hc hd he hf hBlueF).elim
    · have hNoBlueF : ∀ x, G.Adj f x → C.color x ≠ .blue := by
        intro x hfx hx
        exact hBlueF ⟨x, hfx, hx⟩
      by_cases hBlueA : ∃ x, G.Adj a x ∧ C.color x = .blue
      · exact (extendRight hinduced.reverse hf he hd hc hb ha hBlueA).elim
      · have hNoBlueA : ∀ x, G.Adj a x → C.color x ≠ .blue := by
          intro x hax hx
          exact hBlueA ⟨x, hax, hx⟩
        exact noResult (lemma5_11 C hinduced ha hb hc hd he hf
          hNoBlueA hNoBlueF)

end Subcubic
