import Subcubic.Lemma4_7
import Subcubic.NegativeTailReducerWitnesses

/-!
# Lemma 5.8, Case (2.1)

The four red vertices have bluish third neighbors `p,q,r,s`.  Once the
crossed coincidences have been excluded, failure of either red edge to share
its third neighbor gives one of the terminal negative reducer configurations.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

private theorem color_ne {C : MatchingCutColoring G} {x y : V} {cx cy : Color}
    (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) : x ≠ y := by
  intro h
  subst y
  simp_all

theorem lemma5_8_case2_1
    (C : MatchingCutColoring G) {a b c d e f g h p q r s : V}
    (hcycle : FormsInducedCycle8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (hp : C.color p = .bluish) (hq : C.color q = .bluish)
    (hr : C.color r = .bluish) (hs : C.color s = .bluish)
    (hap : G.Adj a p) (hbq : G.Adj b q)
    (her : G.Adj e r) (hfs : G.Adj f s)
    (hpr : p ≠ r) (hqs : q ≠ s)
    (hqr : q ≠ r) (hps : p ≠ s)
    (hfailure : p ≠ q ∨ r ≠ s) : ContainsNegativeTailReducer C := by
  classical
  dsimp [FormsInducedCycle8] at hcycle
  rcases hcycle with ⟨hinj, hedge⟩
  have hcycleNodup : [a, b, c, d, e, f, g, h].Nodup := by
    simpa using List.nodup_ofFn_ofInjective hinj
  have edge (x y : Fin 8) (hxy : (graphOfEdges
      [(0, 1), (1, 2), (2, 3), (3, 4),
       (4, 5), (5, 6), (6, 7), (7, 0)]).Adj x y) :
      G.Adj (![a, b, c, d, e, f, g, h] x)
        (![a, b, c, d, e, f, g, h] y) := (hedge x y).mp hxy
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have hde : G.Adj d e := edge 3 4 (by native_decide)
  have hef : G.Adj e f := edge 4 5 (by native_decide)
  have hfg : G.Adj f g := edge 5 6 (by native_decide)
  have hgh : G.Adj g h := edge 6 7 (by native_decide)
  have hha : G.Adj h a := edge 7 0 (by native_decide)
  have out {z : V} (hz : C.color z = .bluish) :
      z ∉ [a, b, c, d, e, f, g, h] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨color_ne hz ha (by decide), color_ne hz hb (by decide),
      color_ne hz hc (by decide), color_ne hz hd (by decide),
      color_ne hz he (by decide), color_ne hz hf (by decide),
      color_ne hz hg (by decide), color_ne hz hh (by decide)⟩
  have hpout := out hp
  have hqout := out hq
  have hrout := out hr
  have hsout := out hs
  by_cases hpq : p = q
  · subst q
    have hrs : r ≠ s := hfailure.resolve_left (by simp)
    apply containsNegativeAk C he hf ha hb hr hs hg hh hc hd hp
      hef her hde.symm hfs hfg hab hha.symm hap hbc hbq hgh hcd
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil]
      at hcycleNodup hpout hrout hsout ⊢
    grind
  · by_cases hrs : r = s
    · subst s
      apply containsNegativeAk C ha hb he hf hp hq hc hd hg hh hr
        hab hap hha.symm hbq hbc hef hde.symm her hfg hfs hcd hgh
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil]
        at hcycleNodup hpout hqout hrout ⊢
      grind
    · apply containsNegativeAl C ha hb he hf hp hq hc hd hg hh hs hr
        hab hap hha.symm hbq hbc hef hde.symm her hfg hfs hcd hgh
      simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil]
        at hcycleNodup hpout hqout hrout hsout ⊢
      grind

end Subcubic
