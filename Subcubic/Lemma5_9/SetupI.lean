import Subcubic.Lemma5_9.Cases3_1To3_3
import Subcubic.Lemma3_7

/-!
# Lemma 5.9, start of Case (3.4)

After orienting so that `i` is not adjacent to `c`, Lemma 3.7 gives degree
three at `i`.  Its third neighbor `t` is bluish; if it were blue, the five
vertices `d,e,h,i,t` would induce cut enhancer `c` after swapping sides.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9IConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9Case3_4Configuration C a b c d e f g h where
  hic : ¬ G.Adj i c
  hideg : vertexDegree G i = 3
  t : V
  ht : C.color t = .bluish
  hit : G.Adj i t
  htd : t ≠ d
  hth : t ≠ h

theorem lemma5_9_setup_i
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red) (hf : C.color f = .red)
    (hg : C.color g = .blue) (hh : C.color h = .blue)
    (Q : Lemma5_9Case3_4Configuration C a b c d e f g h)
    (hic : ¬ G.Adj Q.i c) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9IConfiguration C a b c d e f g h) := by
  classical
  rcases Q with ⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩
  change ¬ G.Adj i c at hic
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
  have hde := edge 3 4 (by native_decide)
  have hef := edge 4 5 (by native_decide)
  have hgh := edge 6 7 (by native_decide)
  rcases lemma3_7 C he hd hi hde.symm hdi with hideg | hce
  · obtain ⟨t, hit, htd, hth⟩ :=
      exists_third_neighbor_of_degree_three hideg
        (hv (u := (3 : Fin 8)) (v := 7) (by decide))
    have htSide : C.color t = .blue ∨ C.color t = .bluish := by
      rw [← C.not_mem_redSide_iff]
      intro htRed
      have hcorrect := C.color_correct i
      rw [hi] at hcorrect
      exact hcorrect.2 ⟨t, htRed, hit⟩
    rcases htSide with ht | ht
    · left
      have hdh : ¬ G.Adj d h := by simpa using nonedge 3 7 (by native_decide)
      have htc : t ≠ c := by intro q; subst t; exact hic hit
      have hdt : ¬ G.Adj d t :=
        C.blueSide_not_adj_second_neighbor (by simp [hd]) (by simp [hc])
          (by simp [ht]) (edge 3 2 (by native_decide)) htc.symm
      have heh : ¬ G.Adj e h := by simpa using nonedge 4 7 (by native_decide)
      have htg : t ≠ g := by intro q; subst t; exact hig hit
      have hht : ¬ G.Adj h t :=
        C.blueSide_not_adj_second_neighbor (by simp [hh]) (by simp [hg])
          (by simp [ht]) hgh.symm htg.symm
      have hei : ¬ G.Adj e i :=
        fun q => C.reddish_not_adj_redSide hi (Or.inl he) q.symm
      have het : ¬ G.Adj e t := by
        apply not_adj_fourth_neighbor_of_subcubic C.subcubic
          hde.symm hef hej
        · exact hv (u := (3 : Fin 8)) (v := 5) (by decide)
        · exact vertex_ne_of_color_eq hd hj (by decide)
        · exact vertex_ne_of_color_eq hf hj (by decide)
        · exact htd
        · exact vertex_ne_of_color_eq ht hf (by decide)
        · exact vertex_ne_of_color_eq ht hj (by decide)
      have hceSwap := containsCutEnhancerC_of C.swapSides
        (a := d) (b := h) (c := e) (d := i) (e := t)
        (by simp [hd]) (by simp [hh]) (by simp [he]) (by simp [hi])
        (by simp [ht]) hde hdi hih.symm hit
        hdh hdt (fun q => heh q.symm) hht hei het
        (hv (u := (3 : Fin 8)) (v := 7) (by decide))
        htd.symm hth.symm
      exact HasReachableNegativeReduction.of_current_ce C
        ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hceSwap)
    · right
      exact ⟨{
        toLemma4_8Case3_4Configuration :=
          ⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
            hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩
        hic := hic
        hideg := hideg
        t := t
        ht := ht
        hit := hit
        htd := htd
        hth := hth }⟩
  · exact Or.inl (HasReachableNegativeReduction.of_lemma3_6 C hce)

end Subcubic
