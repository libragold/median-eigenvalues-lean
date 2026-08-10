import Subcubic.Lemma5_9.SetupK
import Subcubic.Lemma5_5

/-!
# Lemma 5.9, Cases (3.4.1) and (3.4.2)

When `k ~ j`, expose the third neighbor `l` of `k`.  A bluish `l` closes
the induced pentagon `b-a-j-k-c-b` and invokes Lemma 5.5.  The blue case is
recorded for Case (3.4.2).
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9KJBlueConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9KConfiguration C a b c d e f g h where
  hkj : G.Adj k j
  l : V
  hl : C.color l = .blue
  hkl : G.Adj k l
  hlc : l ≠ c
  hlj : l ≠ j
  hkdAdj : ¬ G.Adj k d

theorem lemma5_9_case_k_adj_j
    (C : GoodColoring G) {a b c d e f g h : V}
    (hpath : FormsInducedPath8 G a b c d e f g h)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (he : C.color e = .red)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (Q : Lemma5_9KConfiguration C a b c d e f g h)
    (hkj : G.Adj Q.k Q.j) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_9KJBlueConfiguration C a b c d e f g h) := by
  classical
  rcases Q with ⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
    hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩, hxy, hij, hnotBoth⟩,
    hic, hideg, t, ht, hit, htd, hth⟩,
    k, hk, hck, hkb, hkd, hkg, hkdeg⟩
  change G.Adj k j at hkj
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
  obtain ⟨l, hkl, hlc, hlj⟩ :=
    exists_third_neighbor_of_degree_three hkdeg
      (vertex_ne_of_color_eq hc hj (by decide))
  have hlSide : C.color l = .blue ∨ C.color l = .bluish := by
    rw [← C.not_mem_redSide_iff]
    intro hlRed
    have hcorrect := C.color_correct k
    rw [hk] at hcorrect
    exact hcorrect.2 ⟨l, hlRed, hkl⟩
  rcases hlSide with hl | hl
  · have hkdAdj : ¬ G.Adj k d := by
      intro q
      exact (C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hde hdi
        (hv (u := (2 : Fin 8)) (v := 4) (by decide))
        (vertex_ne_of_color_eq hc hi (by decide))
        (vertex_ne_of_color_eq he hi (by decide)) hck.ne.symm
        (vertex_ne_of_color_eq hk he (by decide))
        (by intro z; apply hic; simpa [← z] using hck.symm)) q.symm
    exact Or.inr ⟨{
      toLemma5_9KConfiguration :=
        ⟨⟨⟨⟨i, j, x, y, hi, hj, hx, hy, hdi, hih, hej, hja,
          hax, hxb, hxj, hby, hya, hyc, hig, hjb⟩,
          hxy, hij, hnotBoth⟩,
          hic, hideg, t, ht, hit, htd, hth⟩,
          k, hk, hck, hkb, hkd, hkg, hkdeg⟩
      hkj := hkj
      l := l
      hl := hl
      hkl := hkl
      hlc := hlc
      hlj := hlj
      hkdAdj := hkdAdj }⟩
  · left
    have hbk : ¬ G.Adj b k :=
      fun q => C.reddish_not_adj_redSide hk (Or.inl hb) q.symm
    have hak : ¬ G.Adj a k :=
      fun q => C.reddish_not_adj_redSide hk (Or.inl ha) q.symm
    have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
    have hcj : ¬ G.Adj c j :=
      C.bluish_not_adj_blueSide hj (Or.inl hc) ∘ SimpleGraph.Adj.symm
    have hba : G.Adj b a := hab.symm
    have hkc : G.Adj k c := hck.symm
    have haj : G.Adj a j := hja.symm
    have hbj : ¬ G.Adj b j := fun q => hjb q.symm
    have hn : [b, a, k, c, j].Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
        List.nodup_nil, not_or, not_false_eq_true, and_true]
      exact ⟨⟨hab.ne.symm, hkb.symm, hbc.ne,
          vertex_ne_of_color_eq hb hj (by decide)⟩,
        ⟨vertex_ne_of_color_eq ha hk (by decide),
          hv (u := (0 : Fin 8)) (v := 2) (by decide), hja.ne.symm⟩,
        ⟨hck.ne.symm, hkj.ne⟩, vertex_ne_of_color_eq hc hj (by decide)⟩
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
      intro v hbV hvc hvj hvblue
      rcases C.neighbor_eq_of_three_neighbors (Or.inl hb)
          hab.symm hbc hby
          (hv (u := (0 : Fin 8)) (v := 2) (by decide)) hya.symm hyc.symm hbV with
        rfl | rfl | rfl
      · simp [ha] at hvblue
      · exact (hvc rfl).elim
      · simp [hy] at hvblue
    have hkNoBlue :
        ∀ v, G.Adj k v → v ≠ c → v ≠ j → C.color v ≠ .blue := by
      intro v hkV hvc hvj hvblue
      by_cases hvl : v = l
      · subst v
        simp [hl] at hvblue
      · exact (not_adj_fourth_neighbor_of_degree_three hkdeg
          hck.symm hkj hkl
          (vertex_ne_of_color_eq hc hj (by decide)) hlc.symm hlj.symm
          hvc hvj hvl hkV).elim
    exact lemma5_5 C hpent hb ha hk hc (Or.inr hj)
      hbNoBlue (fun v hav _ _ => hNoBlueAtA v hav) hkNoBlue

end Subcubic
