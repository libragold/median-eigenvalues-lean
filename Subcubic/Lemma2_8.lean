import Subcubic.Lemma5_13.Main

/-!
# Lemma 2.8

Starting from a red edge, either every other neighbor is bluish and Lemma
5.4 applies, or a blue edge can be appended.  A further strong-colored edge
gives the three-block path handled by the inlined Lemma 5.12 argument; if no
such extension exists, the four vertices satisfy Lemma 5.13.  Extra edges
between consecutive monochromatic blocks are handled by Lemmas 5.2 and 5.3.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 2.8.** Every red edge yields, after zero or more permitted
cut-preserver flips, a negative tail reducer or a cut enhancer. -/
theorem lemma2_8
    (C : MatchingCutColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) : HasReachableNegativeReduction C := by
  classical
  by_contra hresult
  have noResult (hout : HasReachableNegativeReduction C) : False := hresult hout
  have color_ne {x y : V} {cx cy : Color}
      (hx : C.color x = cx) (hy : C.color y = cy) (hxy : cx ≠ cy) :
      x ≠ y := by
    intro h
    subst y
    simp_all
  have fromCross {u v c : V}
      (hu : C.color u = .red) (hv : C.color v = .red)
      (hc : C.color c = .blue) (huv : G.Adj u v)
      (hvc : G.Adj v c) : False := by
    have hcCorrect := C.color_correct c
    rw [hc] at hcCorrect
    obtain ⟨_, d, hdSide, hcd⟩ := hcCorrect
    have hdCases := (C.not_mem_redSide_iff d).1 hdSide
    have hd : C.color d = .blue := by
      rcases hdCases with hd | hd
      · exact hd
      · exact (C.bluish_not_adj_blueSide hd (Or.inl hc) hcd.symm).elim
    have huc : ¬ G.Adj u c := by
      intro h
      apply noResult
      apply lemma5_2 C u v c d huv hu hv hcd hc hd
      simp [fourVertexCrossEdgeCount, h, hvc]
      omega
    have hud : ¬ G.Adj u d := by
      intro h
      apply noResult
      apply lemma5_2 C u v c d huv hu hv hcd hc hd
      simp [fourVertexCrossEdgeCount, h, hvc]
      omega
    have hvd : ¬ G.Adj v d := by
      intro h
      apply noResult
      apply lemma5_2 C u v c d huv hu hv hcd hc hd
      simp [fourVertexCrossEdgeCount, h, hvc]
    have hNoBlueU : ∀ z, G.Adj u z → C.color z ≠ .blue := by
      intro z huz hz
      have hzc : z ≠ c := by
        intro h
        subst z
        exact huc huz
      have hzd : z ≠ d := by
        intro h
        subst z
        exact hud huz
      have hzCorrect := C.color_correct z
      rw [hz] at hzCorrect
      obtain ⟨_, w, hwSide, hzw⟩ := hzCorrect
      have hwCases := (C.not_mem_redSide_iff w).1 hwSide
      have hw : C.color w = .blue := by
        rcases hwCases with hw | hw
        · exact hw
        · exact (C.bluish_not_adj_blueSide hw (Or.inl hz) hzw.symm).elim
      have hwc : w ≠ c := by
        intro h
        have hnot := C.blueSide_not_adj_second_neighbor
          (by simp [hc]) (by simp [hd]) (by simp [hz]) hcd hzd.symm
        exact hnot (by simpa [h] using hzw.symm)
      have hwd : w ≠ d := by
        intro h
        have hnot := C.blueSide_not_adj_second_neighbor
          (by simp [hd]) (by simp [hc]) (by simp [hz]) hcd.symm hzc.symm
        exact hnot (by simpa [h] using hzw.symm)
      have hnodup : [w, z, u, v, c, d].Nodup := by
        simp [hzw.ne.symm, huv.ne, hcd.ne, hzc, hzd, hwc, hwd,
          color_ne hw hu (by decide), color_ne hw hv (by decide),
          color_ne hz hu (by decide), color_ne hz hv (by decide),
          color_ne hu hc (by decide), color_ne hu hd (by decide),
          color_ne hv hc (by decide), color_ne hv hd (by decide)]
      have hpath : FormsNegativePath6Subgraph G w z u v c d := by
        refine ⟨?_, ?_⟩
        · have hvec : (![w, z, u, v, c, d] : Fin 6 → V) =
              [w, z, u, v, c, d].get := by
            funext i
            fin_cases i <;> rfl
          rw [hvec]
          exact hnodup.injective_get
        · intro i j hij
          have hwz := hzw.symm
          have hzu := huz.symm
          have hvu := huv.symm
          have hcv := hvc.symm
          have hdc := hcd.symm
          fin_cases i <;> fin_cases j <;> simp [graphOfEdges] at hij
          all_goals assumption
      exact noResult (HasReachableNegativeReduction.of_swapSides C
        (lemma5_12_inline C.swapSides hpath
          (by simp [hw]) (by simp [hz]) (by simp [hu])
          (by simp [hv]) (by simp [hc]) (by simp [hd])))
    have hNoRedD : ∀ z, G.Adj d z → C.color z ≠ .red := by
      intro z hdz hz
      have hzu : z ≠ u := by
        intro h
        subst z
        exact hud hdz.symm
      have hzv : z ≠ v := by
        intro h
        subst z
        exact hvd hdz.symm
      have hzCorrect := C.color_correct z
      rw [hz] at hzCorrect
      obtain ⟨_, w, hwSide, hzw⟩ := hzCorrect
      have hwCases := (C.mem_redSide_iff w).1 hwSide
      have hw : C.color w = .red := by
        rcases hwCases with hw | hw
        · exact hw
        · exact (C.reddish_not_adj_redSide hw (Or.inl hz) hzw.symm).elim
      have hwu : w ≠ u := by
        intro h
        have hnot := C.redSide_not_adj_second_neighbor
          (by simp [hu]) (by simp [hv]) (by simp [hz]) huv hzv.symm
        exact hnot (by simpa [h] using hzw.symm)
      have hwv : w ≠ v := by
        intro h
        have hnot := C.redSide_not_adj_second_neighbor
          (by simp [hv]) (by simp [hu]) (by simp [hz]) huv.symm hzu.symm
        exact hnot (by simpa [h] using hzw.symm)
      have hnodup : [u, v, c, d, z, w].Nodup := by
        simp [huv.ne, hcd.ne, hzw.ne, hzu.symm, hzv.symm, hwu.symm, hwv.symm,
          color_ne hu hc (by decide), color_ne hu hd (by decide),
          color_ne hv hc (by decide), color_ne hv hd (by decide),
          color_ne hc hz (by decide), color_ne hc hw (by decide),
          color_ne hd hz (by decide), color_ne hd hw (by decide)]
      have hpath : FormsNegativePath6Subgraph G u v c d z w := by
        refine ⟨?_, ?_⟩
        · have hvec : (![u, v, c, d, z, w] : Fin 6 → V) =
              [u, v, c, d, z, w].get := by
            funext i
            fin_cases i <;> rfl
          rw [hvec]
          exact hnodup.injective_get
        · intro i j hij
          have hvu := huv.symm
          have hcv := hvc.symm
          have hdc := hcd.symm
          have hzd := hdz.symm
          have hwz := hzw.symm
          fin_cases i <;> fin_cases j <;> simp [graphOfEdges] at hij
          all_goals assumption
      exact noResult (lemma5_12_inline C hpath hu hv hc hd hz hw)
    have hpath4 : FormsInducedPath4 G u v c d := by
      refine ⟨?_, ?_⟩
      · have hn : [u, v, c, d].Nodup := by
          simp [huv.ne, hcd.ne, color_ne hu hc (by decide),
            color_ne hu hd (by decide), color_ne hv hc (by decide),
            color_ne hv hd (by decide)]
        have hvec : (![u, v, c, d] : Fin 4 → V) = [u, v, c, d].get := by
          funext i
          fin_cases i <;> rfl
        rw [hvec]
        exact hn.injective_get
      · intro i j
        fin_cases i <;> fin_cases j <;>
          simp [graphOfEdges, SimpleGraph.adj_comm, huv, hvc, hcd,
            huc, hud, hvd]
    exact noResult (lemma5_13 C hpath4 hu hv hc hd hNoBlueU hNoRedD)
  by_cases hBlue : ∃ x, (G.Adj a x ∨ G.Adj b x) ∧ C.color x = .blue
  · obtain ⟨c, hac | hbc, hc⟩ := hBlue
    · exact fromCross hb ha hc hab.symm hac
    · exact fromCross ha hb hc hab hbc
  · have haOther : ∀ v, G.Adj a v → v ≠ b → C.color v = .bluish := by
      intro v hav hvb
      have hvSide := C.other_neighbor_of_red_is_blueSide ha hb hab hav hvb
      rcases hvSide with hv | hv
      · exact (hBlue ⟨v, Or.inl hav, hv⟩).elim
      · exact hv
    have hbOther : ∀ v, G.Adj b v → v ≠ a → C.color v = .bluish := by
      intro v hbV hva
      have hvSide := C.other_neighbor_of_red_is_blueSide hb ha hab.symm hbV hva
      rcases hvSide with hv | hv
      · exact (hBlue ⟨v, Or.inr hbV, hv⟩).elim
      · exact hv
    exact noResult (lemma5_4 C ha hb hab haOther hbOther)

end Subcubic
