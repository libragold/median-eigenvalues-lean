import Subcubic.Lemma5_13.Case4ExactBlueNoRed

/-!
# Lemma 5.13: the reusable blue-neighbor flip

This is the common local argument used several times in Case (4.4.3.3.3):
a red neighbor `r` of the bluish vertex `i` also has a blue neighbor `q`.
After flipping `rq`, either `q` meets one of the two reddish neighbors of
`d`, giving the alternating six-vertex path, or the blue vertex `i` is
handled according as it has a red neighbor.
-/

namespace Subcubic

set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_blue_neighbor_flip
    (C : MatchingCutColoring G) {a b c d h s i r t q qm : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hh : C.color h = .reddish) (hs : C.color s = .reddish)
    (hi : C.color i = .bluish)
    (hdh : G.Adj d h) (hds : G.Adj d s) (hsh : s ≠ h)
    (hih : G.Adj i h) (hir : G.Adj i r) (hid : i ≠ d)
    (hr : C.color r = .red) (ht : C.color t = .red)
    (hq : C.color q = .blue) (hqm : C.color qm = .blue)
    (hrt : G.Adj r t) (hrq : G.Adj r q) (hqqm : G.Adj q qm)
    (hia : ¬ G.Adj i a) (hib : ¬ G.Adj i b)
    (hci : c ≠ i) (hqc : q ≠ c) (hqd : q ≠ d) :
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
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath4 G a b c d := ⟨hinj, hedge⟩
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj u v) :
      G.Adj (![a, b, c, d] u) (![a, b, c, d] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e; subst v; simp_all
  have hra : r ≠ a := by intro e; subst r; exact hia hir
  have hrb : r ≠ b := by intro e; subst r; exact hib hir
  have hqa : q ≠ a := color_ne hq ha (by decide)
  have hqb : q ≠ b := color_ne hq hb (by decide)
  rcases exists_flipAt_or_cutEnhancer C hr hq ht hqm
      (degreeC (Or.inl hr)) (degreeC (Or.inr hq)) hrt hrq hqqm with
    ⟨M, hflip⟩ | hce
  · let D := M.toColoring
    have haD : D.color a = .red :=
      red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
        hra.symm hqa.symm hrb.symm hqb.symm
    have hbD : D.color b = .red :=
      red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
        hrb.symm hqb.symm hra.symm hqa.symm
    have hcD : D.color c = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
        (color_ne hc hr (by decide)) hqc.symm
        (color_ne hd hr (by decide)) hqd.symm
    have hdD : D.color d = .blue :=
      blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
        (color_ne hd hr (by decide)) hqd.symm
        (color_ne hc hr (by decide)) hqc.symm
    have hiD : D.color i = .blue :=
      blue_of_bluish_gains_flipped_red C hflip hi hir
        (color_ne hi hr (by decide)) (color_ne hi hq (by decide))
    have finishNoShare (hhq : ¬ G.Adj h q) (hsq : ¬ G.Adj s q) :
        HasReachableNegativeReduction C := by
      have hhD : D.color h = .reddish :=
        reddish_of_untouched_reddish C hflip hh hhq
          (color_ne hh hr (by decide)) (color_ne hh hq (by decide))
      have hsD : D.color s = .reddish :=
        reddish_of_untouched_reddish C hflip hs hsq
          (color_ne hs hr (by decide)) (color_ne hs hq (by decide))
      by_cases hRedI : ∃ z, G.Adj i z ∧ D.color z = .red
      · obtain ⟨z, hiz, hz⟩ := hRedI
        exact HasReachableNegativeReduction.after_flip C hflip
          (lemma5_13_case4_exact_shared_i_blue_red D hp haD hbD hcD hdD
            hhD hiD hz hdh hih.symm hiz
            (by intro e; subst z; exact hia hiz)
            (by intro e; subst z; exact hib hiz)
            hci (fun e => hid e.symm))
      · have hNoRedI : ∀ z, G.Adj i z → D.color z ≠ .red := by
          intro z hiz hz; exact hRedI ⟨z, hiz, hz⟩
        exact HasReachableNegativeReduction.after_flip C hflip
          (lemma5_13_case4_exact_blue_no_red D hcD hdD hhD hsD hiD
            hcd hdh hds hsh hih hci (fun e => hid e.symm) hNoRedI)
    by_cases hhq : G.Adj h q
    · have hhD : D.color h = .red :=
        red_of_reddish_gains_flipped_blue C hflip hh hhq
          (color_ne hh hr (by decide)) (color_ne hh hq (by decide))
      have hqD : D.color q = .red :=
        red_of_flipped_blue_endpoint C hflip hqm hqqm
          (degreeC (Or.inr hq))
          (color_ne hqm hr (by decide))
      have hah : a ≠ h := color_ne ha hh (by decide)
      have hbh : b ≠ h := color_ne hb hh (by decide)
      have hn : [a, b, c, d, h, q].Nodup := by
        simp [hab.ne, hbc.ne, hcd.ne, hdh.ne, hhq.ne, hah, hbh,
          hqa.symm, hqb.symm,
          vertex_ne_of_color_eq haD hcD (by decide),
          vertex_ne_of_color_eq haD hdD (by decide),
          vertex_ne_of_color_eq hbD hdD (by decide),
          vertex_ne_of_color_eq hcD hhD (by decide), hqc.symm, hqd.symm]
      have hsub : FormsNegativePath6Subgraph G a b c d h q := by
        refine ⟨?_, ?_⟩
        · have hv : (![a,b,c,d,h,q] : Fin 6 → V) =
              [a,b,c,d,h,q].get := by funext z; fin_cases z <;> rfl
          rw [hv]; exact hn.injective_get
        · intro u v huv
          fin_cases u <;> fin_cases v <;>
            simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hdh, hhq] at huv ⊢
      exact HasReachableNegativeReduction.after_flip C hflip
        (lemma5_12_inline D hsub haD hbD hcD hdD hhD hqD)
    · by_cases hsq : G.Adj s q
      · have hsD : D.color s = .red :=
          red_of_reddish_gains_flipped_blue C hflip hs hsq
            (color_ne hs hr (by decide)) (color_ne hs hq (by decide))
        have hqD : D.color q = .red :=
          red_of_flipped_blue_endpoint C hflip hqm hqqm
            (degreeC (Or.inr hq))
            (color_ne hqm hr (by decide))
        have has : a ≠ s := color_ne ha hs (by decide)
        have hbs : b ≠ s := color_ne hb hs (by decide)
        have hn : [a, b, c, d, s, q].Nodup := by
          simp [hab.ne, hbc.ne, hcd.ne, hds.ne, hsq.ne, has, hbs,
            hqa.symm, hqb.symm,
            vertex_ne_of_color_eq haD hcD (by decide),
            vertex_ne_of_color_eq haD hdD (by decide),
            vertex_ne_of_color_eq hbD hdD (by decide),
            vertex_ne_of_color_eq hcD hsD (by decide), hqc.symm, hqd.symm]
        have hsub : FormsNegativePath6Subgraph G a b c d s q := by
          refine ⟨?_, ?_⟩
          · have hv : (![a,b,c,d,s,q] : Fin 6 → V) =
                [a,b,c,d,s,q].get := by funext z; fin_cases z <;> rfl
            rw [hv]; exact hn.injective_get
          · intro u v huv
            fin_cases u <;> fin_cases v <;>
              simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hds, hsq] at huv ⊢
        exact HasReachableNegativeReduction.after_flip C hflip
          (lemma5_12_inline D hsub haD hbD hcD hdD hsD hqD)
      · exact finishNoShare hhq hsq
  · exact HasReachableNegativeReduction.of_current_ce C hce

end Subcubic
