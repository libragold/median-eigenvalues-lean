import Subcubic.Lemma5_13.Case4ExactNoRedLow
import Subcubic.Lemma5_13.Case4BlueNeighborFlip

/-!
# Lemma 5.13, Case (4.4.3.3.3)

The third neighbor `i` of the unique common reddish neighbor of `d` and
`g` is bluish and has a red neighbor.  This is the flip chain in the final
part of Case (4.4.3.3).
-/

namespace Subcubic

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_exact_bluish_red
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ z, G.Adj d z → C.color z ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hgf : ¬ G.Adj Q.g Q.f) (hdf : ¬ G.Adj d Q.f)
    (hgdeg : vertexDegree G Q.g = 3)
    (hNoShareDE : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj d z)
    (hNoShareEG : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj Q.g z)
    {x h s i : V}
    (hx : C.color x = .reddish) (hh : C.color h = .reddish)
    (hs : C.color s = .reddish) (hi : C.color i = .bluish)
    (hgx : G.Adj Q.g x) (hgh : G.Adj Q.g h)
    (hxh : x ≠ h) (hdh : G.Adj d h) (hds : G.Adj d s)
    (hsh : s ≠ h) (hih : G.Adj i h) (hig : i ≠ Q.g) (hid : i ≠ d)
    (hUniqueDG : ∀ z, C.color z = .reddish →
      G.Adj Q.g z → G.Adj d z → z = h)
    {j : V} (hj : C.color j = .red) (hij : G.Adj i j) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath4 G a b c d := ⟨hinj, hedge⟩
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj u v) :
      G.Adj (![a, b, c, d] u) (![a, b, c, d] v) := (hedge u v).mp huv
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hacV : a ≠ c := by simpa using hinj.ne (show (0 : Fin 4) ≠ 2 by decide)
  have hadV : a ≠ d := by simpa using hinj.ne (show (0 : Fin 4) ≠ 3 by decide)
  have hbdV : b ≠ d := by simpa using hinj.ne (show (1 : Fin 4) ≠ 3 by decide)
  by_contra hfinal
  have noResult (hr : HasReachableNegativeReduction C) : False := hfinal hr
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (noResult (.of_current_ntr C hntr)).elim
    · exact (noResult (.of_current_ce C hce)).elim
  have noCE (hce : ContainsCutEnhancer C) : False :=
    noResult (HasReachableNegativeReduction.of_current_ce C hce)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e; subst v; simp_all
  have hjCorrect := C.color_correct j
  rw [hj] at hjCorrect
  obtain ⟨_, k, hkSide, hjk⟩ := hjCorrect
  have hkCases := (C.mem_redSide_iff k).1 hkSide
  have hk : C.color k = .red := by
    rcases hkCases with hk | hk
    · exact hk
    · exact (C.reddish_not_adj_redSide hk (Or.inl hj) hjk.symm).elim
  obtain ⟨l, hjl, hli, hlk⟩ :=
    exists_third_neighbor_of_degree_three
      (degreeC (Or.inl hj)) (color_ne hi hk (by decide))
  have hlSide := C.other_neighbor_of_red_is_blueSide hj hk hjk hjl hlk
  have hie : i ≠ Q.e := by
    intro q; subst i
    exact hNoShareDE h hh hih hdh
  have hja : j ≠ a := by
    intro q; subst j
    have hai : ¬ G.Adj a i := by
      apply not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
      · exact color_ne hb Q.he (by decide)
      · exact color_ne hb Q.hg (by decide)
      · exact Q.hge.symm
      · exact color_ne hi hb (by decide)
      · exact hie
      · exact hig
    exact hai hij.symm
  have hjb : j ≠ b := by
    intro q; subst j
    have hbi : ¬ G.Adj b i := by
      apply not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
      · exact color_ne ha hc (by decide)
      · exact color_ne ha Q.he (by decide)
      · exact color_ne hc Q.he (by decide)
      · exact color_ne hi ha (by decide)
      · exact color_ne hi hc (by decide)
      · exact hie
    exact hbi hij.symm
  have hia : ¬ G.Adj i a := by
    intro hia
    apply (not_adj_fourth_neighbor_of_degree_three
      (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
      (color_ne hb Q.he (by decide)) (color_ne hb Q.hg (by decide))
      Q.hge.symm (color_ne hi hb (by decide)) hie hig)
    exact hia.symm
  have hib : ¬ G.Adj i b := by
    intro hib
    apply (not_adj_fourth_neighbor_of_degree_three
      (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
      (color_ne ha hc (by decide)) (color_ne ha Q.he (by decide))
      (color_ne hc Q.he (by decide)) (color_ne hi ha (by decide))
      (color_ne hi hc (by decide)) hie)
    exact hib.symm
  have hci : c ≠ i := by
    intro q; subst i
    have hch : ¬ G.Adj c h := by
      apply not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
      · exact color_ne hb hd (by decide)
      · exact color_ne hb Q.hf (by decide)
      · exact color_ne hd Q.hf (by decide)
      · exact color_ne hh hb (by decide)
      · exact color_ne hh hd (by decide)
      · intro q; subst h; exact hdf hdh
    exact hch hih
  rcases hlSide with hl | hl
  · obtain ⟨m, hm, hlm⟩ := C.exists_blue_mate hl
    rcases exists_flipAt_or_cutEnhancer C hj hl hk hm
        (degreeC (Or.inl hj)) (degreeC (Or.inr hl)) hjk hjl hlm with
      ⟨M, hflip⟩ | hce
    · let D := M.toColoring
      have degreeD {v : V} (hv : D.color v = .red ∨ D.color v = .blue) :
          vertexDegree G v = 3 := by
        rcases lemma3_6_negative D hv with hdegree | hntr | hce
        · exact hdegree
        · exact (noResult (HasReachableNegativeReduction.after_flip C hflip
            (.of_current_ntr D hntr))).elim
        · exact (noResult (HasReachableNegativeReduction.after_flip C hflip
            (.of_current_ce D hce))).elim
      have hla : l ≠ a := color_ne hl ha (by decide)
      have hlb : l ≠ b := color_ne hl hb (by decide)
      have hlc : l ≠ c := by
        intro q; subst l
        have hcj : ¬ G.Adj c j := by
          apply not_adj_fourth_neighbor_of_degree_three
            (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
          · exact color_ne hb hd (by decide)
          · exact color_ne hb Q.hf (by decide)
          · exact color_ne hd Q.hf (by decide)
          · exact hjb
          · exact color_ne hj hd (by decide)
          · exact color_ne hj Q.hf (by decide)
        exact hcj hjl.symm
      have hld : l ≠ d := by
        intro q; subst l
        exact hNoRedAtD j hjl.symm hj
      have haD : D.color a = .red :=
        red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
          hja.symm hla.symm hjb.symm hlb.symm
      have hbD : D.color b = .red :=
        red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
          hjb.symm hlb.symm hja.symm hla.symm
      have hcD : D.color c = .blue :=
        blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
          (color_ne hc hj (by decide)) hlc.symm
          (color_ne hd hj (by decide)) hld.symm
      have hdD : D.color d = .blue :=
        blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
          (color_ne hd hj (by decide)) hld.symm
          (color_ne hc hj (by decide)) hlc.symm
      have hiD : D.color i = .blue :=
        blue_of_bluish_gains_flipped_red C hflip hi hij
          (color_ne hi hj (by decide)) (color_ne hi hl (by decide))
      have finishNoShare (hhl : ¬ G.Adj h l) (hsl : ¬ G.Adj s l) : False := by
        have hhD : D.color h = .reddish :=
          reddish_of_untouched_reddish C hflip hh hhl
            (color_ne hh hj (by decide)) (color_ne hh hl (by decide))
        have hsD : D.color s = .reddish :=
          reddish_of_untouched_reddish C hflip hs hsl
            (color_ne hs hj (by decide)) (color_ne hs hl (by decide))
        by_cases hRedI : ∃ z, G.Adj i z ∧ D.color z = .red
        · obtain ⟨z, hiz, hz⟩ := hRedI
          exact noResult (HasReachableNegativeReduction.after_flip C hflip
            (lemma5_13_case4_exact_shared_i_blue_red D hp haD hbD hcD hdD
              hhD hiD hz hdh hih.symm hiz
              (by intro q; subst z; exact hia hiz)
              (by intro q; subst z; exact hib hiz)
              hci (fun q => hid q.symm)))
        · have hNoRedI : ∀ z, G.Adj i z → D.color z ≠ .red := by
            intro z hiz hz; exact hRedI ⟨z, hiz, hz⟩
          exact noResult (HasReachableNegativeReduction.after_flip C hflip
            (lemma5_13_case4_exact_blue_no_red D hcD hdD hhD hsD hiD
              hcd hdh hds hsh hih hci (fun q => hid q.symm) hNoRedI))
      by_cases hhl : G.Adj h l
      · have hhD : D.color h = .red :=
          red_of_reddish_gains_flipped_blue C hflip hh hhl
            (color_ne hh hj (by decide)) (color_ne hh hl (by decide))
        have hlD : D.color l = .red :=
          red_of_flipped_blue_endpoint C hflip hm hlm
            (degreeC (Or.inr hl)) (color_ne hm hj (by decide))
        have hah : a ≠ h := by intro q; subst h; exact hNoRedAtD a hdh ha
        have hbh : b ≠ h := by intro q; subst h; exact hNoRedAtD b hdh hb
        have hn : [a, b, c, d, h, l].Nodup := by
          simp [hab.ne, hbc.ne, hcd.ne, hdh.ne, hhl.ne, hah, hbh,
            hla.symm, hlb.symm,
            vertex_ne_of_color_eq haD hcD (by decide),
            vertex_ne_of_color_eq haD hdD (by decide),
            vertex_ne_of_color_eq hbD hdD (by decide),
            vertex_ne_of_color_eq hcD hhD (by decide), hlc.symm,
            hld.symm]
        have hsub : FormsNegativePath6Subgraph G a b c d h l := by
          refine ⟨?_, ?_⟩
          · have hv : (![a,b,c,d,h,l] : Fin 6 → V) = [a,b,c,d,h,l].get := by
              funext z; fin_cases z <;> rfl
            rw [hv]; exact hn.injective_get
          · intro u v huv
            fin_cases u <;> fin_cases v <;>
              simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hdh, hhl] at huv ⊢
        exact noResult (HasReachableNegativeReduction.after_flip C hflip
          (lemma5_12_inline D hsub haD hbD hcD hdD hhD hlD))
      · by_cases hsl : G.Adj s l
        · have hsD : D.color s = .red :=
            red_of_reddish_gains_flipped_blue C hflip hs hsl
              (color_ne hs hj (by decide)) (color_ne hs hl (by decide))
          have hlD : D.color l = .red :=
            red_of_flipped_blue_endpoint C hflip hm hlm
              (degreeC (Or.inr hl)) (color_ne hm hj (by decide))
          have has : a ≠ s := by intro q; subst s; exact hNoRedAtD a hds ha
          have hbs : b ≠ s := by intro q; subst s; exact hNoRedAtD b hds hb
          have hn : [a, b, c, d, s, l].Nodup := by
            simp [hab.ne, hbc.ne, hcd.ne, hds.ne, hsl.ne, has, hbs,
              hla.symm, hlb.symm,
              vertex_ne_of_color_eq haD hcD (by decide),
              vertex_ne_of_color_eq haD hdD (by decide),
              vertex_ne_of_color_eq hbD hdD (by decide),
              vertex_ne_of_color_eq hcD hsD (by decide), hlc.symm,
              hld.symm]
          have hsub : FormsNegativePath6Subgraph G a b c d s l := by
            refine ⟨?_, ?_⟩
            · have hv : (![a,b,c,d,s,l] : Fin 6 → V) = [a,b,c,d,s,l].get := by
                funext z; fin_cases z <;> rfl
              rw [hv]; exact hn.injective_get
            · intro u v huv
              fin_cases u <;> fin_cases v <;>
                simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hds, hsl] at huv ⊢
          exact noResult (HasReachableNegativeReduction.after_flip C hflip
            (lemma5_12_inline D hsub haD hbD hcD hdD hsD hlD))
        · exact finishNoShare hhl hsl
    · exact (noCE hce).elim
  · have kNoBlue : (∀ z, G.Adj k z → C.color z ≠ .blue) → False := by
      intro hNoBlueK
      have hjOther : ∀ z, G.Adj j z → z ≠ k → C.color z = .bluish := by
        intro z hjz hzk
        rcases neighbor_eq_of_degree_three
            (degreeC (Or.inl hj)) hjk hij.symm hjl
            (color_ne hk hi (by decide)) (color_ne hk hl (by decide))
            hli.symm hjz with q | q | q
        · exact (hzk q).elim
        · simpa [q] using hi
        · simpa [q] using hl
      have hkOther : ∀ z, G.Adj k z → z ≠ j → C.color z = .bluish := by
        intro z hkz hzj
        cases hz : C.color z with
        | red =>
            exact (C.redSide_not_adj_second_neighbor (by simp [hk])
              (by simp [hj]) (by simp [hz]) hjk.symm hzj.symm hkz).elim
        | reddish => exact (C.reddish_not_adj_redSide hz (Or.inl hk) hkz.symm).elim
        | blue => exact (hNoBlueK z hkz hz).elim
        | bluish => rfl
      exact noResult (lemma5_4 C hj hk hjk hjOther hkOther)
    have hHasBlue : ∃ o, G.Adj k o ∧ C.color o = .blue := by
      by_contra hnone
      push Not at hnone
      exact kNoBlue hnone
    obtain ⟨o, hko, ho⟩ := hHasBlue
    obtain ⟨om, hom, hoom⟩ := C.exists_blue_mate ho
    have hka : k ≠ a := by
      intro q; subst k
      exact (C.redSide_not_adj_second_neighbor
        (by simp [ha]) (by simp [hb]) (by simp [hj]) hab hjb.symm) hjk.symm
    have hkb : k ≠ b := by
      intro q; subst k
      exact (C.redSide_not_adj_second_neighbor
        (by simp [hb]) (by simp [ha]) (by simp [hj]) hab.symm hja.symm) hjk.symm
    have hoc : o ≠ c := by
      intro q; subst o
      have hck : ¬ G.Adj c k := by
        apply not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
        · exact color_ne hb hd (by decide)
        · exact color_ne hb Q.hf (by decide)
        · exact color_ne hd Q.hf (by decide)
        · exact hkb
        · exact color_ne hk hd (by decide)
        · exact color_ne hk Q.hf (by decide)
      exact hck hko.symm
    have hod : o ≠ d := by
      intro q; subst o
      exact hNoRedAtD k hko.symm hk
    by_cases hik : G.Adj i k
    · exact noResult (lemma5_13_case4_blue_neighbor_flip C hp ha hb hc hd
        hh hs hi hdh hds hsh hih hik hid hk hj ho hom hjk.symm hko hoom
        hia hib hci hoc hod)
    · rcases exists_flipAt_or_cutEnhancer C hk ho hj hom
          (degreeC (Or.inl hk)) (degreeC (Or.inr ho)) hjk.symm hko hoom with
        ⟨M, hflip⟩ | hce
      · let D := M.toColoring
        have degreeD {v : V} (hv : D.color v = .red ∨ D.color v = .blue) :
            vertexDegree G v = 3 := by
          rcases lemma3_6_negative D hv with hdegree | hntr | hce
          · exact hdegree
          · exact (noResult (HasReachableNegativeReduction.after_flip C hflip
              (.of_current_ntr D hntr))).elim
          · exact (noResult (HasReachableNegativeReduction.after_flip C hflip
              (.of_current_ce D hce))).elim
        have haD : D.color a = .red :=
          red_of_untouched_red_edge C hflip (by simp [ha]) (by simp [hb]) hab
            hka.symm (color_ne ha ho (by decide))
            hkb.symm (color_ne hb ho (by decide))
        have hbD : D.color b = .red :=
          red_of_untouched_red_edge C hflip (by simp [hb]) (by simp [ha]) hab.symm
            hkb.symm (color_ne hb ho (by decide))
            hka.symm (color_ne ha ho (by decide))
        have hcD : D.color c = .blue :=
          blue_of_untouched_blue_edge C hflip (by simp [hc]) (by simp [hd]) hcd
            (color_ne hc hk (by decide)) hoc.symm
            (color_ne hd hk (by decide)) hod.symm
        have hdD : D.color d = .blue :=
          blue_of_untouched_blue_edge C hflip (by simp [hd]) (by simp [hc]) hcd.symm
            (color_ne hd hk (by decide)) hod.symm
            (color_ne hc hk (by decide)) hoc.symm
        have hiD : D.color i = .bluish :=
          bluish_of_untouched_bluish C hflip hi hik
            (color_ne hi hk (by decide)) (color_ne hi ho (by decide))
        have hjo : ¬ G.Adj j o := by
          apply not_adj_fourth_neighbor_of_degree_three
            (degreeC (Or.inl hj)) hjk hij.symm hjl
          · exact color_ne hk hi (by decide)
          · exact color_ne hk hl (by decide)
          · exact hli.symm
          · exact color_ne ho hk (by decide)
          · exact color_ne ho hi (by decide)
          · exact color_ne ho hl (by decide)
        have hjD : D.color j = .reddish :=
          reddish_of_red_loses_flipped_mate C hflip hj hjk hjo
            hjk.ne (color_ne hj ho (by decide))
        by_cases hho : G.Adj h o
        · have hhD : D.color h = .red :=
            red_of_reddish_gains_flipped_blue C hflip hh hho
              (color_ne hh hk (by decide)) (color_ne hh ho (by decide))
          have hoD : D.color o = .red :=
            red_of_flipped_blue_endpoint C hflip hom hoom
              (degreeC (Or.inr ho))
              (color_ne hom hk (by decide))
          have hn : [a, b, c, d, h, o].Nodup := by
            simp [hab.ne, hbc.ne, hcd.ne, hdh.ne, hho.ne, hoc.symm, hod.symm,
              hacV, hadV, hbdV,
              color_ne ha hh (by decide), color_ne hb hh (by decide),
              color_ne ha ho (by decide), color_ne hb ho (by decide),
              color_ne hc hh (by decide), color_ne hd hh (by decide)]
          have hsub : FormsNegativePath6Subgraph G a b c d h o := by
            refine ⟨?_, ?_⟩
            · have hv : (![a,b,c,d,h,o] : Fin 6 → V) =
                  [a,b,c,d,h,o].get := by funext z; fin_cases z <;> rfl
              rw [hv]; exact hn.injective_get
            · intro u v huv
              fin_cases u <;> fin_cases v <;>
                simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hdh, hho] at huv ⊢
          exact noResult (HasReachableNegativeReduction.after_flip C hflip
            (lemma5_12_inline D hsub haD hbD hcD hdD hhD hoD))
        · by_cases hso : G.Adj s o
          · have hsD : D.color s = .red :=
              red_of_reddish_gains_flipped_blue C hflip hs hso
                (color_ne hs hk (by decide)) (color_ne hs ho (by decide))
            have hoD : D.color o = .red :=
              red_of_flipped_blue_endpoint C hflip hom hoom
                (degreeC (Or.inr ho))
                (color_ne hom hk (by decide))
            have hn : [a, b, c, d, s, o].Nodup := by
              simp [hab.ne, hbc.ne, hcd.ne, hds.ne, hso.ne, hoc.symm, hod.symm,
                hacV, hadV, hbdV,
                color_ne ha hs (by decide), color_ne hb hs (by decide),
                color_ne ha ho (by decide), color_ne hb ho (by decide),
                color_ne hc hs (by decide), color_ne hd hs (by decide)]
            have hsub : FormsNegativePath6Subgraph G a b c d s o := by
              refine ⟨?_, ?_⟩
              · have hv : (![a,b,c,d,s,o] : Fin 6 → V) =
                    [a,b,c,d,s,o].get := by funext z; fin_cases z <;> rfl
                rw [hv]; exact hn.injective_get
              · intro u v huv
                fin_cases u <;> fin_cases v <;>
                  simp [graphOfEdges, G.adj_comm, hab, hbc, hcd, hds, hso] at huv ⊢
            exact noResult (HasReachableNegativeReduction.after_flip C hflip
              (lemma5_12_inline D hsub haD hbD hcD hdD hsD hoD))
          · have hhD : D.color h = .reddish :=
              reddish_of_untouched_reddish C hflip hh hho
                (color_ne hh hk (by decide)) (color_ne hh ho (by decide))
            have hsD : D.color s = .reddish :=
              reddish_of_untouched_reddish C hflip hs hso
                (color_ne hs hk (by decide)) (color_ne hs ho (by decide))
            have hck : ¬ G.Adj c k := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
              · exact color_ne hb hd (by decide)
              · exact color_ne hb Q.hf (by decide)
              · exact color_ne hd Q.hf (by decide)
              · exact hkb
              · exact color_ne hk hd (by decide)
              · exact color_ne hk Q.hf (by decide)
            have hbo : ¬ G.Adj b o := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
              · exact color_ne ha hc (by decide)
              · exact color_ne ha Q.he (by decide)
              · exact color_ne hc Q.he (by decide)
              · exact color_ne ho ha (by decide)
              · exact hoc
              · exact color_ne ho Q.he (by decide)
            have hco : ¬ G.Adj c o :=
              C.blueSide_not_adj_second_neighbor (by simp [hc]) (by simp [hd])
                (by simp [ho]) hcd hod.symm
            have hbk : ¬ G.Adj b k := by
              apply C.redSide_not_adj_second_neighbor
                (by simp [hb]) (by simp [ha]) (by simp [hk]) hab.symm hka.symm
            by_cases hCommonC : ∃ z, G.Adj c z ∧ G.Adj o z
            · obtain ⟨z, hcz, hoz⟩ := hCommonC
              have hzf : z = Q.f := by
                rcases neighbor_eq_of_degree_three
                    (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
                    (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
                    (color_ne hd Q.hf (by decide)) hcz with rfl | rfl | rfl
                · exact (hbo hoz.symm).elim
                · exact (C.blueSide_not_adj_second_neighbor
                    (by simp [hd]) (by simp [hc]) (by simp [ho]) hcd.symm
                    hoc.symm hoz.symm).elim
                · rfl
              subst z
              exact noResult (HasReachableNegativeReduction.of_current_ce C
                (containsCutEnhancerB_of C Q.hf hc hb ho hk Q.hcf.symm hoz.symm
                  hbc.symm hko.symm
                  (C.reddish_not_adj_redSide Q.hf (Or.inl hb))
                  (C.reddish_not_adj_redSide Q.hf (Or.inl hk))
                  hco hck hbo hbk))
            · have hfo : ¬ G.Adj Q.f o := by
                intro hfo
                exact hCommonC ⟨Q.f, Q.hcf, hfo.symm⟩
              by_cases hCommonE : ∃ z, G.Adj Q.e z ∧ G.Adj o z
              · obtain ⟨z, hez, hoz⟩ := hCommonE
                have hao : ¬ G.Adj a o := by
                  apply not_adj_fourth_neighbor_of_degree_three
                    (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
                  · exact color_ne hb Q.he (by decide)
                  · exact color_ne hb Q.hg (by decide)
                  · exact Q.hge.symm
                  · exact color_ne ho hb (by decide)
                  · exact color_ne ho Q.he (by decide)
                  · exact color_ne ho Q.hg (by decide)
                have hzr : z = Q.r := by
                  rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                      Q.heaEdge Q.her
                      hab.ne.symm
                      (color_ne hb Q.hr (by decide))
                      (color_ne ha Q.hr (by decide)) hez with q | q | q
                  · exact (hbo (q ▸ hoz.symm)).elim
                  · exact (hao (q ▸ hoz.symm)).elim
                  · exact q
                subst z
                have heD : D.color Q.e = .bluish := by
                  apply bluish_of_untouched_bluish C hflip Q.he
                  · intro hek
                    rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                        Q.heaEdge Q.her
                        hab.ne.symm
                        (color_ne hb Q.hr (by decide))
                        (color_ne ha Q.hr (by decide)) hek with q | q | q
                    · exact hkb q
                    · exact hka q
                    · exact color_ne hk Q.hr (by decide) q
                  · exact color_ne Q.he hk (by decide)
                  · exact color_ne Q.he ho (by decide)
                have hfD : D.color Q.f = .reddish :=
                  reddish_of_untouched_reddish C hflip Q.hf hfo
                    (color_ne Q.hf hk (by decide)) (color_ne Q.hf ho (by decide))
                have hrD : D.color Q.r = .red :=
                  red_of_reddish_gains_flipped_blue C hflip Q.hr hoz.symm
                    (color_ne Q.hr hk (by decide)) (color_ne Q.hr ho (by decide))
                let T : Lemma5_13ThirdNeighborConfiguration D a b c d := {
                  e := Q.e, f := Q.f, he := heD, hf := hfD,
                  hbe := Q.hbe, hcf := Q.hcf, hea := Q.hea,
                  hec := Q.hec, hfb := Q.hfb, hfd := Q.hfd,
                  hedeg := Q.hedeg, hfdeg := Q.hfdeg }
                obtain ⟨R, hRT⟩ := lemma5_13_case2_setup D T hrD Q.her Q.hra Q.hrb
                rcases lemma5_13_case2_flip_path D hp haD hbD hcD hdD R with
                  hresult | hpath3
                · exact noResult (HasReachableNegativeReduction.after_flip C hflip hresult)
                · obtain ⟨P⟩ := hpath3
                  exact noResult (HasReachableNegativeReduction.after_flip C hflip P.reduces)
              · have hro : ¬ G.Adj Q.r o := by
                  intro hro; exact hCommonE ⟨Q.r, Q.her, hro.symm⟩
                have hek : ¬ G.Adj Q.e k := by
                  intro hek
                  rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                      Q.heaEdge Q.her
                      hab.ne.symm
                      (color_ne hb Q.hr (by decide))
                      (color_ne ha Q.hr (by decide)) hek with q | q | q
                  · exact hkb q
                  · exact hka q
                  · exact color_ne hk Q.hr (by decide) q
                have hgk : ¬ G.Adj Q.g k := by
                  intro hgk
                  rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                      (color_ne ha hx (by decide))
                      (color_ne ha hh (by decide)) hxh hgk with q | q | q
                  · exact hka q
                  · exact color_ne hk hx (by decide) q
                  · exact color_ne hk hh (by decide) q
                have heD : D.color Q.e = .bluish :=
                  bluish_of_untouched_bluish C hflip Q.he hek
                    (color_ne Q.he hk (by decide)) (color_ne Q.he ho (by decide))
                have hfD : D.color Q.f = .reddish :=
                  reddish_of_untouched_reddish C hflip Q.hf hfo
                    (color_ne Q.hf hk (by decide)) (color_ne Q.hf ho (by decide))
                have hgD : D.color Q.g = .bluish :=
                  bluish_of_untouched_bluish C hflip Q.hg hgk
                    (color_ne Q.hg hk (by decide)) (color_ne Q.hg ho (by decide))
                have hrD : D.color Q.r = .reddish :=
                  reddish_of_untouched_reddish C hflip Q.hr hro
                    (color_ne Q.hr hk (by decide)) (color_ne Q.hr ho (by decide))
                let QD : Lemma5_13Case4Configuration D a b c d := {
                  e := Q.e, f := Q.f, he := heD, hf := hfD,
                  hbe := Q.hbe, hcf := Q.hcf, hea := Q.hea,
                  hec := Q.hec, hfb := Q.hfb, hfd := Q.hfd,
                  hedeg := Q.hedeg, hfdeg := Q.hfdeg,
                  heaEdge := Q.heaEdge, hef := Q.hef,
                  g := Q.g, hg := hgD, hag := Q.hag,
                  hgb := Q.hgb, hge := Q.hge,
                  r := Q.r, hr := hrD, her := Q.her,
                  hra := Q.hra, hrb := Q.hrb }
                have hNoRedAtDD : ∀ z, G.Adj d z → D.color z ≠ .red := by
                  intro z hdz hz
                  rcases neighbor_eq_of_degree_three
                      (degreeC (Or.inr hd)) hcd.symm hdh hds
                      (color_ne hc hh (by decide))
                      (color_ne hc hs (by decide)) hsh.symm hdz with q | q | q
                  · subst z; simp [hcD] at hz
                  · subst z; simp [hhD] at hz
                  · subst z; simp [hsD] at hz
                by_cases hCommonG : ∃ z, G.Adj Q.g z ∧ G.Adj o z
                · obtain ⟨z, hgz, hoz⟩ := hCommonG
                  have hao : ¬ G.Adj a o := by
                    apply not_adj_fourth_neighbor_of_degree_three
                      (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
                    · exact color_ne hb Q.he (by decide)
                    · exact color_ne hb Q.hg (by decide)
                    · exact Q.hge.symm
                    · exact color_ne ho hb (by decide)
                    · exact color_ne ho Q.he (by decide)
                    · exact color_ne ho Q.hg (by decide)
                  have hzx : z = x := by
                    rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                        (color_ne ha hx (by decide))
                        (color_ne ha hh (by decide)) hxh hgz with q | q | q
                    · exact (hao (q ▸ hoz.symm)).elim
                    · exact q
                    · exact (hho (q ▸ hoz.symm)).elim
                  subst z
                  have hxD : D.color x = .red :=
                    red_of_reddish_gains_flipped_blue C hflip hx hoz.symm
                      (color_ne hx hk (by decide)) (color_ne hx ho (by decide))
                  exact noResult (HasReachableNegativeReduction.after_flip C hflip
                    (lemma5_13_case4_red_neighbor D hp haD hbD hcD hdD
                      hNoRedAtDD QD hxD hgx (color_ne hx ha (by decide))))
                · have hxo : ¬ G.Adj x o := by
                    intro hxo; exact hCommonG ⟨x, hgx, hxo.symm⟩
                  have hxD : D.color x = .reddish :=
                    reddish_of_untouched_reddish C hflip hx hxo
                      (color_ne hx hk (by decide)) (color_ne hx ho (by decide))
                  have hNoShareDED : ∀ z, D.color z = .reddish →
                      G.Adj Q.e z → ¬ G.Adj d z := by
                    intro z hz hez hdz
                    rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                        Q.heaEdge Q.her
                        hab.ne.symm
                        (vertex_ne_of_color_eq hbD hrD (by decide))
                        (vertex_ne_of_color_eq haD hrD (by decide)) hez with q | q | q
                    · subst z; simp [hbD] at hz
                    · subst z; simp [haD] at hz
                    · subst z; exact hNoShareDE Q.r Q.hr Q.her hdz
                  have hNoShareEGD : ∀ z, D.color z = .reddish →
                      G.Adj Q.e z → ¬ G.Adj Q.g z := by
                    intro z hz hez hgz
                    rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                        Q.heaEdge Q.her
                        hab.ne.symm
                        (vertex_ne_of_color_eq hbD hrD (by decide))
                        (vertex_ne_of_color_eq haD hrD (by decide)) hez with q | q | q
                    · subst z; simp [hbD] at hz
                    · subst z; simp [haD] at hz
                    · subst z; exact hNoShareEG Q.r Q.hr Q.her hgz
                  have hgs : ¬ G.Adj Q.g s := by
                    intro hgs
                    exact hsh (hUniqueDG s hs hgs hds)
                  have hUniqueD : ∀ z, D.color z = .reddish →
                      G.Adj Q.g z → G.Adj d z → z = h := by
                    intro z hz hgz hdz
                    rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                        (vertex_ne_of_color_eq haD hxD (by decide))
                        (vertex_ne_of_color_eq haD hhD (by decide)) hxh hgz with
                      q | q | q
                    · subst z; simp [haD] at hz
                    · rcases neighbor_eq_of_degree_three
                          (degreeC (Or.inr hd)) hcd.symm hdh hds
                          (color_ne hc hh (by decide))
                          (color_ne hc hs (by decide)) hsh.symm hdz with r | r | r
                      · exact (vertex_ne_of_color_eq hxD hcD (by decide)
                          (q.symm.trans r)).elim
                      · exact (hxh (q.symm.trans r)).elim
                      · exact (hgs ((q.symm.trans r) ▸ hgx)).elim
                    · exact q
                  have finishNoRedD
                      (hNoRedI : ∀ z, G.Adj i z → D.color z ≠ .red) : False := by
                    by_cases hideg : vertexDegree G i = 3
                    · exact noResult (HasReachableNegativeReduction.after_flip C hflip
                        (lemma5_13_case4_exact_no_red_degree_three D hp
                          haD hbD hcD hdD QD hgf hdf hgdeg hNoShareDED hNoShareEGD
                          hxD hhD hsD hiD hgx hgh hxh hdh hds hsh hih hideg
                          hUniqueD hNoRedI))
                    · have hipos : 0 < vertexDegree G i := by
                        change 0 < (G.neighborSet i).ncard
                        rw [Set.ncard_pos]
                        exact ⟨h, hih⟩
                      have hile : vertexDegree G i ≤ 3 := D.subcubic i
                      have hilow : vertexDegree G i = 1 ∨ vertexDegree G i = 2 := by
                        omega
                      exact noResult (HasReachableNegativeReduction.after_flip C hflip
                        (lemma5_13_case4_exact_no_red_low_degree D hp
                          haD hbD hcD hdD QD hgf hdf hgdeg hNoShareDED hNoShareEGD
                          hxD hhD hsD hiD hgx hgh hxh hdh hds hsh hih hUniqueD
                          hNoRedI hilow))
                  by_cases hRedI : ∃ z, G.Adj i z ∧ D.color z = .red
                  · obtain ⟨m, him, hmD⟩ := hRedI
                    have hmCorrect := D.color_correct m
                    rw [hmD] at hmCorrect
                    obtain ⟨_, n, hnSide, hmn⟩ := hmCorrect
                    have hnCases := (D.mem_redSide_iff n).1 hnSide
                    have hnD : D.color n = .red := by
                      rcases hnCases with hnD | hnD
                      · exact hnD
                      · exact (D.reddish_not_adj_redSide hnD (Or.inl hmD) hmn.symm).elim
                    have hmc : m ≠ c := by
                      intro q; subst m
                      exact (D.bluish_not_adj_blueSide hiD (Or.inl hcD) him).elim
                    have hmd : m ≠ d := vertex_ne_of_color_eq hmD hdD (by decide)
                    have hiaD : ¬ G.Adj i a := hia
                    have hibD : ¬ G.Adj i b := hib
                    by_cases hBlueM : ∃ q, G.Adj m q ∧ D.color q = .blue
                    · obtain ⟨q, hmq, hqD⟩ := hBlueM
                      obtain ⟨qm, hqmD, hqqm⟩ := D.exists_blue_mate hqD
                      have hqc : q ≠ c := by
                        intro e; subst q
                        rcases neighbor_eq_of_degree_three
                            (degreeD (Or.inr hcD)) hbc.symm hcd Q.hcf
                            (vertex_ne_of_color_eq hbD hdD (by decide))
                            (vertex_ne_of_color_eq hbD hfD (by decide))
                            (vertex_ne_of_color_eq hdD hfD (by decide)) hmq.symm with
                          r | r | r
                        · subst m; exact hibD him
                        · exact hmd r
                        · exact (vertex_ne_of_color_eq hmD hfD (by decide)) r
                      have hqd : q ≠ d := by
                        intro e; subst q; exact hNoRedAtDD m hmq.symm hmD
                      exact noResult (HasReachableNegativeReduction.after_flip C hflip
                        (lemma5_13_case4_blue_neighbor_flip D hp haD hbD hcD hdD
                          hhD hsD hiD hdh hds hsh hih him hid hmD hnD hqD hqmD
                          hmn hmq hqqm hiaD hibD hci hqc hqd))
                    · have hNoBlueM : ∀ q, G.Adj m q → D.color q ≠ .blue := by
                        intro q hmq hq; exact hBlueM ⟨q, hmq, hq⟩
                      have hkD : D.color k = .blue :=
                        blue_of_flipped_red_endpoint C hflip hj hjk.symm
                          (degreeC (Or.inl hk))
                          (color_ne hj ho (by decide))
                      have hoD : D.color o = .red :=
                        red_of_flipped_blue_endpoint C hflip hom hoom
                          (degreeC (Or.inr ho))
                          (color_ne hom hk (by decide))
                      have hkom : ¬ G.Adj k om := by
                        intro hkom
                        have hntr : ContainsNegativeTailReducer C := by
                          apply containsNegativeA C hk ho hom hko hkom hoom
                          simp [hko.ne, hkom.ne, hoom.ne,
                            color_ne hk ho (by decide),
                            color_ne hk hom (by decide)]
                        exact noResult
                          (HasReachableNegativeReduction.of_current_ntr C hntr)
                      have homD : D.color om = .bluish := by
                        apply bluish_of_blue_loses_flipped_mate C hflip hom
                          hoom.symm (fun z => hkom z.symm)
                          (color_ne hom hk (by decide)) hoom.ne.symm
                      /- Prose names in Case (4.4.3.3.3.2): the present
                         `l, om, m, n` are respectively `m, n, o, p` there. -/
                      have hmo : ¬ G.Adj m o := by
                        intro hmoAdj
                        by_cases hkl : G.Adj k l
                        · have hlD : D.color l = .blue := by
                            apply blue_of_bluish_gains_flipped_red C hflip hl
                              hkl.symm hlk (color_ne hl ho (by decide))
                          have hgl : Q.g ≠ l := by
                            intro eq
                            subst l
                            have hnot : ¬ G.Adj Q.g j := by
                              apply not_adj_fourth_neighbor_of_degree_three hgdeg
                                Q.hag.symm hgx hgh
                              · exact color_ne ha hx (by decide)
                              · exact color_ne ha hh (by decide)
                              · exact hxh
                              · exact hja
                              · exact color_ne hj hx (by decide)
                              · exact color_ne hj hh (by decide)
                            exact hnot hjl.symm
                          have hel : Q.e ≠ l := by
                            intro eq
                            subst l
                            have hnot : ¬ G.Adj Q.e j := by
                              apply not_adj_fourth_neighbor_of_degree_three Q.hedeg
                                Q.hbe.symm Q.heaEdge Q.her
                              · exact hab.ne.symm
                              · exact color_ne hb Q.hr (by decide)
                              · exact color_ne ha Q.hr (by decide)
                              · exact hjb
                              · exact hja
                              · exact color_ne hj Q.hr (by decide)
                            exact hnot hjl.symm
                          have jFourth {w : V} (hwk : w ≠ k) (hwi : w ≠ i)
                              (hwl : w ≠ l) : ¬ G.Adj j w := by
                            apply not_adj_fourth_neighbor_of_subcubic C.subcubic
                              hjk hij.symm hjl
                            · exact color_ne hk hi (by decide)
                            · exact hlk.symm
                            · exact hli.symm
                            · exact hwk
                            · exact hwi
                            · exact hwl
                          have hjg : ¬ G.Adj j Q.g := jFourth
                            (vertex_ne_of_color_eq hgD hkD (by decide)) hig.symm hgl
                          have hje : ¬ G.Adj j Q.e := jFourth
                            (vertex_ne_of_color_eq heD hkD (by decide)) hie.symm hel
                          have hjc : ¬ G.Adj j c := jFourth
                            (color_ne hc hk (by decide)) hci
                            (color_ne hc hl (by decide))
                          have hjd : ¬ G.Adj j d := jFourth
                            (color_ne hd hk (by decide)) hid.symm
                            (color_ne hd hl (by decide))
                          have hFourth {w : V} (hwi : w ≠ i) (hwg : w ≠ Q.g)
                              (hwd : w ≠ d) : ¬ G.Adj h w := by
                            apply not_adj_fourth_neighbor_of_subcubic C.subcubic
                              hih.symm hgh.symm hdh.symm
                            · exact hig
                            · exact hid
                            · exact vertex_ne_of_color_eq hgD hdD (by decide)
                            · exact hwi
                            · exact hwg
                            · exact hwd
                          have hhk : ¬ G.Adj h k := hFourth
                            (color_ne hk hi (by decide))
                            (color_ne hk Q.hg (by decide))
                            (color_ne hk hd (by decide))
                          have hhl : ¬ G.Adj h l := hFourth hli
                            hgl.symm
                            (color_ne hl hd (by decide))
                          have hhe : ¬ G.Adj h Q.e := hFourth hie.symm Q.hge.symm
                            (color_ne Q.he hd (by decide))
                          have hhc : ¬ G.Adj h c := hFourth hci
                            (color_ne hc Q.hg (by decide)) hcd.ne
                          have hntr : ContainsNegativeTailReducer D := by
                            apply containsNegativeAj D hjD hhD haD hbD hkD hlD
                              hiD hgD heD hcD hdD hjk hjl hij.symm hih.symm
                              hgh.symm hdh.symm hab Q.hag Q.heaEdge.symm Q.hbe
                              hbc hkl hcd hjg hje hjc hjd hhk hhl hhe hhc
                            simp [hjk.ne, hjl.ne, hij.ne, hih.ne, hgh.ne, hdh.ne,
                              hab.ne, Q.hag.ne, Q.heaEdge.ne, Q.hbe.ne, hbc.ne,
                              hkl.ne, hcd.ne, hjg, hje, hjc, hjd, hhk, hhl, hhe,
                              hhc, hgl, hgl.symm, hel, hel.symm, hie, hig,
                              hid, hci, hci.symm, hja, hjb, hka, hka.symm,
                              hkb, hkb.symm, hli, hlk, Q.hge,
                              color_ne hj hi (by decide),
                              color_ne hj Q.hg (by decide),
                              color_ne hj Q.he (by decide),
                              color_ne hj hc (by decide),
                              color_ne hj hd (by decide),
                              color_ne hj hh (by decide), hab.ne,
                              color_ne hh ha (by decide),
                              color_ne hh hb (by decide),
                              color_ne hh hk (by decide),
                              color_ne hh hl (by decide),
                              color_ne hh hi (by decide),
                              color_ne hh Q.hg (by decide),
                              color_ne hh Q.he (by decide),
                              color_ne hh hc (by decide),
                              color_ne hh hd (by decide),
                              color_ne ha hl (by decide),
                              color_ne ha hi (by decide),
                              color_ne ha Q.he (by decide),
                              color_ne ha hc (by decide),
                              color_ne ha hd (by decide),
                              color_ne hb hl (by decide),
                              color_ne hb hi (by decide),
                              color_ne hb Q.hg (by decide),
                              color_ne hb hd (by decide),
                              color_ne hk hi (by decide),
                              color_ne hk Q.hg (by decide),
                              color_ne hk Q.he (by decide),
                              color_ne Q.hg hc (by decide),
                              color_ne Q.hg hd (by decide),
                              color_ne Q.he hc (by decide),
                              color_ne Q.he hd (by decide),
                              color_ne hk hc (by decide),
                              color_ne hk hd (by decide),
                              color_ne hl hc (by decide),
                              color_ne hl hd (by decide)]
                          exact noResult (HasReachableNegativeReduction.after_flip C hflip
                            (HasReachableNegativeReduction.of_current_ntr D hntr))
                        · have hlD : D.color l = .bluish := by
                            apply bluish_of_untouched_bluish C hflip hl
                              (fun z => hkl z.symm) hlk
                              (color_ne hl ho (by decide))
                          have hmj : ¬ G.Adj m j := fun hmj =>
                            D.reddish_not_adj_redSide hjD (Or.inl hmD) hmj.symm
                          have hmk : ¬ G.Adj m k := fun hmk => hNoBlueM k hmk hkD
                          have hio : ¬ G.Adj i o :=
                            C.bluish_not_adj_blueSide hi (Or.inl ho)
                          have hoj : ¬ G.Adj o j := fun z => hjo z.symm
                          have hoi : ¬ G.Adj o i := fun z => hio z.symm
                          have hjm : ¬ G.Adj j m := fun z => hmj z.symm
                          have hkm : ¬ G.Adj k m := fun z => hmk z.symm
                          have hki : ¬ G.Adj k i := fun z => hik z.symm
                          have hpent : FormsInducedPentagon G o m j k i := by
                            have hn : [o, m, j, k, i].Nodup := by
                              simp [hmoAdj.ne, hmoAdj.ne.symm, hko.ne, hko.ne.symm,
                                hjk.ne, hjk.ne.symm, hij.ne, hij.ne.symm,
                                him.ne, him.ne.symm, hjo, hoj, hio, hoi,
                                hmj, hjm, hmk, hkm, hik, hki,
                                vertex_ne_of_color_eq hoD hjD (by decide),
                                vertex_ne_of_color_eq hoD hkD (by decide),
                                vertex_ne_of_color_eq hoD hiD (by decide),
                                vertex_ne_of_color_eq hmD hjD (by decide),
                                vertex_ne_of_color_eq hmD hkD (by decide),
                                vertex_ne_of_color_eq hmD hiD (by decide),
                                vertex_ne_of_color_eq hjD hkD (by decide),
                                vertex_ne_of_color_eq hjD hiD (by decide),
                                vertex_ne_of_color_eq hkD hiD (by decide)]
                            refine ⟨?_, ?_⟩
                            · intro u v huv
                              apply hn.injective_get
                              fin_cases u <;> fin_cases v <;> exact huv
                            · intro u v
                              fin_cases u <;> fin_cases v <;>
                                simp [graphOfEdges, G.adj_comm, hmoAdj, hmoAdj.symm,
                                  hko, hko.symm, hjk, hjk.symm, hij, hij.symm,
                                  him, him.symm, hjo, hoj, hio, hoi, hmj, hjm,
                                  hmk, hkm, hik, hki]
                          have hoNoBlue : ∀ z, G.Adj o z → z ≠ k → z ≠ i →
                              D.color z ≠ .blue := by
                            intro z hoz hzk _ hz
                            rcases neighbor_eq_of_degree_three
                                (degreeD (Or.inl hoD))
                                hmoAdj.symm hko.symm hoom
                                (vertex_ne_of_color_eq hmD hkD (by decide))
                                (vertex_ne_of_color_eq hmD homD (by decide))
                                (vertex_ne_of_color_eq hkD homD (by decide))
                                hoz with r | r | r
                            · subst z; simp [hmD] at hz
                            · exact (hzk r).elim
                            · subst z; simp [homD] at hz
                          have hmNoBlue : ∀ z, G.Adj m z → z ≠ k → z ≠ i →
                              D.color z ≠ .blue := by
                            intro z hmz _ _ hz
                            exact hNoBlueM z hmz hz
                          have hjNoBlue : ∀ z, G.Adj j z → z ≠ k → z ≠ i →
                              D.color z ≠ .blue := by
                            intro z hjz hzk hzi hz
                            rcases neighbor_eq_of_degree_three
                                (degreeC (Or.inl hj))
                                hjk hij.symm hjl
                                (vertex_ne_of_color_eq hkD hiD (by decide))
                                hlk.symm hli.symm hjz with r | r | r
                            · exact (hzk r).elim
                            · exact (hzi r).elim
                            · subst z; simp [hlD] at hz
                          exact noResult (HasReachableNegativeReduction.after_flip C hflip
                            (lemma5_5 D hpent hoD hmD hjD hkD (Or.inr hiD)
                              hoNoBlue hmNoBlue hjNoBlue))
                      by_cases hBlueN : ∃ q, G.Adj n q ∧ D.color q = .blue
                      · obtain ⟨q, hnq, hqD⟩ := hBlueN
                        obtain ⟨qm, hqmD, hqqm⟩ := D.exists_blue_mate hqD
                        have hqc : q ≠ c := by
                          intro e; subst q
                          have hcn : ¬ G.Adj c n := by
                            apply not_adj_fourth_neighbor_of_degree_three
                              (degreeD (Or.inr hcD)) hbc.symm hcd Q.hcf
                            · exact vertex_ne_of_color_eq hbD hdD (by decide)
                            · exact vertex_ne_of_color_eq hbD hfD (by decide)
                            · exact vertex_ne_of_color_eq hdD hfD (by decide)
                            · intro e
                              subst n
                              rcases neighbor_eq_of_degree_three
                                  (degreeD (Or.inl hbD)) hab.symm hbc Q.hbe
                                  (vertex_ne_of_color_eq haD hcD (by decide))
                                  (vertex_ne_of_color_eq haD heD (by decide))
                                  (vertex_ne_of_color_eq hcD heD (by decide)) hmn.symm with
                                r | r | r
                              · subst m; exact hiaD him
                              · exact (vertex_ne_of_color_eq hmD hcD (by decide) r).elim
                              · exact (vertex_ne_of_color_eq hmD heD (by decide) r).elim
                            · exact vertex_ne_of_color_eq hnD hdD (by decide)
                            · exact vertex_ne_of_color_eq hnD hfD (by decide)
                          exact hcn hnq.symm
                        have hqd : q ≠ d := by
                          intro e; subst q; exact hNoRedAtDD n hnq.symm hnD
                        by_cases hin : G.Adj i n
                        · exact noResult (HasReachableNegativeReduction.after_flip C hflip
                            (lemma5_13_case4_blue_neighbor_flip D hp haD hbD hcD hdD
                              hhD hsD hiD hdh hds hsh hih hin hid hnD hmD hqD hqmD
                              hmn.symm hnq hqqm hiaD hibD hci hqc hqd))
                        · by_cases hqj : G.Adj q j
                          · have hkD : D.color k = .blue :=
                              blue_of_flipped_red_endpoint C hflip hj hjk.symm
                                (degreeC (Or.inl hk))
                                (color_ne hj ho (by decide))
                            have hoD : D.color o = .red :=
                              red_of_flipped_blue_endpoint C hflip hom hoom
                                (degreeC (Or.inr ho))
                                (color_ne hom hk (by decide))
                            have noCED (hceD : ContainsCutEnhancer D) : False :=
                              noResult (HasReachableNegativeReduction.after_flip C hflip
                                (HasReachableNegativeReduction.of_current_ce D hceD))
                            by_cases hkq : G.Adj k q
                            · obtain ⟨p, hmp, hpn, hpi⟩ :=
                                exists_third_neighbor_of_degree_three
                                  (degreeD (Or.inl hmD))
                                  (vertex_ne_of_color_eq hnD hiD (by decide))
                              have hpD : D.color p = .bluish := by
                                rcases D.other_neighbor_of_red_is_blueSide hmD hnD hmn
                                    hmp hpn with hp | hp
                                · exact (hNoBlueM p hmp hp).elim
                                · exact hp
                              have hmj : ¬ G.Adj m j := fun hmj =>
                                D.reddish_not_adj_redSide hjD (Or.inl hmD) hmj.symm
                              have hmk : ¬ G.Adj m k := fun hmk => hNoBlueM k hmk hkD
                              have hmq : ¬ G.Adj m q := fun hmq => hNoBlueM q hmq hqD
                              have hjp : ¬ G.Adj j p := by
                                apply not_adj_fourth_neighbor_of_degree_three
                                  (degreeC (Or.inl hj)) hjk hij.symm hqj.symm
                                · exact vertex_ne_of_color_eq hkD hiD (by decide)
                                · exact hkq.ne
                                · exact vertex_ne_of_color_eq hiD hqD (by decide)
                                · exact vertex_ne_of_color_eq hpD hkD (by decide)
                                · exact hpi
                                · exact vertex_ne_of_color_eq hpD hqD (by decide)
                              have hntr : ContainsNegativeTailReducer D := by
                                apply containsNegativeH D hmD hjD hpD hiD hkD hqD
                                  hmp him.symm hij.symm hjk hqj.symm hkq hmj hmk hmq hjp
                                simp [hmp.ne, him.ne, hij.ne, hjk.ne, hqj.ne, hkq.ne,
                                  vertex_ne_of_color_eq hmD hjD (by decide),
                                  vertex_ne_of_color_eq hmD hpD (by decide),
                                  vertex_ne_of_color_eq hmD hiD (by decide),
                                  vertex_ne_of_color_eq hmD hkD (by decide),
                                  vertex_ne_of_color_eq hmD hqD (by decide),
                                  vertex_ne_of_color_eq hjD hpD (by decide),
                                  vertex_ne_of_color_eq hjD hiD (by decide),
                                  vertex_ne_of_color_eq hjD hkD (by decide),
                                  vertex_ne_of_color_eq hjD hqD (by decide),
                                  vertex_ne_of_color_eq hpD hkD (by decide),
                                  vertex_ne_of_color_eq hpD hqD (by decide),
                                  vertex_ne_of_color_eq hiD hkD (by decide),
                                  vertex_ne_of_color_eq hiD hqD (by decide), hpi]
                              exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                (HasReachableNegativeReduction.of_current_ntr D hntr))
                            · by_cases hkn : G.Adj k n
                              · by_cases hkqV : k = q
                                · subst q
                                  have hno : n = o := by
                                    rcases neighbor_eq_of_degree_three
                                        (degreeD (Or.inr hkD))
                                        hjk.symm hko hqqm
                                        (vertex_ne_of_color_eq hjD hoD (by decide))
                                        (vertex_ne_of_color_eq hjD hqmD (by decide))
                                        (vertex_ne_of_color_eq hoD hqmD (by decide))
                                        hkn with r | r | r
                                    · exact (vertex_ne_of_color_eq hnD hjD
                                        (by decide) r).elim
                                    · exact r
                                    · exact (vertex_ne_of_color_eq hnD hqmD
                                        (by decide) r).elim
                                  subst n
                                  obtain ⟨w, hmw, hwo, hwi⟩ :=
                                    exists_third_neighbor_of_degree_three
                                      (degreeD (Or.inl hmD))
                                      (vertex_ne_of_color_eq hoD hiD (by decide))
                                  have hwD : D.color w = .bluish := by
                                    rcases D.other_neighbor_of_red_is_blueSide
                                        hmD hoD hmn hmw hwo with hw | hw
                                    · exact (hNoBlueM w hmw hw).elim
                                    · exact hw
                                  by_cases hkom : G.Adj k om
                                  · have hntr : ContainsNegativeTailReducer C := by
                                      apply containsNegativeA C hk ho hom hko hkom hoom
                                      simp [hko.ne, hkom.ne, hoom.ne,
                                        color_ne hk ho (by decide),
                                        color_ne hk hom (by decide)]
                                    exact noResult
                                      (HasReachableNegativeReduction.of_current_ntr C hntr)
                                  · have homD : D.color om = .bluish := by
                                      apply bluish_of_blue_loses_flipped_mate C hflip hom
                                        hoom.symm (fun z => hkom z.symm)
                                        (color_ne hom hk (by decide))
                                        hoom.ne.symm
                                    by_cases hkl : G.Adj k l
                                    · have hlD : D.color l = .blue := by
                                        apply blue_of_bluish_gains_flipped_red C hflip hl
                                          hkl.symm hlk
                                          (color_ne hl ho (by decide))
                                      have hmj : ¬ G.Adj m j :=
                                        fun hmj => D.reddish_not_adj_redSide hjD
                                          (Or.inl hmD) hmj.symm
                                      have hmk : ¬ G.Adj m k :=
                                        fun hmk => hNoBlueM k hmk hkD
                                      have hml : ¬ G.Adj m l :=
                                        fun hml => hNoBlueM l hml hlD
                                      have hjw : ¬ G.Adj j w := by
                                        apply not_adj_fourth_neighbor_of_degree_three
                                          (degreeC (Or.inl hj))
                                          hjk hij.symm hjl
                                        · exact vertex_ne_of_color_eq hkD hiD (by decide)
                                        · exact hkl.ne
                                        · exact vertex_ne_of_color_eq hiD hlD (by decide)
                                        · exact vertex_ne_of_color_eq hwD hkD (by decide)
                                        · exact hwi
                                        · exact vertex_ne_of_color_eq hwD hlD (by decide)
                                      have hntr : ContainsNegativeTailReducer D := by
                                        apply containsNegativeH D hmD hjD hwD hiD hkD hlD
                                          hmw him.symm hij.symm hjk hjl hkl
                                          hmj hmk hml hjw
                                        simp [hmw.ne, him.ne, hij.ne, hjk.ne, hjl.ne,
                                          hkl.ne, hwi, hwo,
                                          vertex_ne_of_color_eq hmD hjD (by decide),
                                          vertex_ne_of_color_eq hmD hwD (by decide),
                                          vertex_ne_of_color_eq hmD hiD (by decide),
                                          vertex_ne_of_color_eq hmD hkD (by decide),
                                          vertex_ne_of_color_eq hmD hlD (by decide),
                                          vertex_ne_of_color_eq hjD hwD (by decide),
                                          vertex_ne_of_color_eq hjD hiD (by decide),
                                          vertex_ne_of_color_eq hjD hkD (by decide),
                                          vertex_ne_of_color_eq hjD hlD (by decide),
                                          vertex_ne_of_color_eq hwD hkD (by decide),
                                          vertex_ne_of_color_eq hwD hlD (by decide),
                                          vertex_ne_of_color_eq hiD hkD (by decide),
                                          vertex_ne_of_color_eq hiD hlD (by decide)]
                                      exact noResult (HasReachableNegativeReduction.after_flip
                                        C hflip
                                        (HasReachableNegativeReduction.of_current_ntr D hntr))
                                    · have hlD : D.color l = .bluish := by
                                        apply bluish_of_untouched_bluish C hflip hl
                                          (fun z => hkl z.symm) hlk
                                          (color_ne hl ho (by decide))
                                      have hmj : ¬ G.Adj m j :=
                                        fun hmj => D.reddish_not_adj_redSide hjD
                                          (Or.inl hmD) hmj.symm
                                      have hmk : ¬ G.Adj m k :=
                                        fun hmk => hNoBlueM k hmk hkD
                                      have hoj : ¬ G.Adj o j := fun z => hjo z.symm
                                      have hoi : ¬ G.Adj o i := fun z => hin z.symm
                                      have hjm : ¬ G.Adj j m := fun z => hmj z.symm
                                      have hkm : ¬ G.Adj k m := fun z => hmk z.symm
                                      have hki : ¬ G.Adj k i := fun z => hik z.symm
                                      have hpent : FormsInducedPentagon G o m j k i := by
                                        have hn : [o, m, j, k, i].Nodup := by
                                          simp [hmn.ne, hko.ne, hjk.ne, hij.ne, him.ne,
                                            hmn.ne.symm, hko.ne.symm, hjk.ne.symm,
                                            hij.ne.symm, him.ne.symm,
                                            hjo, hoj, hin, hoi, hmj, hjm, hmk, hkm, hik, hki,
                                            vertex_ne_of_color_eq hoD hjD (by decide),
                                            vertex_ne_of_color_eq hoD hkD (by decide),
                                            vertex_ne_of_color_eq hoD hiD (by decide),
                                            vertex_ne_of_color_eq hmD hjD (by decide),
                                            vertex_ne_of_color_eq hmD hkD (by decide),
                                            vertex_ne_of_color_eq hmD hiD (by decide),
                                            vertex_ne_of_color_eq hjD hkD (by decide),
                                            vertex_ne_of_color_eq hjD hiD (by decide),
                                            vertex_ne_of_color_eq hkD hiD (by decide)]
                                        refine ⟨?_, ?_⟩
                                        · intro u v huv
                                          apply hn.injective_get
                                          fin_cases u <;> fin_cases v <;> exact huv
                                        · intro u v
                                          fin_cases u <;> fin_cases v <;>
                                            simp [graphOfEdges, G.adj_comm, hmn, hmn.symm,
                                              hko, hko.symm, hjk, hjk.symm, hij, hij.symm,
                                              him, him.symm, hjo, hoj, hin, hoi, hmj, hjm,
                                              hmk, hkm, hik, hki]
                                      have hoNoBlue : ∀ z, G.Adj o z → z ≠ k → z ≠ i →
                                          D.color z ≠ .blue := by
                                        intro z hoz hzk hzi hz
                                        rcases neighbor_eq_of_degree_three
                                            (degreeD (Or.inl hoD))
                                            hmn.symm hko.symm hoom
                                            (vertex_ne_of_color_eq hmD hkD (by decide))
                                            (vertex_ne_of_color_eq hmD homD (by decide))
                                            (vertex_ne_of_color_eq hkD homD (by decide))
                                            hoz with r | r | r
                                        · subst z; simp [hmD] at hz
                                        · exact (hzk r).elim
                                        · subst z; simp [homD] at hz
                                      have hmNoBlue : ∀ z, G.Adj m z → z ≠ k → z ≠ i →
                                          D.color z ≠ .blue := by
                                        intro z hmz _ _ hz
                                        exact hNoBlueM z hmz hz
                                      have hjNoBlue : ∀ z, G.Adj j z → z ≠ k → z ≠ i →
                                          D.color z ≠ .blue := by
                                        intro z hjz hzk hzi hz
                                        rcases neighbor_eq_of_degree_three
                                            (degreeC (Or.inl hj))
                                            hjk hij.symm hjl
                                            (vertex_ne_of_color_eq hkD hiD (by decide))
                                            hlk.symm hli.symm hjz with r | r | r
                                        · exact (hzk r).elim
                                        · exact (hzi r).elim
                                        · subst z; simp [hlD] at hz
                                      exact noResult
                                        (HasReachableNegativeReduction.after_flip C hflip
                                          (lemma5_5 D hpent hoD hmD hjD hkD (Or.inr hiD)
                                            hoNoBlue hmNoBlue hjNoBlue))
                                · exact noCED (containsCutEnhancerA_of D hnD hkD hqD
                                    hkn.symm hnq hkqV hkq)
                              · by_cases hoq : G.Adj o q
                                · have hkqV : k ≠ q := by
                                    intro e; subst q
                                    exact hkn hnq.symm
                                  exact noCED (containsCutEnhancerA_of D hoD hkD hqD
                                    hko.symm hoq hkqV hkq)
                                · have hmoV : m ≠ o := by
                                    intro e
                                    subst o
                                    exact hNoBlueM k hko.symm hkD
                                  have hon : ¬ G.Adj o n := by
                                    intro hon
                                    exact (D.redSide_not_adj_second_neighbor
                                      (by simp [hnD]) (by simp [hmD]) (by simp [hoD])
                                      hmn.symm hmoV) hon.symm
                                  have hjn : ¬ G.Adj j n :=
                                    D.reddish_not_adj_redSide hjD (Or.inl hnD)
                                  exact noCED (containsCutEnhancerB_of D hjD hkD hoD hqD hnD
                                    hjk hqj.symm hko hnq.symm hjo hjn hkq hkn hoq hon)
                          · rcases exists_flipAt_or_cutEnhancer D hnD hqD hmD hqmD
                                (degreeD (Or.inl hnD)) (degreeD (Or.inr hqD))
                                hmn.symm hnq hqqm with ⟨N, hflip2⟩ | hce2
                            · let E := N.toColoring
                              have degreeE {v : V}
                                  (hv : E.color v = .red ∨ E.color v = .blue) :
                                  vertexDegree G v = 3 := by
                                rcases lemma3_6_negative E hv with hdegree | hntr | hce
                                · exact hdegree
                                · exact (noResult
                                    (HasReachableNegativeReduction.after_flip C hflip
                                      (HasReachableNegativeReduction.after_flip D hflip2
                                        (.of_current_ntr E hntr)))).elim
                                · exact (noResult
                                    (HasReachableNegativeReduction.after_flip C hflip
                                      (HasReachableNegativeReduction.after_flip D hflip2
                                        (.of_current_ce E hce)))).elim
                              have hna : n ≠ a := by
                                intro e; subst n
                                have hmb : m ≠ b := by
                                  intro r; subst m; exact hibD him
                                exact (D.redSide_not_adj_second_neighbor
                                  (by simp [haD]) (by simp [hbD]) (by simp [hmD])
                                  hab hmb.symm) hmn.symm
                              have hnb : n ≠ b := by
                                intro e; subst n
                                have hma : m ≠ a := by
                                  intro r; subst m; exact hiaD him
                                exact (D.redSide_not_adj_second_neighbor
                                  (by simp [hbD]) (by simp [haD]) (by simp [hmD])
                                  hab.symm hma.symm) hmn.symm
                              have haE : E.color a = .red :=
                                red_of_untouched_red_edge D hflip2
                                  (by simp [haD]) (by simp [hbD]) hab
                                  hna.symm (vertex_ne_of_color_eq haD hqD (by decide))
                                  hnb.symm (vertex_ne_of_color_eq hbD hqD (by decide))
                              have hbE : E.color b = .red :=
                                red_of_untouched_red_edge D hflip2
                                  (by simp [hbD]) (by simp [haD]) hab.symm
                                  hnb.symm (vertex_ne_of_color_eq hbD hqD (by decide))
                                  hna.symm (vertex_ne_of_color_eq haD hqD (by decide))
                              have hcE : E.color c = .blue :=
                                blue_of_untouched_blue_edge D hflip2
                                  (by simp [hcD]) (by simp [hdD]) hcd
                                  (vertex_ne_of_color_eq hcD hnD (by decide)) hqc.symm
                                  (vertex_ne_of_color_eq hdD hnD (by decide)) hqd.symm
                              have hdE : E.color d = .blue :=
                                blue_of_untouched_blue_edge D hflip2
                                  (by simp [hdD]) (by simp [hcD]) hcd.symm
                                  (vertex_ne_of_color_eq hdD hnD (by decide)) hqd.symm
                                  (vertex_ne_of_color_eq hcD hnD (by decide)) hqc.symm
                              have hiE : E.color i = .bluish :=
                                bluish_of_untouched_bluish D hflip2 hiD hin
                                  (vertex_ne_of_color_eq hiD hnD (by decide))
                                  (vertex_ne_of_color_eq hiD hqD (by decide))
                              have hmq : ¬ G.Adj m q := fun z => hNoBlueM q z hqD
                              have hmE : E.color m = .reddish :=
                                reddish_of_red_loses_flipped_mate D hflip2 hmD hmn hmq
                                  hmn.ne (vertex_ne_of_color_eq hmD hqD (by decide))
                              have hjn : ¬ G.Adj j n :=
                                D.reddish_not_adj_redSide hjD (Or.inl hnD)
                              have hjE : E.color j = .reddish :=
                                reddish_of_untouched_reddish D hflip2 hjD (fun z => hqj z.symm)
                                  (vertex_ne_of_color_eq hjD hnD (by decide))
                                  (vertex_ne_of_color_eq hjD hqD (by decide))
                              by_cases hhq : G.Adj h q
                              · have hhE : E.color h = .red :=
                                  red_of_reddish_gains_flipped_blue D hflip2 hhD hhq
                                    (vertex_ne_of_color_eq hhD hnD (by decide))
                                    (vertex_ne_of_color_eq hhD hqD (by decide))
                                have hqE : E.color q = .red :=
                                  red_of_flipped_blue_endpoint D hflip2 hqmD hqqm
                                    (degreeD (Or.inr hqD))
                                    (vertex_ne_of_color_eq hqmD hnD (by decide))
                                have hn6 : [a,b,c,d,h,q].Nodup := by
                                  simp [hab.ne, hbc.ne, hcd.ne, hdh.ne, hhq.ne,
                                    vertex_ne_of_color_eq haE hcE (by decide),
                                    vertex_ne_of_color_eq haE hdE (by decide),
                                    vertex_ne_of_color_eq hbE hdE (by decide),
                                    vertex_ne_of_color_eq hcE hhE (by decide),
                                    color_ne ha hh (by decide),
                                    color_ne hb hh (by decide),
                                    vertex_ne_of_color_eq haD hqD (by decide),
                                    vertex_ne_of_color_eq hbD hqD (by decide), hqc.symm, hqd.symm]
                                have hsub : FormsNegativePath6Subgraph G a b c d h q := by
                                  refine ⟨?_, ?_⟩
                                  · have hv : (![a,b,c,d,h,q] : Fin 6 → V) =
                                        [a,b,c,d,h,q].get := by funext z; fin_cases z <;> rfl
                                    rw [hv]; exact hn6.injective_get
                                  · intro u v huv
                                    fin_cases u <;> fin_cases v <;>
                                      simp [graphOfEdges, G.adj_comm, hab, hbc, hcd,
                                        hdh, hhq] at huv ⊢
                                exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                  (HasReachableNegativeReduction.after_flip D hflip2
                                    (lemma5_12_inline E hsub haE hbE hcE hdE hhE hqE)))
                              · by_cases hsq : G.Adj s q
                                · have hsE : E.color s = .red :=
                                    red_of_reddish_gains_flipped_blue D hflip2 hsD hsq
                                      (vertex_ne_of_color_eq hsD hnD (by decide))
                                      (vertex_ne_of_color_eq hsD hqD (by decide))
                                  have hqE : E.color q = .red :=
                                    red_of_flipped_blue_endpoint D hflip2 hqmD hqqm
                                      (degreeD (Or.inr hqD))
                                      (vertex_ne_of_color_eq hqmD hnD (by decide))
                                  have hn6 : [a,b,c,d,s,q].Nodup := by
                                    simp [hab.ne, hbc.ne, hcd.ne, hds.ne, hsq.ne,
                                      vertex_ne_of_color_eq haE hcE (by decide),
                                      vertex_ne_of_color_eq haE hdE (by decide),
                                      vertex_ne_of_color_eq hbE hdE (by decide),
                                      vertex_ne_of_color_eq hcE hsE (by decide),
                                      color_ne ha hs (by decide),
                                      color_ne hb hs (by decide),
                                      vertex_ne_of_color_eq haD hqD (by decide),
                                      vertex_ne_of_color_eq hbD hqD (by decide), hqc.symm, hqd.symm]
                                  have hsub : FormsNegativePath6Subgraph G a b c d s q := by
                                    refine ⟨?_, ?_⟩
                                    · have hv : (![a,b,c,d,s,q] : Fin 6 → V) =
                                          [a,b,c,d,s,q].get := by funext z; fin_cases z <;> rfl
                                      rw [hv]; exact hn6.injective_get
                                    · intro u v huv
                                      fin_cases u <;> fin_cases v <;>
                                        simp [graphOfEdges, G.adj_comm, hab, hbc, hcd,
                                          hds, hsq] at huv ⊢
                                  exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                    (HasReachableNegativeReduction.after_flip D hflip2
                                      (lemma5_12_inline E hsub haE hbE hcE hdE hsE hqE)))
                                · have hhE : E.color h = .reddish :=
                                    reddish_of_untouched_reddish D hflip2 hhD hhq
                                      (vertex_ne_of_color_eq hhD hnD (by decide))
                                      (vertex_ne_of_color_eq hhD hqD (by decide))
                                  have hsE : E.color s = .reddish :=
                                    reddish_of_untouched_reddish D hflip2 hsD hsq
                                      (vertex_ne_of_color_eq hsD hnD (by decide))
                                      (vertex_ne_of_color_eq hsD hqD (by decide))
                                  have hcn : ¬ G.Adj c n := by
                                    apply not_adj_fourth_neighbor_of_degree_three
                                      (degreeD (Or.inr hcD)) hbc.symm hcd Q.hcf
                                    · exact vertex_ne_of_color_eq hbD hdD (by decide)
                                    · exact vertex_ne_of_color_eq hbD hfD (by decide)
                                    · exact vertex_ne_of_color_eq hdD hfD (by decide)
                                    · exact hnb
                                    · exact vertex_ne_of_color_eq hnD hdD (by decide)
                                    · exact vertex_ne_of_color_eq hnD hfD (by decide)
                                  have hbq : ¬ G.Adj b q := by
                                    apply not_adj_fourth_neighbor_of_degree_three
                                      (degreeD (Or.inl hbD)) hab.symm hbc Q.hbe
                                    · exact vertex_ne_of_color_eq haD hcD (by decide)
                                    · exact vertex_ne_of_color_eq haD heD (by decide)
                                    · exact vertex_ne_of_color_eq hcD heD (by decide)
                                    · exact vertex_ne_of_color_eq hqD haD (by decide)
                                    · exact hqc
                                    · exact vertex_ne_of_color_eq hqD heD (by decide)
                                  have hcq : ¬ G.Adj c q :=
                                    D.blueSide_not_adj_second_neighbor (by simp [hcD])
                                      (by simp [hdD]) (by simp [hqD]) hcd hqd.symm
                                  have hbn : ¬ G.Adj b n := by
                                    apply D.redSide_not_adj_second_neighbor
                                      (by simp [hbD]) (by simp [haD]) (by simp [hnD])
                                      hab.symm hna.symm
                                  by_cases hCommonC2 : ∃ z, G.Adj c z ∧ G.Adj q z
                                  · obtain ⟨z, hcz, hqz⟩ := hCommonC2
                                    have hzf : z = Q.f := by
                                      rcases neighbor_eq_of_degree_three
                                          (degreeD (Or.inr hcD)) hbc.symm hcd Q.hcf
                                          (vertex_ne_of_color_eq hbD hdD (by decide))
                                          (vertex_ne_of_color_eq hbD hfD (by decide))
                                          (vertex_ne_of_color_eq hdD hfD (by decide)) hcz with
                                        rfl | rfl | rfl
                                      · exact (hbq hqz.symm).elim
                                      · exact (D.blueSide_not_adj_second_neighbor
                                          (by simp [hdD]) (by simp [hcD]) (by simp [hqD])
                                          hcd.symm hqc.symm hqz.symm).elim
                                      · rfl
                                    subst z
                                    exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                      (HasReachableNegativeReduction.of_current_ce D
                                        (containsCutEnhancerB_of D hfD hcD hbD hqD hnD
                                          Q.hcf.symm hqz.symm hbc.symm hnq.symm
                                          (D.reddish_not_adj_redSide hfD (Or.inl hbD))
                                          (D.reddish_not_adj_redSide hfD (Or.inl hnD))
                                          hcq hcn hbq hbn)))
                                  · have hfq : ¬ G.Adj Q.f q := by
                                      intro hfq; exact hCommonC2 ⟨Q.f, Q.hcf, hfq.symm⟩
                                    have hen : ¬ G.Adj Q.e n := by
                                      intro hen
                                      rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                                          Q.heaEdge Q.her
                                          hab.ne.symm
                                          (vertex_ne_of_color_eq hbD hrD (by decide))
                                          (vertex_ne_of_color_eq haD hrD (by decide)) hen with
                                        r | r | r
                                      · exact hnb r
                                      · exact hna r
                                      · exact (vertex_ne_of_color_eq hnD hrD (by decide)) r
                                    by_cases hCommonE2 : ∃ z, G.Adj Q.e z ∧ G.Adj q z
                                    · obtain ⟨z, hez, hqz⟩ := hCommonE2
                                      have haq : ¬ G.Adj a q := by
                                        apply not_adj_fourth_neighbor_of_degree_three
                                          (degreeD (Or.inl haD)) hab
                                            Q.heaEdge.symm Q.hag
                                        · exact vertex_ne_of_color_eq hbD heD (by decide)
                                        · exact vertex_ne_of_color_eq hbD hgD (by decide)
                                        · exact Q.hge.symm
                                        · exact vertex_ne_of_color_eq hqD hbD (by decide)
                                        · exact vertex_ne_of_color_eq hqD heD (by decide)
                                        · exact vertex_ne_of_color_eq hqD hgD (by decide)
                                      have hzr : z = Q.r := by
                                        rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                                            Q.heaEdge Q.her
                                            hab.ne.symm
                                            (vertex_ne_of_color_eq hbD hrD (by decide))
                                            (vertex_ne_of_color_eq haD hrD (by decide)) hez with
                                          r | r | r
                                        · exact (hbq (r ▸ hqz.symm)).elim
                                        · exact (haq (r ▸ hqz.symm)).elim
                                        · exact r
                                      subst z
                                      have heE : E.color Q.e = .bluish :=
                                        bluish_of_untouched_bluish D hflip2 heD hen
                                          (vertex_ne_of_color_eq heD hnD (by decide))
                                          (vertex_ne_of_color_eq heD hqD (by decide))
                                      have hfE : E.color Q.f = .reddish :=
                                        reddish_of_untouched_reddish D hflip2 hfD hfq
                                          (vertex_ne_of_color_eq hfD hnD (by decide))
                                          (vertex_ne_of_color_eq hfD hqD (by decide))
                                      have hrE : E.color Q.r = .red :=
                                        red_of_reddish_gains_flipped_blue D hflip2 hrD hqz.symm
                                          (vertex_ne_of_color_eq hrD hnD (by decide))
                                          (vertex_ne_of_color_eq hrD hqD (by decide))
                                      let T : Lemma5_13ThirdNeighborConfiguration E a b c d := {
                                        e := Q.e, f := Q.f, he := heE, hf := hfE,
                                        hbe := Q.hbe, hcf := Q.hcf, hea := Q.hea,
                                        hec := Q.hec, hfb := Q.hfb, hfd := Q.hfd,
                                        hedeg := Q.hedeg, hfdeg := Q.hfdeg }
                                      obtain ⟨R, hRT⟩ :=
                                        lemma5_13_case2_setup E T hrE Q.her Q.hra Q.hrb
                                      rcases lemma5_13_case2_flip_path E hp haE hbE hcE hdE R with
                                        hresult | hpath3
                                      · exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                          (HasReachableNegativeReduction.after_flip D hflip2 hresult))
                                      · obtain ⟨P⟩ := hpath3
                                        exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                          (HasReachableNegativeReduction.after_flip D hflip2 P.reduces))
                                    · have hrq : ¬ G.Adj Q.r q := by
                                        intro hrq; exact hCommonE2 ⟨Q.r, Q.her, hrq.symm⟩
                                      have hgn : ¬ G.Adj Q.g n := by
                                        intro hgn
                                        rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                                            (vertex_ne_of_color_eq haD hxD (by decide))
                                            (vertex_ne_of_color_eq haD hhD (by decide)) hxh hgn with
                                          r | r | r
                                        · exact hna r
                                        · exact (vertex_ne_of_color_eq hnD hxD (by decide)) r
                                        · exact (vertex_ne_of_color_eq hnD hhD (by decide)) r
                                      have heE : E.color Q.e = .bluish :=
                                        bluish_of_untouched_bluish D hflip2 heD hen
                                          (vertex_ne_of_color_eq heD hnD (by decide))
                                          (vertex_ne_of_color_eq heD hqD (by decide))
                                      have hfE : E.color Q.f = .reddish :=
                                        reddish_of_untouched_reddish D hflip2 hfD hfq
                                          (vertex_ne_of_color_eq hfD hnD (by decide))
                                          (vertex_ne_of_color_eq hfD hqD (by decide))
                                      have hgE : E.color Q.g = .bluish :=
                                        bluish_of_untouched_bluish D hflip2 hgD hgn
                                          (vertex_ne_of_color_eq hgD hnD (by decide))
                                          (vertex_ne_of_color_eq hgD hqD (by decide))
                                      have hrE : E.color Q.r = .reddish :=
                                        reddish_of_untouched_reddish D hflip2 hrD hrq
                                          (vertex_ne_of_color_eq hrD hnD (by decide))
                                          (vertex_ne_of_color_eq hrD hqD (by decide))
                                      let QE : Lemma5_13Case4Configuration E a b c d := {
                                        e := Q.e, f := Q.f, he := heE, hf := hfE,
                                        hbe := Q.hbe, hcf := Q.hcf, hea := Q.hea,
                                        hec := Q.hec, hfb := Q.hfb, hfd := Q.hfd,
                                        hedeg := Q.hedeg, hfdeg := Q.hfdeg,
                                        heaEdge := Q.heaEdge, hef := Q.hef,
                                        g := Q.g, hg := hgE, hag := Q.hag,
                                        hgb := Q.hgb, hge := Q.hge,
                                        r := Q.r, hr := hrE, her := Q.her,
                                        hra := Q.hra, hrb := Q.hrb }
                                      by_cases hCommonG2 : ∃ z, G.Adj Q.g z ∧ G.Adj q z
                                      · obtain ⟨z, hgz, hqz⟩ := hCommonG2
                                        have haq : ¬ G.Adj a q := by
                                          apply not_adj_fourth_neighbor_of_degree_three
                                            (degreeD (Or.inl haD)) hab
                                              Q.heaEdge.symm Q.hag
                                          · exact vertex_ne_of_color_eq hbD heD (by decide)
                                          · exact vertex_ne_of_color_eq hbD hgD (by decide)
                                          · exact Q.hge.symm
                                          · exact vertex_ne_of_color_eq hqD hbD (by decide)
                                          · exact vertex_ne_of_color_eq hqD heD (by decide)
                                          · exact vertex_ne_of_color_eq hqD hgD (by decide)
                                        have hzx : z = x := by
                                          rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                                              (vertex_ne_of_color_eq haD hxD (by decide))
                                              (vertex_ne_of_color_eq haD hhD (by decide)) hxh hgz with
                                            r | r | r
                                          · exact (haq (r ▸ hqz.symm)).elim
                                          · exact r
                                          · exact (hhq (r ▸ hqz.symm)).elim
                                        subst z
                                        have hxE : E.color x = .red :=
                                          red_of_reddish_gains_flipped_blue D hflip2 hxD hqz.symm
                                            (vertex_ne_of_color_eq hxD hnD (by decide))
                                            (vertex_ne_of_color_eq hxD hqD (by decide))
                                        have hNoRedAtDE : ∀ z, G.Adj d z → E.color z ≠ .red := by
                                          intro z hdz hz
                                          rcases neighbor_eq_of_degree_three
                                              (degreeD (Or.inr hdD)) hcd.symm hdh hds
                                              (vertex_ne_of_color_eq hcD hhD (by decide))
                                              (vertex_ne_of_color_eq hcD hsD (by decide)) hsh.symm hdz with
                                            r | r | r
                                          · subst z; simp [hcE] at hz
                                          · subst z; simp [hhE] at hz
                                          · subst z; simp [hsE] at hz
                                        exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                          (HasReachableNegativeReduction.after_flip D hflip2
                                            (lemma5_13_case4_red_neighbor E hp haE hbE hcE hdE
                                              hNoRedAtDE QE hxE hgx
                                              (color_ne hx ha (by decide)))))
                                      · have hxq : ¬ G.Adj x q := by
                                          intro hxq; exact hCommonG2 ⟨x, hgx, hxq.symm⟩
                                        have hxE : E.color x = .reddish :=
                                          reddish_of_untouched_reddish D hflip2 hxD hxq
                                            (vertex_ne_of_color_eq hxD hnD (by decide))
                                            (vertex_ne_of_color_eq hxD hqD (by decide))
                                        -- The displayed neighbors `h,j,m` exhaust `i`;
                                        -- after the second flip all three are reddish.
                                        have hijm : j ≠ m :=
                                          vertex_ne_of_color_eq hjD hmD (by decide)
                                        have hhm : h ≠ m :=
                                          vertex_ne_of_color_eq hhD hmD (by decide)
                                        have hhj : h ≠ j := color_ne hh hj (by decide)
                                        have hilower : 3 ≤ vertexDegree G i := by
                                          have hsub : ({h,j,m} : Set V) ⊆ G.neighborSet i := by
                                            intro z hz
                                            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
                                            rcases hz with rfl | rfl | rfl
                                            · exact hih
                                            · exact hij
                                            · exact him
                                          unfold vertexDegree
                                          have hncard := Set.ncard_le_ncard hsub
                                          simpa [hhj, hhm, hijm] using hncard
                                        have hideg3 : vertexDegree G i = 3 := by
                                          have hiupper := E.subcubic i
                                          omega
                                        have hNoRedI : ∀ z, G.Adj i z → E.color z ≠ .red := by
                                          intro z hiz hz
                                          rcases neighbor_eq_of_degree_three hideg3 hih hij him
                                              hhj hhm hijm hiz with r | r | r
                                          · subst z; simp [hhE] at hz
                                          · subst z; simp [hjE] at hz
                                          · subst z; simp [hmE] at hz
                                        have hNoShareDEE : ∀ z, E.color z = .reddish →
                                            G.Adj Q.e z → ¬ G.Adj d z := by
                                          intro z hz hez hdz
                                          rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                                              Q.heaEdge Q.her
                                              hab.ne.symm
                                              (vertex_ne_of_color_eq hbE hrE (by decide))
                                              (vertex_ne_of_color_eq haE hrE (by decide)) hez with r | r | r
                                          · subst z; simp [hbE] at hz
                                          · subst z; simp [haE] at hz
                                          · subst z; exact hNoShareDED Q.r hrD Q.her hdz
                                        have hNoShareEGE : ∀ z, E.color z = .reddish →
                                            G.Adj Q.e z → ¬ G.Adj Q.g z := by
                                          intro z hz hez hgz
                                          rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm
                                              Q.heaEdge Q.her
                                              hab.ne.symm
                                              (vertex_ne_of_color_eq hbE hrE (by decide))
                                              (vertex_ne_of_color_eq haE hrE (by decide)) hez with r | r | r
                                          · subst z; simp [hbE] at hz
                                          · subst z; simp [haE] at hz
                                          · subst z; exact hNoShareEGD Q.r hrD Q.her hgz
                                        have hUniqueE : ∀ z, E.color z = .reddish →
                                            G.Adj Q.g z → G.Adj d z → z = h := by
                                          intro z hz hgz hdz
                                          rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
                                              (vertex_ne_of_color_eq haE hxE (by decide))
                                              (vertex_ne_of_color_eq haE hhE (by decide)) hxh hgz with
                                            r | r | r
                                          · subst z; simp [haE] at hz
                                          · rcases neighbor_eq_of_degree_three
                                                (degreeE (Or.inr hdE)) hcd.symm hdh hds
                                                (vertex_ne_of_color_eq hcE hhE (by decide))
                                                (vertex_ne_of_color_eq hcE hsE (by decide)) hsh.symm hdz with
                                              t | t | t
                                            · exact (vertex_ne_of_color_eq hxE hcE (by decide)
                                                (r.symm.trans t)).elim
                                            · exact (hxh (r.symm.trans t)).elim
                                            · exact (hgs ((r.symm.trans t) ▸ hgx)).elim
                                          · exact r
                                        exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                          (HasReachableNegativeReduction.after_flip D hflip2
                                            (lemma5_13_case4_exact_no_red_degree_three E hp
                                              haE hbE hcE hdE QE hgf hdf hgdeg
                                              hNoShareDEE hNoShareEGE hxE hhE hsE hiE
                                              hgx hgh hxh hdh hds hsh hih hideg3 hUniqueE hNoRedI)))
                            · exact noResult (HasReachableNegativeReduction.after_flip C hflip
                                (HasReachableNegativeReduction.of_current_ce D hce2))
                      · have hNoBlueN : ∀ q, G.Adj n q → D.color q ≠ .blue := by
                          intro q hnq hq; exact hBlueN ⟨q, hnq, hq⟩
                        have hmOther : ∀ z, G.Adj m z → z ≠ n →
                            D.color z = .bluish := by
                          intro z hmz hzn
                          rcases D.other_neighbor_of_red_is_blueSide hmD hnD hmn hmz hzn with
                            hz | hz
                          · exact (hNoBlueM z hmz hz).elim
                          · exact hz
                        have hnOther : ∀ z, G.Adj n z → z ≠ m →
                            D.color z = .bluish := by
                          intro z hnz hzm
                          rcases D.other_neighbor_of_red_is_blueSide hnD hmD hmn.symm hnz hzm with
                            hz | hz
                          · exact (hNoBlueN z hnz hz).elim
                          · exact hz
                        exact noResult (HasReachableNegativeReduction.after_flip C hflip
                          (lemma5_4 D hmD hnD hmn hmOther hnOther))
                  · exact finishNoRedD (by
                      intro z hiz hz; exact hRedI ⟨z, hiz, hz⟩)
      · exact (noCE hce).elim

end Subcubic
