import Subcubic.Lemma5_13.Case4ExactBluishRed
import Subcubic.Lemma5_13.Case4DisjointMeetsF

/-! Assembly of Lemma 5.13, Case (4). -/

namespace Subcubic

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_core
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hTerminal : ∀ {x y h s : V},
      C.color x = .reddish → C.color y = .reddish →
      C.color h = .reddish → C.color s = .reddish →
      G.Adj Q.g x → G.Adj Q.g y → x ≠ a → y ≠ a → x ≠ y →
      G.Adj d h → G.Adj d s → h ≠ c → s ≠ c → h ≠ s →
      vertexDegree G Q.g = 3 → G.Adj d Q.f →
      (∀ z, C.color z = .reddish → G.Adj Q.e z → ¬ G.Adj d z) →
      (∀ z, C.color z = .reddish → G.Adj Q.e z → ¬ G.Adj Q.g z) →
      ¬ G.Adj Q.g Q.f →
      ¬ G.Adj Q.g h → ¬ G.Adj Q.g s →
      HasReachableNegativeReduction C)
    (hOutsideF : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ d →
      C.color z = .bluish) :
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
  by_cases hShareDE : ∃ z, C.color z = .reddish ∧
      G.Adj Q.e z ∧ G.Adj d z
  · obtain ⟨z, hz, hez, hdz⟩ := hShareDE
    exact lemma5_13_case4_shared_de C hpath ha hb hc hd hNoRedAtD Q
      hz hez hdz
  have hNoShareDE : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj d z := by
    intro z hz hez hdz
    exact hShareDE ⟨z, hz, hez, hdz⟩
  by_cases hRedG : ∃ z, G.Adj Q.g z ∧ C.color z = .red ∧ z ≠ a
  · obtain ⟨z, hgz, hz, hza⟩ := hRedG
    exact lemma5_13_case4_red_neighbor C hpath ha hb hc hd hNoRedAtD Q
      hz hgz hza
  have hNoOtherRedG : ∀ z, G.Adj Q.g z → C.color z = .red → z = a := by
    intro z hgz hz
    by_contra hza
    exact hRedG ⟨z, hgz, hz, hza⟩
  by_cases hgf : G.Adj Q.g Q.f
  · exact lemma5_13_case4_g_meets_f C hpath ha hb hc hd hNoBlueAtA Q
      hOutsideF hgf
  have hgf' : ¬ G.Adj Q.g Q.f := hgf
  by_cases hShareEG : ∃ z, C.color z = .reddish ∧
      G.Adj Q.g z ∧ G.Adj Q.e z
  · obtain ⟨z, hz, hgz, hez⟩ := hShareEG
    exact lemma5_13_case4_shared_eg C hpath ha hb hc hd Q hgf'
      hNoOtherRedG hz hgz hez
  have hNoShareEG : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj Q.g z := by
    intro z hz hez hgz
    exact hShareEG ⟨z, hz, hgz, hez⟩
  by_cases hgdeg : vertexDegree G Q.g = 3
  · dsimp [FormsInducedPath4] at hpath
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
    obtain ⟨x, y, hgx, hgy, hxa, hya, hxy⟩ :=
      exists_two_other_neighbors_of_degree_three hgdeg Q.hag.symm
    have reddishG {z : V} (hgz : G.Adj Q.g z) (hza : z ≠ a) :
        C.color z = .reddish := by
      cases hz : C.color z with
      | red => exact (hza (hNoOtherRedG z hgz hz)).elim
      | reddish => rfl
      | blue => exact (C.bluish_not_adj_blueSide Q.hg (Or.inl hz) hgz).elim
      | bluish => exact (C.bluish_not_adj_blueSide Q.hg (Or.inr hz) hgz).elim
    have hx := reddishG hgx hxa
    have hy := reddishG hgy hya
    obtain ⟨h, s, hdh, hds, hhc, hsc, hhs⟩ :=
      exists_two_other_neighbors_of_degree_three
        (degreeC (Or.inr hd)) hcd.symm
    have reddishD {z : V} (hdz : G.Adj d z) (hzc : z ≠ c) :
        C.color z = .reddish := by
      cases hz : C.color z with
      | red => exact (hNoRedAtD z hdz hz).elim
      | reddish => rfl
      | blue =>
          exact (C.blueSide_not_adj_second_neighbor
            (by simp [hd]) (by simp [hc]) (by simp [hz]) hcd.symm
            hzc.symm) hdz |>.elim
      | bluish =>
          exact (C.blueSide_not_adj_second_neighbor
            (by simp [hd]) (by simp [hc]) (by simp [hz]) hcd.symm
            hzc.symm) hdz |>.elim
    have hh := reddishD hdh hhc
    have hs := reddishD hds hsc
    by_cases hdf : G.Adj d Q.f
    · have sharedMeetsF {z : V} (hz : C.color z = .reddish)
          (hgz : G.Adj Q.g z) (hdz : G.Adj d z) :
          HasReachableNegativeReduction C := by
        by_cases hxz : x = z
        · exact lemma5_13_case4_shared_dg_meets_f C hp ha hb hc hd Q hgf'
            hNoShareEG hy hz hgy hgz (by simpa [hxz] using hxy.symm) hdz hdf
        · exact lemma5_13_case4_shared_dg_meets_f C hp ha hb hc hd Q hgf'
            hNoShareEG hx hz hgx hgz hxz hdz hdf
      by_cases hgH : G.Adj Q.g h
      · exact sharedMeetsF hh hgH hdh
      · by_cases hgS : G.Adj Q.g s
        · exact sharedMeetsF hs hgS hds
        · exact hTerminal hx hy hh hs hgx hgy hxa hya hxy
            hdh hds hhc hsc hhs hgdeg hdf hNoShareDE hNoShareEG hgf' hgH hgS
    · have exactShared {h s x : V}
          (hh : C.color h = .reddish) (hs : C.color s = .reddish)
          (hx : C.color x = .reddish)
          (hgh : G.Adj Q.g h) (hgx : G.Adj Q.g x) (hxh : x ≠ h)
          (hdh : G.Adj d h) (hds : G.Adj d s) (hsh : s ≠ h)
          (hgs : ¬ G.Adj Q.g s) : HasReachableNegativeReduction C := by
        have hUnique : ∀ z, C.color z = .reddish →
            G.Adj Q.g z → G.Adj d z → z = h := by
          intro z hz hgz hdz
          rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
              (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh hgz with
            e | e | e
          · exact (color_ne hz ha (by decide) e).elim
          · have ezs : z = s := by
              rcases neighbor_eq_of_degree_three
                  (degreeC (Or.inr hd)) hcd.symm hdh hds
                  (color_ne hc hh (by decide)) (color_ne hc hs (by decide))
                  hsh.symm hdz with q | q | q
              · exact (color_ne hz hc (by decide) q).elim
              · exact (hxh (e.symm.trans q)).elim
              · exact q
            exact (hgs (ezs ▸ hgz)).elim
          · exact e
        have hdegCases : vertexDegree G h = 2 ∨ vertexDegree G h = 3 :=
          C.degree_eq_two_or_three_of_two_neighbors
            (color_ne Q.hg hd (by decide)) hgh.symm hdh.symm
        by_cases hhdeg : vertexDegree G h = 3
        · obtain ⟨i, hhi, hig, hid⟩ :=
            exists_third_neighbor_of_degree_three hhdeg
              (color_ne Q.hg hd (by decide))
          have hiSide : C.color i = .blue ∨ C.color i = .bluish := by
            cases hi : C.color i with
            | red => exact (C.reddish_not_adj_redSide hh (Or.inl hi) hhi).elim
            | reddish => exact (C.reddish_not_adj_redSide hh (Or.inr hi) hhi).elim
            | blue => exact Or.inl rfl
            | bluish => exact Or.inr rfl
          rcases hiSide with hi | hi
          · by_cases hRedI : ∃ j, G.Adj i j ∧ C.color j = .red
            · obtain ⟨j, hij, hj⟩ := hRedI
              have haj : a ≠ j := by
                intro e; subst j; exact hNoBlueAtA i hij.symm hi
              have hdi : d ≠ i := by exact fun e => hid e.symm
              have hci : c ≠ i := by
                intro e; subst i
                have hch : ¬ G.Adj c h := by
                  apply not_adj_fourth_neighbor_of_degree_three
                    (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
                  · exact color_ne hb hd (by decide)
                  · exact color_ne hb Q.hf (by decide)
                  · exact color_ne hd Q.hf (by decide)
                  · exact color_ne hh hb (by decide)
                  · exact color_ne hh hd (by decide)
                  · intro ehf; subst h; exact hdf hdh
                exact hch hhi.symm
              by_cases hbj : b = j
              · subst j
                have hciAdj : ¬ G.Adj c i :=
                  C.blueSide_not_adj_second_neighbor (by simp [hc])
                    (by simp [hd]) (by simp [hi]) hcd hid.symm
                exact HasReachableNegativeReduction.of_current_ce C
                  (containsCutEnhancerA_of C hb hc hi hbc hij.symm
                    hci hciAdj)
              exact lemma5_13_case4_exact_shared_i_blue_red C hp ha hb hc hd
                hh hi hj hdh hhi hij haj hbj hci hdi
            · have hNoRedI : ∀ z, G.Adj i z → C.color z ≠ .red := by
                intro z hiz hz; exact hRedI ⟨z, hiz, hz⟩
              exact lemma5_13_case4_exact_blue_no_red C hc hd hh hs hi
                hcd hdh hds hsh hhi.symm
                (by
                  intro e; subst i
                  have hch : ¬ G.Adj c h := by
                    apply not_adj_fourth_neighbor_of_degree_three
                      (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
                    · exact color_ne hb hd (by decide)
                    · exact color_ne hb Q.hf (by decide)
                    · exact color_ne hd Q.hf (by decide)
                    · exact color_ne hh hb (by decide)
                    · exact color_ne hh hd (by decide)
                    · intro ehf; subst h; exact hdf hdh
                  exact hch hhi.symm)
                (fun e => hid e.symm) hNoRedI
          · by_cases hRedI : ∃ j, G.Adj i j ∧ C.color j = .red
            · obtain ⟨j, hij, hj⟩ := hRedI
              exact lemma5_13_case4_exact_bluish_red C hp ha hb hc hd hNoRedAtD Q
                hgf' hdf hgdeg hNoShareDE hNoShareEG hx hh hs hi hgx hgh
                hxh hdh hds hsh hhi.symm hig hid hUnique hj hij
            · have hNoRedI : ∀ z, G.Adj i z → C.color z ≠ .red := by
                intro z hiz hz; exact hRedI ⟨z, hiz, hz⟩
              by_cases hideg : vertexDegree G i = 3
              · exact lemma5_13_case4_exact_no_red_degree_three C hp ha hb hc hd
                  Q hgf' hdf hgdeg hNoShareDE hNoShareEG hx hh hs hi hgx hgh
                  hxh hdh hds hsh hhi.symm hideg hUnique hNoRedI
              · have hipos : 0 < vertexDegree G i := by
                  change 0 < (G.neighborSet i).ncard
                  rw [Set.ncard_pos]
                  exact ⟨h, hhi.symm⟩
                have hile : vertexDegree G i ≤ 3 := C.subcubic i
                have hilow : vertexDegree G i = 1 ∨ vertexDegree G i = 2 := by omega
                exact lemma5_13_case4_exact_no_red_low_degree C hp ha hb hc hd
                  Q hgf' hdf hgdeg hNoShareDE hNoShareEG hx hh hs hi hgx hgh
                  hxh hdh hds hsh hhi.symm hUnique hNoRedI hilow
        · have hhdeg2 : vertexDegree G h = 2 := by
            rcases hdegCases with hdeg2 | hdeg3
            · exact hdeg2
            · exact (hhdeg hdeg3).elim
          exact lemma5_13_case4_exact_shared_h_degree_two C hp ha hb hc hd Q
            hh hgh hdh hhdeg2
      by_cases hgH : G.Adj Q.g h
      · by_cases hgS : G.Adj Q.g s
        · exact lemma5_13_case4_two_shared_dg C hp ha hb hc hd Q hgf' hdf
            hNoShareEG hh hs hgH hgS hhs hdh hds
        · by_cases hxh : x = h
          · exact exactShared hh hs hy hgH hgy
              (by intro eyh; exact hxy (hxh.trans eyh.symm))
              hdh hds hhs.symm hgS
          · exact exactShared hh hs hx hgH hgx hxh hdh hds hhs.symm hgS
      · by_cases hgS : G.Adj Q.g s
        · by_cases hxs : x = s
          · exact exactShared hs hh hy hgS hgy
              (by intro eys; exact hxy (hxs.trans eys.symm))
              hds hdh hhs hgH
          · exact exactShared hs hh hx hgS hgx hxs hds hdh hhs hgH
        · have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
          have hex : ¬ G.Adj Q.e x := fun ex => hNoShareEG x hx ex hgx
          have hey : ¬ G.Adj Q.e y := fun ey => hNoShareEG y hy ey hgy
          have heh : ¬ G.Adj Q.e h := fun eh => hNoShareDE h hh eh hdh
          have hes : ¬ G.Adj Q.e s := fun es => hNoShareDE s hs es hds
          have hxr : x ≠ Q.r := by intro e; subst x; exact hgr hgx
          have hyr : y ≠ Q.r := by intro e; subst y; exact hgr hgy
          have hxf : x ≠ Q.f := by intro e; subst x; exact hgf' hgx
          have hyf : y ≠ Q.f := by intro e; subst y; exact hgf' hgy
          have hxh : x ≠ h := by intro e; subst x; exact hgH hgx
          have hyh : y ≠ h := by intro e; subst y; exact hgH hgy
          have hxs : x ≠ s := by intro e; subst x; exact hgS hgx
          have hys : y ≠ s := by intro e; subst y; exact hgS hgy
          have hrh : Q.r ≠ h := by intro e; subst h; exact heh Q.her
          have hrs : Q.r ≠ s := by intro e; subst s; exact hes Q.her
          have hfh : Q.f ≠ h := by intro e; subst h; exact hdf hdh
          have hfs : Q.f ≠ s := by intro e; subst s; exact hdf hds
          have hrf : Q.r ≠ Q.f := by
            intro e; apply Q.hef; rw [← e]; exact Q.her
          have hn : [Q.g, Q.e, c, d, x, y, Q.r, a, b, Q.f, h, s].Nodup := by
            simp [Q.hge, hgx.ne, hgy.ne, Q.her.ne, Q.heaEdge.ne,
              Q.hbe.ne, hcd.ne, hbc.ne, hab.ne, Q.hcf.ne, hdh.ne,
              hds.ne, hxy, hhs, hxr, hyr, hxf, hyf, hxh, hyh, hxs,
              hys, hrh, hrs, hrf, hfh, hfs,
              color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
              color_ne Q.hg hx (by decide), color_ne Q.hg hy (by decide),
              color_ne Q.hg Q.hr (by decide),
              color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
              color_ne Q.hg Q.hf (by decide), color_ne Q.hg hh (by decide),
              color_ne Q.hg hs (by decide),
              color_ne Q.he hc (by decide), color_ne Q.he hd (by decide),
              color_ne Q.he hx (by decide), color_ne Q.he hy (by decide),
              color_ne Q.he Q.hr (by decide),
              color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
              color_ne Q.he Q.hf (by decide), color_ne Q.he hh (by decide),
              color_ne Q.he hs (by decide),
              color_ne hc hx (by decide), color_ne hc hy (by decide),
              color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
              color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
              color_ne hc hh (by decide), color_ne hc hs (by decide),
              color_ne hd hx (by decide), color_ne hd hy (by decide),
              color_ne hd Q.hr (by decide), color_ne hd ha (by decide),
              color_ne hd hb (by decide), color_ne hd Q.hf (by decide),
              color_ne hd hh (by decide), color_ne hd hs (by decide),
              color_ne hx ha (by decide), color_ne hx hb (by decide),
              color_ne hy ha (by decide), color_ne hy hb (by decide),
              color_ne Q.hr ha (by decide), color_ne Q.hr hb (by decide),
              color_ne ha Q.hf (by decide), color_ne ha hh (by decide),
              color_ne ha hs (by decide), color_ne hb Q.hf (by decide),
              color_ne hb hh (by decide), color_ne hb hs (by decide)]
          exact lemma5_13_case4_disjoint_avoids_f C ha hb hc hd Q hx hy hh hs
            hgx hgy hdh hds hcd hbc hab hgr hgf' hgH hgS hex hey heh hes hn
  · have hpos : 0 < vertexDegree G Q.g := by
      change 0 < (G.neighborSet Q.g).ncard
      rw [Set.ncard_pos]
      exact ⟨a, Q.hag.symm⟩
    have hle : vertexDegree G Q.g ≤ 3 := C.subcubic Q.g
    have hlow : vertexDegree G Q.g = 1 ∨ vertexDegree G Q.g = 2 := by omega
    exact lemma5_13_case4_low_degree C hpath ha hb hc hd Q hgf'
      hNoOtherRedG hNoShareEG hlow

/-- Complete Case (4), including the temporary `{b,c}` relabeling in
Case (4.4.4.1). -/
theorem lemma5_13_case4
    (C : MatchingCutColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoBlueAtA : ∀ v, G.Adj a v → C.color v ≠ .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma5_13Case4Configuration C a b c d)
    (hOutsideF : ∀ z, G.Adj Q.f z → z ≠ c → z ≠ d →
      C.color z = .bluish) :
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
  apply lemma5_13_case4_core C hpath ha hb hc hd hNoBlueAtA hNoRedAtD Q
    (hOutsideF := hOutsideF)
  intro x y h s hx hy hh hs hgx hgy hxa hya hxy
    hdh hds hhc hsc hhs hgdeg hdf hNoShareDE hNoShareEG hgf hgh hgs
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath4 G a b c d := ⟨hinj, hedge⟩
  have hv {u v : Fin 4} (huv : u ≠ v) :
      (![a,b,c,d] u) ≠ (![a,b,c,d] v) := hinj.ne huv
  have edge (u v : Fin 4)
      (huv : (graphOfEdges [(0,1),(1,2),(2,3)]).Adj u v) :
      G.Adj (![a,b,c,d] u) (![a,b,c,d] v) := (hedge u v).mp huv
  have nonedge (u v : Fin 4)
      (huv : ¬ (graphOfEdges [(0,1),(1,2),(2,3)]).Adj u v) :
      ¬ G.Adj (![a,b,c,d] u) (![a,b,c,d] v) := fun z => huv ((hedge u v).mpr z)
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hac : ¬ G.Adj a c := by simpa using nonedge 0 2 (by native_decide)
  have had : ¬ G.Adj a d := by simpa using nonedge 0 3 (by native_decide)
  have hbd : ¬ G.Adj b d := by simpa using nonedge 1 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (hne : cu ≠ cv) : u ≠ v := by
    intro e; subst v; simp_all
  have hfCases := neighbor_eq_of_degree_three
    (degreeC (Or.inr hd)) hcd.symm hdh hds
    (color_ne hc hh (by decide)) (color_ne hc hs (by decide)) hhs hdf
  have finish {r : V} (hr : C.color r = .reddish)
      (hdr : G.Adj d r) (hrf : r ≠ Q.f) (hgr : ¬ G.Adj Q.g r) :
      HasReachableNegativeReduction C := by
    obtain ⟨t, hft, htc, htd⟩ :=
      exists_third_neighbor_of_degree_three Q.hfdeg hcd.ne
    have ht := hOutsideF t hft htc htd
    have htb : ¬ G.Adj t b := by
      intro htb
      apply (not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
        (color_ne ha hc (by decide)) (color_ne ha Q.he (by decide))
        (color_ne hc Q.he (by decide)) (color_ne ht ha (by decide))
        (color_ne ht hc (by decide)) (by intro e; subst t; exact Q.hef hft.symm))
      exact htb.symm
    have hrc : ¬ G.Adj r c := by
      intro hrc
      apply (not_adj_fourth_neighbor_of_degree_three
        (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
        (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
        (color_ne hd Q.hf (by decide)) (color_ne hr hb (by decide))
        (color_ne hr hd (by decide)) hrf)
      exact hrc.symm
    rcases exists_flipAt_or_cutEnhancer C hb hc ha hd
        (degreeC (Or.inl hb)) (degreeC (Or.inr hc)) hab.symm hbc hcd with
      ⟨M, hflip⟩ | hce
    · let D := M.toColoring
      have hcD : D.color c = .red :=
        red_of_flipped_blue_endpoint C hflip hd hcd
          (degreeC (Or.inr hc))
          (color_ne hd hb (by decide))
      have hbD : D.color b = .blue :=
        blue_of_flipped_red_endpoint C hflip ha hab.symm
          (degreeC (Or.inl hb))
          (color_ne ha hc (by decide))
      have hfD : D.color Q.f = .red :=
        red_of_reddish_gains_flipped_blue C hflip Q.hf Q.hcf.symm
          (color_ne Q.hf hb (by decide)) (color_ne Q.hf hc (by decide))
      have heD : D.color Q.e = .blue :=
        blue_of_bluish_gains_flipped_red C hflip Q.he Q.hbe.symm
          (color_ne Q.he hb (by decide)) (color_ne Q.he hc (by decide))
      have hdD : D.color d = .bluish :=
        bluish_of_blue_loses_flipped_mate C hflip hd hcd.symm
          (fun z => hbd z.symm)
          (color_ne hd hb (by decide)) hcd.ne.symm
      have haD : D.color a = .reddish :=
        reddish_of_red_loses_flipped_mate C hflip ha hab hac
          hab.ne (color_ne ha hc (by decide))
      have htD : D.color t = .bluish :=
        bluish_of_untouched_bluish C hflip ht htb
          (color_ne ht hb (by decide)) (color_ne ht hc (by decide))
      have hrD : D.color r = .reddish :=
        reddish_of_untouched_reddish C hflip hr hrc
          (color_ne hr hb (by decide)) (color_ne hr hc (by decide))
      have hpathD : FormsInducedPath4 G Q.f c b Q.e := by
        refine ⟨?_, ?_⟩
        · have hn : [Q.f, c, b, Q.e].Nodup := by
            simp [Q.hcf.ne, Q.hcf.ne.symm, hbc.ne, hbc.ne.symm, Q.hbe.ne,
              color_ne Q.hf hb (by decide), color_ne Q.hf Q.he (by decide),
              color_ne hc Q.he (by decide)]
          have hv' : (![Q.f,c,b,Q.e] : Fin 4 → V) = [Q.f,c,b,Q.e].get := by
            funext z; fin_cases z <;> rfl
          rw [hv']
          exact hn.injective_get
        · intro u v
          have hfb : ¬ G.Adj Q.f b :=
            C.reddish_not_adj_redSide Q.hf (Or.inl hb)
          have hce : ¬ G.Adj c Q.e := fun z =>
            C.bluish_not_adj_blueSide Q.he (Or.inl hc) z.symm
          have hbf : ¬ G.Adj b Q.f := fun z => hfb z.symm
          have hec : ¬ G.Adj Q.e c := fun z => hce z.symm
          fin_cases u <;> fin_cases v <;>
            simp [graphOfEdges, G.adj_comm, Q.hcf, hbc, Q.hbe,
              hfb, hbf, hce, hec, Q.hef]
      let R : Lemma5_13Case4Configuration D Q.f c b Q.e := {
        e := d, f := a, he := hdD, hf := haD,
        hbe := hcd, hcf := hab.symm,
        hea := hdf.ne, hec := color_ne hd hb (by decide),
        hfb := color_ne ha hc (by decide), hfd := Q.heaEdge.ne.symm,
        hedeg := degreeC (Or.inr hd),
        hfdeg := degreeC (Or.inl ha),
        heaEdge := hdf, hef := fun z => had z.symm,
        g := t, hg := htD, hag := hft,
        hgb := htc, hge := htd,
        r := r, hr := hrD, her := hdr,
        hra := hrf, hrb := color_ne hr hc (by decide) }
      have hNoBlueF : ∀ z, G.Adj Q.f z → D.color z ≠ .blue := by
        intro z hfz hz
        rcases neighbor_eq_of_degree_three Q.hfdeg Q.hcf.symm hdf.symm hft
            hcd.ne (color_ne hc ht (by decide))
            (color_ne hd ht (by decide)) hfz with e | e | e
        · subst z; simp [hcD] at hz
        · subst z; simp [hdD] at hz
        · subst z; simp [htD] at hz
      have hQrC : ¬ G.Adj Q.r c := by
        intro hQrC
        apply (not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
          (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
          (color_ne hd Q.hf (by decide)) (color_ne Q.hr hb (by decide))
          (color_ne Q.hr hd (by decide))
          (by
            intro e
            apply Q.hef
            exact e ▸ Q.her))
        exact hQrC.symm
      have hQrD : D.color Q.r = .reddish :=
        reddish_of_untouched_reddish C hflip Q.hr hQrC
          (color_ne Q.hr hb (by decide)) (color_ne Q.hr hc (by decide))
      have hNoRedE : ∀ z, G.Adj Q.e z → D.color z ≠ .red := by
        intro z hez hz
        rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm Q.heaEdge Q.her
            hab.ne.symm (color_ne hb Q.hr (by decide))
            (color_ne ha Q.hr (by decide)) hez with e | e | e
        · subst z; simp [hbD] at hz
        · subst z; simp [haD] at hz
        · subst z; simp [hQrD] at hz
      have hgb : ¬ G.Adj Q.g b := by
        apply not_adj_fourth_neighbor_of_degree_three hgdeg Q.hag.symm hgx hgy
        · exact color_ne ha hx (by decide)
        · exact color_ne ha hy (by decide)
        · exact hxy
        · exact hab.ne.symm
        · exact color_ne hb hx (by decide)
        · exact color_ne hb hy (by decide)
      have hgD : D.color Q.g = .bluish :=
        bluish_of_untouched_bluish C hflip Q.hg hgb
          (color_ne Q.hg hb (by decide)) (color_ne Q.hg hc (by decide))
      have hOutsideA : ∀ z, G.Adj a z → z ≠ b → z ≠ Q.e →
          D.color z = .bluish := by
        intro z haz hzb hze
        have ez : z = Q.g := by
          rcases neighbor_eq_of_degree_three
              (degreeC (Or.inl ha)) hab Q.heaEdge.symm Q.hag
              (color_ne hb Q.he (by decide))
              (color_ne hb Q.hg (by decide)) Q.hge.symm haz with e | e | e
          · exact (hzb e).elim
          · exact (hze e).elim
          · exact e
        simpa [ez] using hgD
      apply HasReachableNegativeReduction.after_flip C hflip
      apply lemma5_13_case4_core D hpathD hfD hcD hbD heD hNoBlueF hNoRedE R
        (hOutsideF := hOutsideA)
      intro u v p q hu hv hpq hqq htu htv huf hvf huv
        hep heq hpf hqf hpqne htdeg hea hNoShareDE' hNoShareEG' htfa htp htq
      dsimp [R] at htu htv htdeg hea hNoShareDE' hNoShareEG' htfa htp htq
      -- The terminal post-flip configuration is disjoint unless `t` and
      -- the original `g` share a reddish neighbor; those shared-neighbor
      -- alternatives are handled separately.
      have color_neD {z w : V} {cz cw : Color}
          (hz : D.color z = cz) (hw : D.color w = cw) (hne : cz ≠ cw) : z ≠ w := by
        intro e; subst w; simp_all
      have hxc : ¬ G.Adj x c := by
        intro z
        apply (not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
          (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
          (color_ne hd Q.hf (by decide)) (color_ne hx hb (by decide))
          (color_ne hx hd (by decide))
          (by intro e; subst x; exact hgf hgx)) z.symm
      have hyc : ¬ G.Adj y c := by
        intro z
        apply (not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
          (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
          (color_ne hd Q.hf (by decide)) (color_ne hy hb (by decide))
          (color_ne hy hd (by decide))
          (by intro e; subst y; exact hgf hgy)) z.symm
      have hxD : D.color x = .reddish :=
        reddish_of_untouched_reddish C hflip hx hxc
          (color_ne hx hb (by decide)) (color_ne hx hc (by decide))
      have hyD : D.color y = .reddish :=
        reddish_of_untouched_reddish C hflip hy hyc
          (color_ne hy hb (by decide)) (color_ne hy hc (by decide))
      have hgc : ¬ G.Adj Q.g c :=
        C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
      have hgbD : ¬ G.Adj Q.g b := hgb
      have htbD : ¬ G.Adj t b :=
        D.bluish_not_adj_blueSide htD (Or.inl hbD)
      have htcAdj : ¬ G.Adj t c := by
        intro z
        apply (not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hc)) hbc.symm hcd Q.hcf
          (color_ne hb hd (by decide)) (color_ne hb Q.hf (by decide))
          (color_ne hd Q.hf (by decide)) (color_neD htD hbD (by decide))
          (color_ne ht hd (by decide)) hft.ne.symm) z.symm
      have hba : G.Adj b a := hab.symm
      have hbf0 : ¬ G.Adj b Q.f :=
        C.reddish_not_adj_redSide Q.hf (Or.inl hb) ∘ SimpleGraph.Adj.symm
      have hbx : ¬ G.Adj b x :=
        fun z => C.reddish_not_adj_redSide hx (Or.inl hb) z.symm
      have hby : ¬ G.Adj b y :=
        fun z => C.reddish_not_adj_redSide hy (Or.inl hb) z.symm
      have hgr0 : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
      have hdr0 : ¬ G.Adj d Q.r := by
        intro hz
        exact hNoShareDE' Q.r hQrD hz Q.her
      have hdx : ¬ G.Adj d x := by
        apply not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hd)) hcd.symm hdh hds
        · exact color_ne hc hh (by decide)
        · exact color_ne hc hs (by decide)
        · exact hhs
        · exact color_ne hx hc (by decide)
        · intro e; subst x; exact hgh hgx
        · intro e; subst x; exact hgs hgx
      have hdy : ¬ G.Adj d y := by
        apply not_adj_fourth_neighbor_of_degree_three
          (degreeC (Or.inr hd)) hcd.symm hdh hds
        · exact color_ne hc hh (by decide)
        · exact color_ne hc hs (by decide)
        · exact hhs
        · exact color_ne hy hc (by decide)
        · intro e; subst y; exact hgh hgy
        · intro e; subst y; exact hgs hgy
      have htQr : ¬ G.Adj t Q.r := by
        intro hz
        rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm hep heq
            hpf.symm hqf.symm hpqne Q.her with e | e | e
        · exact (color_ne Q.hr hb (by decide) e).elim
        · exact htp (e ▸ hz)
        · exact htq (e ▸ hz)
      have hdu : ¬ G.Adj d u := by
        intro z; exact hNoShareEG' u hu z htu
      have hdv : ¬ G.Adj d v := by
        intro z; exact hNoShareEG' v hv z htv
      have htRr : ¬ G.Adj t r := hNoShareEG' r hrD hdr
      have hgRr : ¬ G.Adj Q.g r := hgr
      have htg : t ≠ Q.g := by
        intro e; subst t; exact htfa Q.hag.symm
      have finishBoth (htx : G.Adj t x) (hty : G.Adj t y) :
          HasReachableNegativeReduction D := by
        apply lemma5_13_case4_exact_no_red_shared_g_meets_f D
          hfD hcD hbD hgD htD hxD hyD haD
          hgx hgy Q.hag.symm htx hty hft.symm hba hbc Q.hcf.symm
          hgbD hgf hgc htbD htfa htcAdj hbx hby hbf0
        simp [htg, htg.symm, hxy, hxa, hya, Q.hag.ne, hgx.ne, hgy.ne,
          hft.ne, hbc.ne, hab.ne, Q.hcf.ne,
          color_neD hgD hbD (by decide), color_neD hgD hxD (by decide),
          color_neD hgD hyD (by decide), color_neD hgD haD (by decide),
          color_neD hgD hfD (by decide), color_neD hgD hcD (by decide),
          color_neD htD hbD (by decide), color_neD htD hxD (by decide),
          color_neD htD hyD (by decide), color_neD htD haD (by decide),
          color_neD htD hfD (by decide), color_neD htD hcD (by decide),
          color_neD hbD hxD (by decide), color_neD hbD hyD (by decide),
          color_neD hbD haD (by decide), color_neD hbD hfD (by decide),
          color_neD hbD hcD (by decide), color_neD hxD hfD (by decide),
          color_neD hxD hcD (by decide), color_neD hyD hfD (by decide),
          color_neD hyD hcD (by decide), color_neD haD hfD (by decide),
          color_neD haD hcD (by decide), Q.hcf.ne.symm]
      by_cases htx : G.Adj t x
      · by_cases hty : G.Adj t y
        · exact finishBoth htx hty
        · rcases neighbor_eq_of_degree_three htdeg hft.symm htu htv
              huf.symm hvf.symm huv htx with ex | ex | ex
          · exact (hgf (ex ▸ hgx)).elim
          · subst x
            have hyV : y ≠ v := by intro e; subst v; exact hty htv
            have hva : v ≠ a := by intro e; subst v; exact htfa htv
            have hgv : ¬ G.Adj Q.g v := by
              intro z
              rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgy
                  hxa.symm hya.symm hxy z with e | e | e
              · exact htfa (e ▸ htv)
              · exact huv (e.symm)
              · exact hty (e ▸ htv)
            have hbV : ¬ G.Adj b v := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
              · exact color_ne ha hc (by decide)
              · exact color_ne ha Q.he (by decide)
              · exact color_ne hc Q.he (by decide)
              · intro e; subst v; exact htfa htv
              · exact color_neD hv hcD (by decide)
              · exact color_neD hv heD (by decide)
            apply lemma5_13_case4_exact_no_red_meets_f D
              hfD hcD hbD hgD htD hyD hv hu haD
              hgy hgx Q.hag.symm htv htu hft.symm hba hbc Q.hcf.symm
              hgbD hgv hgf hgc htbD hty htfa htcAdj hby hbV hbx hbf0
            simp [htg, htg.symm, hxy, hxy.symm, huv, huv.symm, hxa, hya, huf, hvf,
              hyV, hva, Q.hag.ne, hgy.ne,
              htu.ne, htv.ne, hft.ne, hbc.ne, hab.ne, Q.hcf.ne,
              color_neD hgD hbD (by decide), color_neD hgD hyD (by decide),
              color_neD hgD hv (by decide), color_neD hgD hu (by decide),
              color_neD hgD haD (by decide), color_neD hgD hfD (by decide),
              color_neD hgD hcD (by decide), color_neD htD hbD (by decide),
              color_neD htD hyD (by decide), color_neD htD hv (by decide),
              color_neD htD hu (by decide), color_neD htD haD (by decide),
              color_neD htD hfD (by decide), color_neD htD hcD (by decide),
              color_neD hbD hyD (by decide), color_neD hbD hv (by decide),
              color_neD hbD hu (by decide), color_neD hbD haD (by decide),
              color_neD hbD hfD (by decide), color_neD hbD hcD (by decide),
              color_neD hyD hfD (by decide), color_neD hyD hcD (by decide),
              color_neD hv hfD (by decide), color_neD hv hcD (by decide),
              color_neD hu hfD (by decide), color_neD hu hcD (by decide),
              color_neD haD hfD (by decide), color_neD haD hcD (by decide),
              Q.hcf.ne.symm]
          · subst x
            have hyU : y ≠ u := by intro e; subst u; exact hty htu
            have hua : u ≠ a := by intro e; subst u; exact htfa htu
            have hgu : ¬ G.Adj Q.g u := by
              intro z
              rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgy
                  hxa.symm hya.symm hxy z with e | e | e
              · exact htfa (e ▸ htu)
              · exact huv e
              · exact hty (e ▸ htu)
            have hbU : ¬ G.Adj b u := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
              · exact color_ne ha hc (by decide)
              · exact color_ne ha Q.he (by decide)
              · exact color_ne hc Q.he (by decide)
              · intro e; subst u; exact htfa htu
              · exact color_neD hu hcD (by decide)
              · exact color_neD hu heD (by decide)
            apply lemma5_13_case4_exact_no_red_meets_f D
              hfD hcD hbD hgD htD hyD hu hv haD
              hgy hgx Q.hag.symm htu htv hft.symm hba hbc Q.hcf.symm
              hgbD hgu hgf hgc htbD hty htfa htcAdj hby hbU hbx hbf0
            simp [htg, htg.symm, hxy, hxy.symm, huv, huv.symm, hxa, hya, huf, hvf,
              hyU, hua, Q.hag.ne, hgy.ne,
              htu.ne, htv.ne, hft.ne, hbc.ne, hab.ne, Q.hcf.ne,
              color_neD hgD hbD (by decide), color_neD hgD hyD (by decide),
              color_neD hgD hu (by decide), color_neD hgD hv (by decide),
              color_neD hgD haD (by decide), color_neD hgD hfD (by decide),
              color_neD hgD hcD (by decide), color_neD htD hbD (by decide),
              color_neD htD hyD (by decide), color_neD htD hu (by decide),
              color_neD htD hv (by decide), color_neD htD haD (by decide),
              color_neD htD hfD (by decide), color_neD htD hcD (by decide),
              color_neD hbD hyD (by decide), color_neD hbD hu (by decide),
              color_neD hbD hv (by decide), color_neD hbD haD (by decide),
              color_neD hbD hfD (by decide), color_neD hbD hcD (by decide),
              color_neD hyD hfD (by decide), color_neD hyD hcD (by decide),
              color_neD hu hfD (by decide), color_neD hu hcD (by decide),
              color_neD hv hfD (by decide), color_neD hv hcD (by decide),
              color_neD haD hfD (by decide), color_neD haD hcD (by decide),
              Q.hcf.ne.symm]
      · by_cases hty : G.Adj t y
        · rcases neighbor_eq_of_degree_three htdeg hft.symm htu htv
              huf.symm hvf.symm huv hty with ey | ey | ey
          · exact (hgf (ey ▸ hgy)).elim
          · subst y
            have hxV : x ≠ v := by intro e; subst v; exact htx htv
            have hva : v ≠ a := by intro e; subst v; exact htfa htv
            have hgv : ¬ G.Adj Q.g v := by
              intro z
              rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgy hgx
                  hya.symm hxa.symm hxy.symm z with e | e | e
              · exact htfa (e ▸ htv)
              · exact huv e.symm
              · exact htx (e ▸ htv)
            have hbV : ¬ G.Adj b v := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
              · exact color_ne ha hc (by decide)
              · exact color_ne ha Q.he (by decide)
              · exact color_ne hc Q.he (by decide)
              · intro e; subst v; exact htfa htv
              · exact color_neD hv hcD (by decide)
              · exact color_neD hv heD (by decide)
            apply lemma5_13_case4_exact_no_red_meets_f D
              hfD hcD hbD hgD htD hxD hv hu haD
              hgx hgy Q.hag.symm htv htu hft.symm hba hbc Q.hcf.symm
              hgbD hgv hgf hgc htbD htx htfa htcAdj hbx hbV hby hbf0
            simp [htg, htg.symm, hxy, hxy.symm, huv, huv.symm, hxa, hya, huf, hvf,
              hxV, hva, Q.hag.ne, hgx.ne,
              htu.ne, htv.ne, hft.ne, hbc.ne, hab.ne, Q.hcf.ne,
              color_neD hgD hbD (by decide), color_neD hgD hxD (by decide),
              color_neD hgD hv (by decide), color_neD hgD hu (by decide),
              color_neD hgD haD (by decide), color_neD hgD hfD (by decide),
              color_neD hgD hcD (by decide), color_neD htD hbD (by decide),
              color_neD htD hxD (by decide), color_neD htD hv (by decide),
              color_neD htD hu (by decide), color_neD htD haD (by decide),
              color_neD htD hfD (by decide), color_neD htD hcD (by decide),
              color_neD hbD hxD (by decide), color_neD hbD hv (by decide),
              color_neD hbD hu (by decide), color_neD hbD haD (by decide),
              color_neD hbD hfD (by decide), color_neD hbD hcD (by decide),
              color_neD hxD hfD (by decide), color_neD hxD hcD (by decide),
              color_neD hv hfD (by decide), color_neD hv hcD (by decide),
              color_neD hu hfD (by decide), color_neD hu hcD (by decide),
              color_neD haD hfD (by decide), color_neD haD hcD (by decide),
              Q.hcf.ne.symm]
          · subst y
            have hxU : x ≠ u := by intro e; subst u; exact htx htu
            have hua : u ≠ a := by intro e; subst u; exact htfa htu
            have hgu : ¬ G.Adj Q.g u := by
              intro z
              rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgy hgx
                  hya.symm hxa.symm hxy.symm z with e | e | e
              · exact htfa (e ▸ htu)
              · exact huv e
              · exact htx (e ▸ htu)
            have hbU : ¬ G.Adj b u := by
              apply not_adj_fourth_neighbor_of_degree_three
                (degreeC (Or.inl hb)) hab.symm hbc Q.hbe
              · exact color_ne ha hc (by decide)
              · exact color_ne ha Q.he (by decide)
              · exact color_ne hc Q.he (by decide)
              · intro e; subst u; exact htfa htu
              · exact color_neD hu hcD (by decide)
              · exact color_neD hu heD (by decide)
            apply lemma5_13_case4_exact_no_red_meets_f D
              hfD hcD hbD hgD htD hxD hu hv haD
              hgx hgy Q.hag.symm htu htv hft.symm hba hbc Q.hcf.symm
              hgbD hgu hgf hgc htbD htx htfa htcAdj hbx hbU hby hbf0
            simp [htg, htg.symm, hxy, hxy.symm, huv, huv.symm, hxa, hya, huf, hvf,
              hxU, hua, Q.hag.ne, hgx.ne,
              htu.ne, htv.ne, hft.ne, hbc.ne, hab.ne, Q.hcf.ne,
              color_neD hgD hbD (by decide), color_neD hgD hxD (by decide),
              color_neD hgD hu (by decide), color_neD hgD hv (by decide),
              color_neD hgD haD (by decide), color_neD hgD hfD (by decide),
              color_neD hgD hcD (by decide), color_neD htD hbD (by decide),
              color_neD htD hxD (by decide), color_neD htD hu (by decide),
              color_neD htD hv (by decide), color_neD htD haD (by decide),
              color_neD htD hfD (by decide), color_neD htD hcD (by decide),
              color_neD hbD hxD (by decide), color_neD hbD hu (by decide),
              color_neD hbD hv (by decide), color_neD hbD haD (by decide),
              color_neD hbD hfD (by decide), color_neD hbD hcD (by decide),
              color_neD hxD hfD (by decide), color_neD hxD hcD (by decide),
              color_neD hu hfD (by decide), color_neD hu hcD (by decide),
              color_neD hv hfD (by decide), color_neD hv hcD (by decide),
              color_neD haD hfD (by decide), color_neD haD hcD (by decide),
              Q.hcf.ne.symm]
        · have hgu : ¬ G.Adj Q.g u := by
            intro z
            rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgy
                hxa.symm hya.symm hxy z with e | e | e
            · exact htfa (e ▸ htu)
            · exact htx (e ▸ htu)
            · exact hty (e ▸ htu)
          have hgv : ¬ G.Adj Q.g v := by
            intro z
            rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgy
                hxa.symm hya.symm hxy z with e | e | e
            · exact htfa (e ▸ htv)
            · exact htx (e ▸ htv)
            · exact hty (e ▸ htv)
          have hdgV : d ≠ Q.g := by
            intro e
            exact hgf (e ▸ hdf)
          have hur : u ≠ r := by intro e; subst u; exact htRr htu
          have huQr : u ≠ Q.r := by intro e; subst u; exact htQr htu
          have hux : u ≠ x := by intro e; subst u; exact hgu hgx
          have huy : u ≠ y := by intro e; subst u; exact hgu hgy
          have hua : u ≠ a := by intro e; subst u; exact htfa htu
          have hvr : v ≠ r := by intro e; subst v; exact htRr htv
          have hvQr : v ≠ Q.r := by intro e; subst v; exact htQr htv
          have hvx : v ≠ x := by intro e; subst v; exact hgv hgx
          have hvy : v ≠ y := by intro e; subst v; exact hgv hgy
          have hva : v ≠ a := by intro e; subst v; exact htfa htv
          have hra : r ≠ a := by intro e; subst r; exact had hdr.symm
          have hrQr : r ≠ Q.r := by intro e; subst r; exact hdr0 hdr
          have hrx : r ≠ x := by intro e; subst r; exact hdx hdr
          have hry : r ≠ y := by intro e; subst r; exact hdy hdr
          have hQrX : Q.r ≠ x := by
            intro e; subst x; exact hgr0 hgx
          have hQrY : Q.r ≠ y := by
            intro e; subst y; exact hgr0 hgy
          apply lemma5_13_case4_disjoint_meets_f_no_share D
            hfD hcD hbD heD R hgD hu hv hQrD hxD hyD
            hft.symm htu htv hdr hdf hcd.symm Q.hbe hbc.symm hab.symm
            Q.heaEdge Q.her
            Q.hag.symm hgx hgy Q.hcf.symm htRr htfa htQr htx hty
            hdu hdv (fun z => had z.symm) hdr0 hdx hdy hgu hgv hgRr hgr0
          dsimp [R]
          simp [htg, htg.symm, htd, hdgV, huv, hxy, hpqne, hxa, hya,
            huf, hvf, hur, huQr, hux, huy, hua, hvr, hvQr, hvx, hvy, hva,
            hra, hrQr, hrx, hry, hQrX, hQrY,
            Q.hag.ne, hgx.ne, hgy.ne, hft.ne, htu.ne, htv.ne,
            hdr.ne, hdf.ne, hcd.ne, hbc.ne, hab.ne, Q.heaEdge.ne,
            Q.her.ne, Q.hcf.ne, Q.hcf.ne.symm, Q.hbe.ne, hxa.symm, hya.symm,
            color_ne ha Q.hr (by decide),
            color_neD htD hrD (by decide),
            color_neD hdD hbD (by decide), color_neD hdD heD (by decide),
            color_neD hdD hu (by decide), color_neD hdD hv (by decide),
            color_neD hdD hcD (by decide), color_neD hdD haD (by decide),
            color_neD hdD hQrD (by decide), color_neD hdD hxD (by decide),
            color_neD hdD hyD (by decide),
            color_neD hbD hgD (by decide), color_neD hbD hu (by decide),
            color_neD hbD hv (by decide), color_neD hbD hrD (by decide),
            color_neD hbD hfD (by decide), color_neD hbD haD (by decide),
            color_neD hbD hQrD (by decide), color_neD hbD hxD (by decide),
            color_neD hbD hyD (by decide),
            color_neD heD hgD (by decide), color_neD heD hu (by decide),
            color_neD heD hv (by decide), color_neD heD hrD (by decide),
            color_neD heD hfD (by decide), color_neD heD hcD (by decide),
            color_neD heD hxD (by decide), color_neD heD hyD (by decide),
            color_neD hgD hu (by decide), color_neD hgD hv (by decide),
            color_neD hgD hrD (by decide), color_neD hgD hfD (by decide),
            color_neD hgD hcD (by decide), color_neD hgD haD (by decide),
            color_neD hgD hQrD (by decide),
            color_neD hu hcD (by decide), color_neD hv hcD (by decide),
            color_neD hrD hfD (by decide), color_neD hrD hcD (by decide),
            color_neD hfD haD (by decide), color_neD hfD hQrD (by decide),
            color_neD hfD hxD (by decide), color_neD hfD hyD (by decide),
            color_neD hcD haD (by decide), color_neD hcD hQrD (by decide),
            color_neD hcD hxD (by decide), color_neD hcD hyD (by decide),
            color_neD htD heD (by decide), color_neD htD hbD (by decide),
            color_neD htD hu (by decide),
            color_neD htD hv (by decide), color_neD htD hQrD (by decide),
            color_neD htD hfD (by decide), color_neD htD hcD (by decide),
            color_neD htD haD (by decide), color_neD htD hxD (by decide),
            color_neD htD hyD (by decide)]
    · exact HasReachableNegativeReduction.of_current_ce C hce
  rcases hfCases with hfC | hfH | hfS
  · exact (color_ne Q.hf hc (by decide) hfC).elim
  · subst h
    exact finish hs hds hhs.symm hgs
  · subst s
    exact finish hh hdh hhs hgh

end Subcubic
