import Subcubic.Lemma4_12.Case4

/-! Case (3.2) of Lemma 4.12. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma4_12NoShareConfiguration (C : GoodColoring G)
    (a b c d : V) extends Lemma4_12ThirdNeighborConfiguration C a b c d where
  x : V
  y : V
  i : V
  j : V
  hx : C.color x = .reddish
  hy : C.color y = .reddish
  hi : C.color i = .reddish
  hj : C.color j = .reddish
  hex : G.Adj e x
  hey : G.Adj e y
  hdi : G.Adj d i
  hdj : G.Adj d j
  hxb : x ≠ b
  hyb : y ≠ b
  hxy : x ≠ y
  hic : i ≠ c
  hjc : j ≠ c
  hij : i ≠ j
  hei : ¬ G.Adj e i
  hej : ¬ G.Adj e j
  hdx : ¬ G.Adj d x
  hdy : ¬ G.Adj d y

theorem lemma4_12_no_share_setup
    (C : GoodColoring G) {a b c d : V}
    (hd : C.color d = .blue) (hc : C.color c = .blue)
    (hcd : G.Adj c d)
    (hddeg : vertexDegree G d = 3)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma4_12ThirdNeighborConfiguration C a b c d)
    (hOnlyRedB : ∀ z, G.Adj Q.e z → C.color z = .red → z = b)
    (hNoShare : ∀ z, C.color z = .reddish →
      G.Adj Q.e z → ¬ G.Adj d z) :
    ∃ R : Lemma4_12NoShareConfiguration C a b c d,
      R.toLemma4_12ThirdNeighborConfiguration = Q := by
  classical
  obtain ⟨x, y, hex, hey, hxb, hyb, hxy⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hedeg Q.hbe.symm
  have reddish_of_e_other {z : V} (hez : G.Adj Q.e z) (hzb : z ≠ b) :
      C.color z = .reddish := by
    cases hz : C.color z with
    | red => exact (hzb (hOnlyRedB z hez hz)).elim
    | reddish => exact rfl
    | blue => exact (C.bluish_not_adj_blueSide Q.he (Or.inl hz) hez).elim
    | bluish => exact (C.bluish_not_adj_blueSide Q.he (Or.inr hz) hez).elim
  have hx := reddish_of_e_other hex hxb
  have hy := reddish_of_e_other hey hyb
  obtain ⟨i, j, hdi, hdj, hic, hjc, hij⟩ :=
    C.exists_two_other_neighbors hddeg hcd.symm
  have reddish_of_d_other {z : V} (hdz : G.Adj d z) (hzc : z ≠ c) :
      C.color z = .reddish := by
    have hzSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdz hzc
    rcases hzSide with hz | hz
    · exact (hNoRedAtD z hdz hz).elim
    · exact hz
  have hi := reddish_of_d_other hdi hic
  have hj := reddish_of_d_other hdj hjc
  exact ⟨⟨Q, x, y, i, j, hx, hy, hi, hj, hex, hey, hdi, hdj,
    hxb, hyb, hxy, hic, hjc, hij,
    (fun hei => (hNoShare i hi hei) hdi),
    (fun hej => (hNoShare j hj hej) hdj),
    hNoShare x hx hex,
    hNoShare y hy hey⟩, rfl⟩

theorem lemma4_12_case3_no_share
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
    (hNoRedAtD : ∀ v, G.Adj d v → C.color v ≠ .red)
    (Q : Lemma4_12NoShareConfiguration C a b c d)
    (hNoShare : ∀ z, C.color z = .reddish → G.Adj Q.e z → ¬ G.Adj d z)
    (hea : ¬ G.Adj Q.e a) (hef : ¬ G.Adj Q.e Q.f) :
    HasReachableReduction C := by
  classical
  by_cases hdone : HasReachableReduction C
  · exact hdone
  have degreeC {v : V} (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_4_positive C hv with hdegree | hptr | hce
    · exact hdegree
    · exact (hdone (.of_current_ptr C hptr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {p q : Fin 4} (hpq : p ≠ q) :
      (![a, b, c, d] p) ≠ (![a, b, c, d] q) := hinj.ne hpq
  have edge (p q : Fin 4)
      (hpq : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj p q) :
      G.Adj (![a, b, c, d] p) (![a, b, c, d] q) := (hedge p q).mp hpq
  have hab : G.Adj a b := edge 0 1 (by native_decide)
  have hbc : G.Adj b c := edge 1 2 (by native_decide)
  have hcd : G.Adj c d := edge 2 3 (by native_decide)
  have color_ne {u v : V} {cu cv : Color}
      (hu : C.color u = cu) (hv : C.color v = cv) (h : cu ≠ cv) : u ≠ v := by
    intro huv; subst v; simp_all
  have hxi : Q.x ≠ Q.i := fun h => Q.hei (by simpa [h] using Q.hex)
  have hxj : Q.x ≠ Q.j := fun h => Q.hej (by simpa [h] using Q.hex)
  have hyi : Q.y ≠ Q.i := fun h => Q.hei (by simpa [h] using Q.hey)
  have hyj : Q.y ≠ Q.j := fun h => Q.hej (by simpa [h] using Q.hey)
  have hxf : Q.x ≠ Q.f := fun h => hef (by simpa [h] using Q.hex)
  have hyf : Q.y ≠ Q.f := fun h => hef (by simpa [h] using Q.hey)
  by_cases hfd : G.Adj Q.f d
  · obtain ⟨k, hdk, hkc, hkf⟩ :=
      C.exists_third_neighbor (degreeC (Or.inr hd))
        (color_ne hc Q.hf (by decide))
    have hkSide := C.other_neighbor_of_blue_is_redSide hd hc hcd.symm hdk hkc
    have hk : C.color k = .reddish := by
      rcases hkSide with hk | hk
      · exact (hNoRedAtD k hdk hk).elim
      · exact hk
    have hek : ¬ G.Adj Q.e k := fun hek => (hNoShare k hk hek) hdk
    have hxk : Q.x ≠ k := fun h => hek (by simpa [h] using Q.hex)
    have hyk : Q.y ≠ k := fun h => hek (by simpa [h] using Q.hey)
    apply HasReachableReduction.of_current_ptr C
    apply (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
    apply containsPositiveT C.swapSides (a := Q.e) (b := c) (c := d)
      (d := Q.x) (e := Q.y) (f := a) (g := b) (h := Q.f) (i := k)
      (by simp [Q.he]) (by simp [hc]) (by simp [hd])
      (by simp [Q.hx]) (by simp [Q.hy]) (by simp [ha]) (by simp [hb])
      (by simp [Q.hf]) (by simp [hk]) Q.hex Q.hey Q.hbe.symm hcd
      hbc.symm Q.hcf hfd.symm hdk hab hea hef hek
    simp [List.nodup_cons, color_ne Q.he hc (by decide),
      color_ne Q.he hd (by decide), color_ne Q.he Q.hx (by decide),
      color_ne Q.he Q.hy (by decide), color_ne Q.he ha (by decide),
      color_ne Q.he hb (by decide), color_ne Q.he Q.hf (by decide),
      color_ne Q.he hk (by decide), hcd.ne, Q.hxy,
      color_ne hc Q.hx (by decide), color_ne hc Q.hy (by decide),
      color_ne hc ha (by decide), color_ne hc hb (by decide),
      color_ne hc Q.hf (by decide), color_ne hc hk (by decide),
      color_ne hd Q.hx (by decide), color_ne hd Q.hy (by decide),
      color_ne hd ha (by decide), color_ne hd hb (by decide),
      color_ne hd Q.hf (by decide), color_ne hd hk (by decide),
      color_ne Q.hx ha (by decide), color_ne Q.hx hb (by decide),
      hxf, hxk, color_ne Q.hy ha (by decide),
      color_ne Q.hy hb (by decide), hyf, hyk,
      hab.ne, color_ne ha Q.hf (by decide), color_ne ha hk (by decide),
      color_ne hb Q.hf (by decide), color_ne hb hk (by decide), hkf.symm]
  · apply HasReachableReduction.of_current_ptr C
    have hif : Q.i ≠ Q.f := fun h => hfd (by simpa [h] using Q.hdi.symm)
    have hjf : Q.j ≠ Q.f := fun h => hfd (by simpa [h] using Q.hdj.symm)
    apply (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1
    apply containsPositiveU C.swapSides (a := Q.e) (b := d) (c := c)
      (d := Q.x) (e := Q.y) (f := Q.i) (g := Q.j)
      (h := b) (i := a) (j := Q.f)
      (by simp [Q.he]) (by simp [hd]) (by simp [hc])
      (by simp [Q.hx]) (by simp [Q.hy]) (by simp [Q.hi])
      (by simp [Q.hj]) (by simp [hb]) (by simp [ha]) (by simp [Q.hf])
      Q.hex Q.hey Q.hbe.symm hcd.symm Q.hdi Q.hdj hbc.symm Q.hcf hab.symm
      Q.hei Q.hej hea hef
    simp [List.nodup_cons, color_ne Q.he hd (by decide),
      color_ne Q.he hc (by decide), color_ne Q.he Q.hx (by decide),
      color_ne Q.he Q.hy (by decide), color_ne Q.he Q.hi (by decide),
      color_ne Q.he Q.hj (by decide), color_ne Q.he hb (by decide),
      color_ne Q.he ha (by decide), color_ne Q.he Q.hf (by decide),
      hcd.ne.symm, Q.hxy, Q.hij,
      color_ne hd Q.hx (by decide), color_ne hd Q.hy (by decide),
      color_ne hd Q.hi (by decide), color_ne hd Q.hj (by decide),
      color_ne hd hb (by decide), color_ne hd ha (by decide),
      color_ne hd Q.hf (by decide), color_ne hc Q.hx (by decide),
      color_ne hc Q.hy (by decide), color_ne hc Q.hi (by decide),
      color_ne hc Q.hj (by decide), color_ne hc hb (by decide),
      color_ne hc ha (by decide), color_ne hc Q.hf (by decide),
      hxi, hxj, hyi, hyj, color_ne Q.hx hb (by decide),
      color_ne Q.hx ha (by decide), color_ne Q.hy hb (by decide),
      color_ne Q.hy ha (by decide), color_ne Q.hi hb (by decide),
      color_ne Q.hi ha (by decide), color_ne Q.hj hb (by decide),
      color_ne Q.hj ha (by decide), hxf, hyf, hif, hjf, hab.ne.symm,
      color_ne hb Q.hf (by decide), color_ne ha Q.hf (by decide)]

end Subcubic
