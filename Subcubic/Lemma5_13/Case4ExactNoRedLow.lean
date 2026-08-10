import Subcubic.Lemma5_13.Case4ExactLowH

/-! Degree-one and degree-two versions of Lemma 5.13, Case (4.4.3.3.2). -/

namespace Subcubic

set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem lemma5_13_case4_exact_no_red_low_degree
    (C : GoodColoring G) {a b c d : V}
    (hpath : FormsInducedPath4 G a b c d)
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .blue) (hd : C.color d = .blue)
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
    (hgx : G.Adj Q.g x) (hgh : G.Adj Q.g h) (hxh : x ≠ h)
    (hdh : G.Adj d h) (hds : G.Adj d s) (hsh : s ≠ h)
    (hih : G.Adj i h)
    (hUniqueDG : ∀ z, C.color z = .reddish →
      G.Adj Q.g z → G.Adj d z → z = h)
    (hNoRedI : ∀ z, G.Adj i z → C.color z ≠ .red)
    (hideg : vertexDegree G i = 1 ∨ vertexDegree G i = 2) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hv {p q : Fin 4} (hpq : p ≠ q) :
      (![a, b, c, d] p) ≠ (![a, b, c, d] q) := hinj.ne hpq
  have edge (p q : Fin 4)
      (hpq : (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj p q) :
      G.Adj (![a, b, c, d] p) (![a, b, c, d] q) := (hedge p q).mp hpq
  have nonedge (p q : Fin 4)
      (hpq : ¬ (graphOfEdges [(0, 1), (1, 2), (2, 3)]).Adj p q) :
      ¬ G.Adj (![a, b, c, d] p) (![a, b, c, d] q) :=
    fun h => hpq ((hedge p q).mpr h)
  have hab : G.Adj a b := by simpa using edge 0 1 (by native_decide)
  have hbc : G.Adj b c := by simpa using edge 1 2 (by native_decide)
  have hcd : G.Adj c d := by simpa using edge 2 3 (by native_decide)
  have hac : ¬ G.Adj c a := by simpa using nonedge 2 0 (by native_decide)
  have color_ne {p q : V} {cp cq : Color}
      (hp : C.color p = cp) (hq : C.color q = cq) (hne : cp ≠ cq) : p ≠ q := by
    intro e; subst q; simp_all
  have hic : ¬ G.Adj i c := C.bluish_not_adj_blueSide hi (Or.inl hc)
  have hia : ¬ G.Adj i a := fun z => hNoRedI a z ha
  have hib : ¬ G.Adj i b := fun z => hNoRedI b z hb
  have hgc : ¬ G.Adj Q.g c := C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
  have hgb : ¬ G.Adj Q.g b := by
    apply not_adj_fourth_neighbor_of_degree_three hgdeg Q.hag.symm hgx hgh
      (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh
      hab.ne.symm (color_ne hb hx (by decide))
      (color_ne hb hh (by decide))
  have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
  have hex : ¬ G.Adj Q.e x := fun hex => hNoShareEG x hx hex hgx
  have heh : ¬ G.Adj Q.e h := fun heh => hNoShareDE h hh heh hdh
  have hes : ¬ G.Adj Q.e s := fun hes => hNoShareDE s hs hes hds
  have hgs : ¬ G.Adj Q.g s := by
    intro z
    exact hsh (hUniqueDG s hs z hds)
  have hdx : ¬ G.Adj d x := by
    intro z
    exact hxh (hUniqueDG x hx hgx z)
  have hch : ¬ G.Adj c h := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hbc.symm hcd Q.hcf
    · exact hv (p := (1 : Fin 4)) (q := 3) (by decide)
    · exact color_ne hb Q.hf (by decide)
    · exact color_ne hd Q.hf (by decide)
    · exact color_ne hh hb (by decide)
    · exact color_ne hh hd (by decide)
    · intro e; subst h; exact hdf hdh
  have hcx : ¬ G.Adj c x := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hbc.symm hcd Q.hcf
    · exact hv (p := (1 : Fin 4)) (q := 3) (by decide)
    · exact color_ne hb Q.hf (by decide)
    · exact color_ne hd Q.hf (by decide)
    · exact color_ne hx hb (by decide)
    · exact color_ne hx hd (by decide)
    · intro e; subst x; exact hgf hgx
  have hdr : ¬ G.Adj d Q.r := hNoShareDE Q.r Q.hr Q.her

  have emitAnMinus2 (hdeg1 : vertexDegree G i = 1) :
      HasReachableNegativeReduction C := by
    have onlyI {z : V} (hiz : G.Adj i z) : z = h := by
      exact neighbor_eq_of_degree_one hdeg1 hih hiz
    have hix : ¬ G.Adj i x := fun z => hxh (onlyI z)
    have hhr : h ≠ Q.r := fun e => heh (e.symm ▸ Q.her)
    have hhf : h ≠ Q.f := fun e => hdf (e.symm ▸ hdh)
    have hir : ¬ G.Adj i Q.r := fun z => hhr (onlyI z).symm
    have hif : ¬ G.Adj i Q.f := fun z => hhf (onlyI z).symm
    have his : ¬ G.Adj i s := fun z => hsh (onlyI z)
    have hig : i ≠ Q.g := fun e => hia (e ▸ Q.hag.symm)
    have hie : i ≠ Q.e := fun e => hia (e ▸ Q.heaEdge)
    have hxr : x ≠ Q.r := fun e => hex (e.symm ▸ Q.her)
    have hxf : x ≠ Q.f := fun e => hgf (e.symm ▸ hgx)
    have hxs : x ≠ s := fun e => hgs (e ▸ hgx)
    have hrs : Q.r ≠ s := fun e => hes (e ▸ Q.her)
    have hrf : Q.r ≠ Q.f := fun e => Q.hef (e ▸ Q.her)
    have hfs : Q.f ≠ s := fun e => hdf (e ▸ hds)
    have hn : [i, Q.g, Q.e, c, d, x, h, Q.r, a, b, Q.f, s].Nodup := by
      simp [hih.ne, Q.hag.ne, hgx.ne, hgh.ne, Q.her.ne,
        Q.heaEdge.ne, Q.hbe.ne, hcd.ne, hbc.ne, hab.ne, Q.hcf.ne,
        hdh.ne, hds.ne, hxh, hsh, hsh.symm, Q.hef, hgf,
        hig, hie, Q.hge, hxr, hxf, hxs, hhr, hhf, hrs, hrf, hfs,
        color_ne hi hc (by decide), color_ne hi hd (by decide),
        color_ne hi hx (by decide), color_ne hi hh (by decide),
        color_ne hi Q.hr (by decide), color_ne hi ha (by decide),
        color_ne hi hb (by decide), color_ne hi Q.hf (by decide),
        color_ne hi hs (by decide),
        color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
        color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
        color_ne Q.hg Q.hr (by decide), color_ne Q.hg ha (by decide),
        color_ne Q.hg hb (by decide), color_ne Q.hg Q.hf (by decide),
        color_ne Q.hg hs (by decide), color_ne Q.he hc (by decide),
        color_ne Q.he hd (by decide), color_ne Q.he hx (by decide),
        color_ne Q.he hh (by decide), color_ne Q.he Q.hr (by decide),
        color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
        color_ne Q.he Q.hf (by decide), color_ne Q.he hs (by decide),
        color_ne hc hx (by decide), color_ne hc hh (by decide),
        color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
        color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
        color_ne hc hs (by decide), color_ne hd hx (by decide),
        color_ne hd hh (by decide), color_ne hd Q.hr (by decide),
        color_ne hd ha (by decide), color_ne hd hb (by decide),
        color_ne hd Q.hf (by decide), color_ne hd hs (by decide),
        color_ne hx ha (by decide), color_ne hx hb (by decide),
        color_ne hh ha (by decide), color_ne hh hb (by decide),
        color_ne Q.hr ha (by decide), color_ne Q.hr hb (by decide),
        color_ne ha Q.hf (by decide), color_ne ha hs (by decide),
        color_ne hb Q.hf (by decide), color_ne hb hs (by decide)]
    apply HasReachableNegativeReduction.of_current_ntr C
    apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
    apply containsNegative_of_embedding_with_degree C.swapSides .dcM
      (![i, Q.g, Q.e, c, d, x, h, Q.r, a, b, Q.f, s])
    · change vertexDegree G i = 1
      exact hdeg1
    · have hvec :
          (![i, Q.g, Q.e, c, d, x, h, Q.r, a, b, Q.f, s] : Fin 12 → V) =
            [i, Q.g, Q.e, c, d, x, h, Q.r, a, b, Q.f, s].get := by
        funext z; fin_cases z <;> rfl
      rw [hvec]; exact hn.injective_get
    · intro p q hpq
      apply (negativeTailReducerData .dcM).adj_map_of_edgesMapTo G _ ?_ hpq
      unfold PatternData.EdgesMapTo
      dsimp only [negativeTailReducerData]
      intro e he
      change e ∈ [(0, 6), (1, 5), (1, 6), (1, 8), (2, 7), (2, 8),
        (2, 9), (3, 4), (3, 9), (3, 10), (4, 6), (4, 11), (8, 9)] at he
      simp at he
      rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl)
      · exact hih
      · exact hgx
      · exact hgh
      · exact Q.hag.symm
      · exact Q.her
      · exact Q.heaEdge
      · exact Q.hbe.symm
      · exact hcd
      · exact hbc.symm
      · exact Q.hcf
      · exact hdh
      · exact hds
      · exact hab
    · intro z
      have hcolors : (negativeTailReducer .dcM).color =
          ![.reddish, .reddish, .reddish, .red, .red, .bluish,
            .bluish, .bluish, .blue, .blue, .bluish, .bluish] := by native_decide
      rw [hcolors]
      fin_cases z
      · change (C.color i).swap = .reddish; simp [hi]
      · change (C.color Q.g).swap = .reddish; simp [Q.hg]
      · change (C.color Q.e).swap = .reddish; simp [Q.he]
      · change (C.color c).swap = .red; simp [hc]
      · change (C.color d).swap = .red; simp [hd]
      · change (C.color x).swap = .bluish; simp [hx]
      · change (C.color h).swap = .bluish; simp [hh]
      · change (C.color Q.r).swap = .bluish; simp [Q.hr]
      · change (C.color a).swap = .blue; simp [ha]
      · change (C.color b).swap = .blue; simp [hb]
      · change (C.color Q.f).swap = .bluish; simp [Q.hf]
      · change (C.color s).swap = .bluish; simp [hs]
    · intro p q hpq hnon hauto
      have hp := negativeDcM_boundaryNonedges p q hpq hnon hauto
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
      rcases hp with
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
          (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
           ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      all_goals first
        | exact hix | exact hir | exact hif | exact his
        | exact hgr | exact hgf | exact hgs | exact hex | exact heh
        | exact Q.hef | exact hes
        | exact fun z => hix z.symm | exact fun z => hir z.symm
        | exact fun z => hif z.symm | exact fun z => his z.symm
        | exact fun z => hgr z.symm | exact fun z => hgf z.symm
        | exact fun z => hgs z.symm | exact fun z => hex z.symm
        | exact fun z => heh z.symm | exact fun z => Q.hef z.symm
        | exact fun z => hes z.symm

  rcases hideg with hdeg1 | hdeg2
  · exact emitAnMinus2 hdeg1
  · obtain ⟨u, hiu, huh⟩ := exists_other_neighbor_of_degree_two hdeg2 hih
    have hu : C.color u = .reddish := by
      cases hcu : C.color u with
      | red => exact (hNoRedI u hiu hcu).elim
      | reddish => rfl
      | blue => exact (C.bluish_not_adj_blueSide hi (Or.inl hcu) hiu).elim
      | bluish => exact (C.bluish_not_adj_blueSide hi (Or.inr hcu) hiu).elim
    -- The overlap alternatives are the shortened versions of Figures
    -- 5(e), 5(ab), 5(ac), and 5(ad); if none occurs, Figure 5(an-minus) applies.
    by_cases hdu : G.Adj d u
    · have hdi : ¬ G.Adj d i := C.bluish_not_adj_blueSide hi (Or.inl hd) ∘
          SimpleGraph.Adj.symm
      apply HasReachableNegativeReduction.of_current_ntr C
      apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
      apply containsNegativeDcB C.swapSides
        (by simp [hd]) (by simp [hi]) (by simp [hu]) (by simp [hh]) hdeg2
        hdu hdh hiu hih hdi
      simp [hdu.ne, hiu.ne, hdh.ne, hih.ne, huh,
        color_ne hd hi (by decide), color_ne hd hu (by decide),
        color_ne hd hh (by decide), color_ne hi hu (by decide),
        color_ne hi hh (by decide)]
    · by_cases hgu : G.Adj Q.g u
      · have huf : u ≠ Q.f := by intro e; subst u; exact hgf hgu
        have hig : i ≠ Q.g := fun e => hia (e ▸ Q.hag.symm)
        have hhf : h ≠ Q.f := fun e => hdf (e.symm ▸ hdh)
        have hgf_ne : Q.g ≠ Q.f := fun e => hgc (e.symm ▸ Q.hcf.symm)
        have hif' : ¬ G.Adj i Q.f := by
          intro z
          rcases neighbor_eq_of_degree_two hdeg2 hih hiu huh.symm z with e | e
          · exact hhf e.symm
          · exact huf e.symm
        have hcu : ¬ G.Adj c u := by
          apply C.not_adj_fourth_neighbor (Or.inr hc) hbc.symm hcd Q.hcf
          · exact hv (p := (1 : Fin 4)) (q := 3) (by decide)
          · exact color_ne hb Q.hf (by decide)
          · exact color_ne hd Q.hf (by decide)
          · exact color_ne hu hb (by decide)
          · exact color_ne hu hd (by decide)
          · exact huf
        have hn : [i, Q.g, c, u, h, a, b, Q.f].Nodup := by
          simp [hih.ne, hiu.ne, huh, hgu.ne, hgh.ne, Q.hag.ne,
            hbc.ne, Q.hcf.ne, hab.ne, hgf, hxh,
            hig, huf, hhf, hgf_ne, color_ne hi hc (by decide),
            color_ne hi hu (by decide), color_ne hi hh (by decide),
            color_ne hi ha (by decide), color_ne hi hb (by decide),
            color_ne hi Q.hf (by decide), color_ne Q.hg hc (by decide),
            color_ne Q.hg hu (by decide), color_ne Q.hg hh (by decide),
            color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
            color_ne hc hu (by decide),
            color_ne hc hh (by decide), color_ne hc ha (by decide),
            color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
            color_ne hu ha (by decide), color_ne hu hb (by decide),
            color_ne hh ha (by decide), color_ne hh hb (by decide),
            color_ne ha Q.hf (by decide), color_ne hb Q.hf (by decide)]
        apply HasReachableNegativeReduction.of_current_ntr C
        apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
        apply containsNegative_of_embedding_with_degree C.swapSides .dcI
          (![i, Q.g, c, u, h, a, b, Q.f])
        · change vertexDegree G i = 2
          exact hdeg2
        · have hvec : (![i, Q.g, c, u, h, a, b, Q.f] : Fin 8 → V) =
              [i, Q.g, c, u, h, a, b, Q.f].get := by
            funext z; fin_cases z <;> rfl
          rw [hvec]; exact hn.injective_get
        · intro p q hpq
          apply (negativeTailReducerData .dcI).adj_map_of_edgesMapTo G _ ?_ hpq
          unfold PatternData.EdgesMapTo
          dsimp only [negativeTailReducerData]
          intro e he
          change e ∈ [(0, 3), (0, 4), (1, 3), (1, 4), (1, 5),
            (2, 6), (2, 7), (5, 6)] at he
          simp at he
          rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · exact hiu
          · exact hih
          · exact hgu
          · exact hgh
          · exact Q.hag.symm
          · exact hbc.symm
          · exact Q.hcf
          · exact hab
        · intro z
          have hcolors : (negativeTailReducer .dcI).color =
              ![.reddish, .reddish, .red, .bluish, .bluish,
                .blue, .blue, .bluish] := by native_decide
          rw [hcolors]
          fin_cases z
          · change (C.color i).swap = .reddish; simp [hi]
          · change (C.color Q.g).swap = .reddish; simp [Q.hg]
          · change (C.color c).swap = .red; simp [hc]
          · change (C.color u).swap = .bluish; simp [hu]
          · change (C.color h).swap = .bluish; simp [hh]
          · change (C.color a).swap = .blue; simp [ha]
          · change (C.color b).swap = .blue; simp [hb]
          · change (C.color Q.f).swap = .bluish; simp [Q.hf]
        · intro p q hpq hnon hauto
          have hp := negativeDcI_boundaryNonedges p q hpq hnon hauto
          simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
          rcases hp with
              (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
              (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
               ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
          · exact hic
          · exact hia
          · exact hib
          · exact hif'
          · exact hgc
          · exact hgb
          · exact hgf
          · exact hcu
          · exact hch
          · exact hac
          · exact fun z => hic z.symm
          · exact fun z => hia z.symm
          · exact fun z => hib z.symm
          · exact fun z => hif' z.symm
          · exact fun z => hgc z.symm
          · exact fun z => hgb z.symm
          · exact fun z => hgf z.symm
          · exact fun z => hcu z.symm
          · exact fun z => hch z.symm
          · exact fun z => hac z.symm
      · -- Remaining shortened configurations are assembled in the degree-three
        -- proof after replacing the absent neighbor by the appropriate guarded
        -- `ac/ad/an-minus` pattern.
        by_cases hif : G.Adj i Q.f
        · have hhf : h ≠ Q.f := fun e => hdf (e.symm ▸ hdh)
          have huf : u = Q.f := by
            rcases neighbor_eq_of_degree_two hdeg2 hih hiu
              huh.symm hif with e | e
            · exact (hhf e.symm).elim
            · exact e.symm
          subst u
          have hig : i ≠ Q.g := fun e => hia (e ▸ Q.hag.symm)
          have hxf : x ≠ Q.f := fun e => hgf (e.symm ▸ hgx)
          have hgf_ne : Q.g ≠ Q.f := fun e => hgc (e.symm ▸ Q.hcf.symm)
          have hix : ¬ G.Adj i x := by
            intro z
            rcases neighbor_eq_of_degree_two hdeg2 hih hif hhf z with e | e
            · exact hxh e
            · exact hxf e
          apply HasReachableNegativeReduction.of_current_ntr C
          apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
          apply containsNegative_of_embedding_with_degree C.swapSides .dcJ
            (![i, Q.g, c, x, h, Q.f, a, b])
          · change vertexDegree G i = 2
            exact hdeg2
          · have hvec : (![i, Q.g, c, x, h, Q.f, a, b] : Fin 8 → V) =
                [i, Q.g, c, x, h, Q.f, a, b].get := by
                funext z; fin_cases z <;> rfl
            rw [hvec]
            apply List.Nodup.injective_get
            simp [hih.ne, hif.ne, hgx.ne, hgh.ne, Q.hag.ne, Q.hcf.ne,
              hab.ne, hxh, hgf, hig, hhf, hxf, hgf_ne,
              color_ne hi hc (by decide),
              color_ne hi hx (by decide), color_ne hi hh (by decide),
              color_ne hi ha (by decide),
              color_ne hi hb (by decide), color_ne Q.hg hc (by decide),
              color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
              color_ne Q.hg ha (by decide),
              color_ne Q.hg hb (by decide), color_ne hc hx (by decide),
              color_ne hc hh (by decide), color_ne hc Q.hf (by decide),
              color_ne hc ha (by decide), color_ne hc hb (by decide),
              color_ne hx ha (by decide), color_ne hx hb (by decide),
              color_ne hh ha (by decide), color_ne hh hb (by decide),
              color_ne Q.hf ha (by decide), color_ne Q.hf hb (by decide)]
          · intro p q hpq
            apply (negativeTailReducerData .dcJ).adj_map_of_edgesMapTo G _ ?_ hpq
            unfold PatternData.EdgesMapTo
            dsimp only [negativeTailReducerData]
            intro e he
            change e ∈ [(0, 4), (0, 5), (1, 3), (1, 4), (1, 6),
              (2, 5), (2, 7), (6, 7)] at he
            simp at he
            rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
            · exact hih
            · exact hif
            · exact hgx
            · exact hgh
            · exact Q.hag.symm
            · exact Q.hcf
            · exact hbc.symm
            · exact hab
          · intro z
            have hcolors : (negativeTailReducer .dcJ).color =
                ![.reddish, .reddish, .red, .bluish, .bluish,
                  .bluish, .blue, .blue] := by native_decide
            rw [hcolors]
            fin_cases z
            · change (C.color i).swap = .reddish; simp [hi]
            · change (C.color Q.g).swap = .reddish; simp [Q.hg]
            · change (C.color c).swap = .red; simp [hc]
            · change (C.color x).swap = .bluish; simp [hx]
            · change (C.color h).swap = .bluish; simp [hh]
            · change (C.color Q.f).swap = .bluish; simp [Q.hf]
            · change (C.color a).swap = .blue; simp [ha]
            · change (C.color b).swap = .blue; simp [hb]
          · intro p q hpq hnon hauto
            have hp := negativeDcJ_boundaryNonedges p q hpq hnon hauto
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
            rcases hp with
                (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                 ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                 ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
                (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                 ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                 ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
            all_goals first
              | exact hic | exact hix
              | exact hia | exact hib | exact hgc | exact hgf | exact hgb
              | exact hcx | exact hch | exact hac
              | exact fun z => hic z.symm | exact fun z => hix z.symm
              | exact fun z => hia z.symm | exact fun z => hib z.symm
              | exact fun z => hgc z.symm | exact fun z => hgf z.symm
              | exact fun z => hgb z.symm | exact fun z => hcx z.symm
              | exact fun z => hch z.symm | exact fun z => hac z.symm
        · by_cases heu : G.Adj Q.e u
          · have hdi : ¬ G.Adj d i := C.bluish_not_adj_blueSide hi (Or.inl hd) ∘
                SimpleGraph.Adj.symm
            have hdu' : ¬ G.Adj d u := hdu
            have hie : i ≠ Q.e := fun e => hia (e ▸ Q.heaEdge)
            have hus : u ≠ s := fun e => hdu (e ▸ hds)
            have his : ¬ G.Adj i s := by
              intro z
              rcases neighbor_eq_of_degree_two hdeg2 hih hiu huh.symm z with e | e
              · exact hsh e
              · exact hus e.symm
            have hda : ¬ G.Adj d a := by simpa using nonedge 3 0 (by native_decide)
            have hdb : ¬ G.Adj d b := by simpa using nonedge 3 1 (by native_decide)
            apply HasReachableNegativeReduction.of_current_ntr C
            apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
            apply containsNegative_of_embedding_with_degree C.swapSides .dcK
              (![i, Q.e, d, h, u, a, b, s])
            · change vertexDegree G i = 2
              exact hdeg2
            · have hvec : (![i, Q.e, d, h, u, a, b, s] : Fin 8 → V) =
                  [i, Q.e, d, h, u, a, b, s].get := by
                  funext z; fin_cases z <;> rfl
              rw [hvec]
              apply List.Nodup.injective_get
              simp [hih.ne, hiu.ne, huh, huh.symm, Q.heaEdge.ne, Q.hbe.ne,
                hdh.ne, hds.ne, hab.ne, hsh, hsh.symm, hie, hus,
                color_ne ha hs (by decide), color_ne hb hs (by decide),
                color_ne hi hd (by decide),
                color_ne hi hh (by decide), color_ne hi hu (by decide),
                color_ne hi ha (by decide), color_ne hi hb (by decide),
                color_ne hi hs (by decide), color_ne Q.he hd (by decide),
                color_ne Q.he hh (by decide), color_ne Q.he hu (by decide),
                color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
                color_ne Q.he hs (by decide), color_ne hd hh (by decide),
                color_ne hd hu (by decide), color_ne hd ha (by decide),
                color_ne hd hb (by decide), color_ne hd hs (by decide),
                color_ne hh ha (by decide), color_ne hh hb (by decide),
                color_ne hu ha (by decide), color_ne hu hb (by decide),
                color_ne hs ha (by decide), color_ne hs hb (by decide)]
            · intro p q hpq
              apply (negativeTailReducerData .dcK).adj_map_of_edgesMapTo G _ ?_ hpq
              unfold PatternData.EdgesMapTo
              dsimp only [negativeTailReducerData]
              intro e he
              change e ∈ [(0, 3), (0, 4), (1, 4), (1, 5), (1, 6),
                (2, 3), (2, 7), (5, 6)] at he
              simp at he
              rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
              · exact hih
              · exact hiu
              · exact heu
              · exact Q.heaEdge
              · exact Q.hbe.symm
              · exact hdh
              · exact hds
              · exact hab
            · intro z
              have hcolors : (negativeTailReducer .dcK).color =
                  ![.reddish, .reddish, .red, .bluish, .bluish,
                    .blue, .blue, .bluish] := by native_decide
              rw [hcolors]
              fin_cases z
              · change (C.color i).swap = .reddish; simp [hi]
              · change (C.color Q.e).swap = .reddish; simp [Q.he]
              · change (C.color d).swap = .red; simp [hd]
              · change (C.color h).swap = .bluish; simp [hh]
              · change (C.color u).swap = .bluish; simp [hu]
              · change (C.color a).swap = .blue; simp [ha]
              · change (C.color b).swap = .blue; simp [hb]
              · change (C.color s).swap = .bluish; simp [hs]
            · intro p q hpq hnon hauto
              have hp := negativeDcK_boundaryNonedges p q hpq hnon hauto
              simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hp
              rcases hp with
                  (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
                  (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
              all_goals first
                | exact hdi | exact hia | exact hib | exact his
                | exact C.bluish_not_adj_blueSide Q.he (Or.inl hd)
                | exact heh | exact hes | exact hdu' | exact hda | exact hdb
                | exact fun z => hdi z.symm | exact fun z => hia z.symm
                | exact fun z => hib z.symm | exact fun z => his z.symm
                | exact fun z => (C.bluish_not_adj_blueSide Q.he (Or.inl hd)) z.symm
                | exact fun z => heh z.symm | exact fun z => hes z.symm
                | exact fun z => hdu' z.symm | exact fun z => hda z.symm
                | exact fun z => hdb z.symm
          · -- No overlap: the guarded `an-minus-` pattern.
            have hir : ¬ G.Adj i Q.r := by
              intro z
              rcases neighbor_eq_of_degree_two hdeg2 hih hiu huh.symm z with e | e
              · exact heh (e ▸ Q.her)
              · exact heu (e ▸ Q.her)
            have his : ¬ G.Adj i s := by
              intro z
              rcases neighbor_eq_of_degree_two hdeg2 hih hiu huh.symm z with e | e
              · exact hsh e
              · exact hdu (e ▸ hds)
            have hgu' : ¬ G.Adj Q.g u := hgu
            have hix : ¬ G.Adj i x := by
              intro z
              rcases neighbor_eq_of_degree_two hdeg2 hih hiu huh.symm z with e | e
              · exact hxh e
              · exact hgu (e ▸ hgx)
            have hig : i ≠ Q.g := fun e => hia (e ▸ Q.hag.symm)
            have hie : i ≠ Q.e := fun e => hia (e ▸ Q.heaEdge)
            have hux : u ≠ x := fun e => hgu (e ▸ hgx)
            have hur : u ≠ Q.r := fun e => heu (e.symm ▸ Q.her)
            have huf : u ≠ Q.f := fun e => hif (e ▸ hiu)
            have hus : u ≠ s := fun e => hdu (e ▸ hds)
            have hxr : x ≠ Q.r := fun e => hex (e.symm ▸ Q.her)
            have hxf : x ≠ Q.f := fun e => hgf (e.symm ▸ hgx)
            have hxs : x ≠ s := fun e => hgs (e ▸ hgx)
            have hhr : h ≠ Q.r := fun e => heh (e.symm ▸ Q.her)
            have hhf : h ≠ Q.f := fun e => hdf (e.symm ▸ hdh)
            have hrs : Q.r ≠ s := fun e => hes (e ▸ Q.her)
            have hrf : Q.r ≠ Q.f := fun e => Q.hef (e ▸ Q.her)
            have hfs : Q.f ≠ s := fun e => hdf (e ▸ hds)
            have hn : [i, Q.g, Q.e, c, d, u, x, h, Q.r,
                a, b, Q.f, s].Nodup := by
              simp [hih.ne, hiu.ne, huh, Q.hag.ne, hgx.ne, hgh.ne,
                Q.her.ne, Q.heaEdge.ne, Q.hbe.ne, hcd.ne, hbc.ne,
                hab.ne, Q.hcf.ne, hdh.ne, hds.ne, hxh, hsh, hsh.symm,
                Q.hef, hgf, hif, hig, hie, Q.hge,
                hux, huh, hur, huf, hus, hxr, hxf, hxs, hhr, hhf,
                hrs, hrf, hfs,
                color_ne hi hc (by decide), color_ne hi hd (by decide),
                color_ne hi hu (by decide), color_ne hi hx (by decide),
                color_ne hi hh (by decide), color_ne hi Q.hr (by decide),
                color_ne hi ha (by decide), color_ne hi hb (by decide),
                color_ne hi Q.hf (by decide), color_ne hi hs (by decide),
                color_ne Q.hg hc (by decide),
                color_ne Q.hg hd (by decide), color_ne Q.hg hu (by decide),
                color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
                color_ne Q.hg Q.hr (by decide), color_ne Q.hg ha (by decide),
                color_ne Q.hg hb (by decide), color_ne Q.hg Q.hf (by decide),
                color_ne Q.hg hs (by decide), color_ne Q.he hc (by decide),
                color_ne Q.he hd (by decide), color_ne Q.he hu (by decide),
                color_ne Q.he hx (by decide), color_ne Q.he hh (by decide),
                color_ne Q.he Q.hr (by decide), color_ne Q.he ha (by decide),
                color_ne Q.he hb (by decide), color_ne Q.he Q.hf (by decide),
                color_ne Q.he hs (by decide), color_ne hc hu (by decide),
                color_ne hc hx (by decide), color_ne hc hh (by decide),
                color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
                color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
                color_ne hc hs (by decide), color_ne hd hu (by decide),
                color_ne hd hx (by decide), color_ne hd hh (by decide),
                color_ne hd Q.hr (by decide), color_ne hd ha (by decide),
                color_ne hd hb (by decide), color_ne hd Q.hf (by decide),
                color_ne hd hs (by decide), color_ne hu ha (by decide),
                color_ne hu hb (by decide), color_ne hx ha (by decide),
                color_ne hx hb (by decide), color_ne hh ha (by decide),
                color_ne hh hb (by decide), color_ne Q.hr ha (by decide),
                color_ne Q.hr hb (by decide), color_ne ha Q.hf (by decide),
                color_ne ha hs (by decide), color_ne hb Q.hf (by decide),
                color_ne hb hs (by decide)]
            apply HasReachableNegativeReduction.of_current_ntr C
            apply (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1
            apply containsNegative_of_embedding_with_degree C.swapSides .dcL
              (![i, Q.g, Q.e, c, d, u, x, h, Q.r, a, b, Q.f, s])
            · change vertexDegree G i = 2
              exact hdeg2
            · have hvec :
                  (![i, Q.g, Q.e, c, d, u, x, h, Q.r, a, b, Q.f, s] :
                    Fin 13 → V) =
                    [i, Q.g, Q.e, c, d, u, x, h, Q.r,
                      a, b, Q.f, s].get := by
                  funext z; fin_cases z <;> rfl
              rw [hvec]; exact hn.injective_get
            · intro p q hpq
              apply (negativeTailReducerData .dcL).adj_map_of_edgesMapTo G _ ?_ hpq
              unfold PatternData.EdgesMapTo
              dsimp only [negativeTailReducerData]
              intro e he
              change e ∈ [(0, 5), (0, 7), (1, 6), (1, 7), (1, 9),
                (2, 8), (2, 9), (2, 10), (3, 4), (3, 10), (3, 11),
                (4, 7), (4, 12), (9, 10)] at he
              simp at he
              rcases he with (rfl | rfl | rfl | rfl | rfl | rfl | rfl |
                rfl | rfl | rfl | rfl | rfl | rfl | rfl)
              · exact hiu
              · exact hih
              · exact hgx
              · exact hgh
              · exact Q.hag.symm
              · exact Q.her
              · exact Q.heaEdge
              · exact Q.hbe.symm
              · exact hcd
              · exact hbc.symm
              · exact Q.hcf
              · exact hdh
              · exact hds
              · exact hab
            · intro z
              have hcolors : (negativeTailReducer .dcL).color =
                  ![.reddish, .reddish, .reddish, .red, .red,
                    .bluish, .bluish, .bluish, .bluish,
                    .blue, .blue, .bluish, .bluish] := by native_decide
              rw [hcolors]
              fin_cases z
              · change (C.color i).swap = .reddish; simp [hi]
              · change (C.color Q.g).swap = .reddish; simp [Q.hg]
              · change (C.color Q.e).swap = .reddish; simp [Q.he]
              · change (C.color c).swap = .red; simp [hc]
              · change (C.color d).swap = .red; simp [hd]
              · change (C.color u).swap = .bluish; simp [hu]
              · change (C.color x).swap = .bluish; simp [hx]
              · change (C.color h).swap = .bluish; simp [hh]
              · change (C.color Q.r).swap = .bluish; simp [Q.hr]
              · change (C.color a).swap = .blue; simp [ha]
              · change (C.color b).swap = .blue; simp [hb]
              · change (C.color Q.f).swap = .bluish; simp [Q.hf]
              · change (C.color s).swap = .bluish; simp [hs]
            · intro p q hpq hnon hauto
              have hp := negativeDcL_boundaryNonedges p q hpq hnon hauto
              simp only [List.mem_cons, List.not_mem_nil, or_false,
                Prod.mk.injEq] at hp
              rcases hp with
                  (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩) |
                  (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
                   ⟨rfl, rfl⟩)
              · exact hix
              · exact hir
              · exact hif
              · exact his
              · exact hgu'
              · exact hgr
              · exact hgf
              · exact hgs
              · exact heu
              · exact hex
              · exact heh
              · exact Q.hef
              · exact hes
              · exact fun z => hix z.symm
              · exact fun z => hir z.symm
              · exact fun z => hif z.symm
              · exact fun z => his z.symm
              · exact fun z => hgu' z.symm
              · exact fun z => hgr z.symm
              · exact fun z => hgf z.symm
              · exact fun z => hgs z.symm
              · exact fun z => heu z.symm
              · exact fun z => hex z.symm
              · exact fun z => heh z.symm
              · exact fun z => Q.hef z.symm
              · exact fun z => hes z.symm

end Subcubic
