import Subcubic.Lemma5_13.Case4ExactNoRedCE

/-! Lemma 5.13, assembly of Case (4.4.3.3.2) when `i` has degree three. -/

namespace Subcubic

set_option linter.unusedSimpArgs false

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The five overlap alternatives in Case (4.4.3.3.2), under the paper's
temporary degree-three assumption for `i`. -/
theorem lemma5_13_case4_exact_no_red_degree_three
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
    (hgx : G.Adj Q.g x) (hgh : G.Adj Q.g h)
    (hxh : x ≠ h) (hdh : G.Adj d h) (hds : G.Adj d s)
    (hsh : s ≠ h) (hih : G.Adj i h)
    (hideg : vertexDegree G i = 3)
    (hUniqueDG : ∀ z, C.color z = .reddish →
      G.Adj Q.g z → G.Adj d z → z = h)
    (hNoRedI : ∀ z, G.Adj i z → C.color z ≠ .red) :
    HasReachableNegativeReduction C := by
  classical
  dsimp [FormsInducedPath4] at hpath
  rcases hpath with ⟨hinj, hedge⟩
  have hp : FormsInducedPath4 G a b c d := ⟨hinj, hedge⟩
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
  obtain ⟨u, v, hiu, hiv, huh, hvh, huv⟩ :=
    exists_two_other_neighbors_of_degree_three hideg hih
  have hu : C.color u = .reddish := by
    cases hcu : C.color u with
    | red => exact (hNoRedI u hiu hcu).elim
    | reddish => rfl
    | blue => exact (C.bluish_not_adj_blueSide hi (Or.inl hcu) hiu).elim
    | bluish => exact (C.bluish_not_adj_blueSide hi (Or.inr hcu) hiu).elim
  have hvv : C.color v = .reddish := by
    cases hcv : C.color v with
    | red => exact (hNoRedI v hiv hcv).elim
    | reddish => rfl
    | blue => exact (C.bluish_not_adj_blueSide hi (Or.inl hcv) hiv).elim
    | bluish => exact (C.bluish_not_adj_blueSide hi (Or.inr hcv) hiv).elim
  have hic : ¬ G.Adj i c := C.bluish_not_adj_blueSide hi (Or.inl hc)
  have hid : ¬ G.Adj i d := C.bluish_not_adj_blueSide hi (Or.inl hd)
  have hia : ¬ G.Adj i a := fun h => hNoRedI a h ha
  have hib : ¬ G.Adj i b := fun h => hNoRedI b h hb
  have hgc : ¬ G.Adj Q.g c := C.bluish_not_adj_blueSide Q.hg (Or.inl hc)
  have hgb : ¬ G.Adj Q.g b := by
    apply not_adj_fourth_neighbor_of_degree_three hgdeg Q.hag.symm hgx hgh
      (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh
      hab.ne.symm (color_ne hb hx (by decide))
      (color_ne hb hh (by decide))
  have hgr : ¬ G.Adj Q.g Q.r := hNoShareEG Q.r Q.hr Q.her
  have hex : ¬ G.Adj Q.e x := fun he => hNoShareEG x hx he hgx
  have heh : ¬ G.Adj Q.e h := fun he => hNoShareDE h hh he hdh
  have hes : ¬ G.Adj Q.e s := fun he => hNoShareDE s hs he hds
  have hdr : ¬ G.Adj d Q.r := hNoShareDE Q.r Q.hr Q.her
  have hgs : ¬ G.Adj Q.g s := by
    intro hgs'
    have e := hUniqueDG s hs hgs' hds
    exact hsh e
  have hdx : ¬ G.Adj d x := by
    intro hdx'
    have e := hUniqueDG x hx hgx hdx'
    exact hxh e
  have hhf : h ≠ Q.f := by
    intro e
    exact hdf (e ▸ hdh)
  have hxf : x ≠ Q.f := by
    intro e
    exact hgf (e ▸ hgx)
  have hsf : s ≠ Q.f := by
    intro e
    exact hdf (e ▸ hds)
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
  have hca : ¬ G.Adj c a := hac
  have notC (z : V) (hz : C.color z = .reddish) (hzf : z ≠ Q.f) :
      ¬ G.Adj c z := by
    apply C.not_adj_fourth_neighbor (Or.inr hc) hbc.symm hcd Q.hcf
    · exact hv (p := (1 : Fin 4)) (q := 3) (by decide)
    · exact color_ne hb Q.hf (by decide)
    · exact color_ne hd Q.hf (by decide)
    · exact color_ne hz hb (by decide)
    · exact color_ne hz hd (by decide)
    · exact hzf
  have notG (z : V) (hz : C.color z = .reddish)
      (hza : z ≠ a) (hzx : z ≠ x) (hzh : z ≠ h) :
      ¬ G.Adj Q.g z := by
    exact not_adj_fourth_neighbor_of_degree_three hgdeg Q.hag.symm hgx hgh
      (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh
      hza hzx hzh
  have notD (z : V) (hz : C.color z = .reddish)
      (hzc : z ≠ c) (hzh : z ≠ h) (hzs : z ≠ s) :
      ¬ G.Adj d z := by
    exact C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hdh hds
      (color_ne hc hh (by decide)) (color_ne hc hs (by decide)) hsh.symm
      hzc hzh hzs
  have notE (z : V) (hz : C.color z = .reddish)
      (hzb : z ≠ b) (hza : z ≠ a) (hzr : z ≠ Q.r) :
      ¬ G.Adj Q.e z := by
    exact not_adj_fourth_neighbor_of_degree_three Q.hedeg Q.hbe.symm
      Q.heaEdge Q.her hab.ne.symm
      (color_ne hb Q.hr (by decide)) (color_ne ha Q.hr (by decide))
      hzb hza hzr
  have notI (z : V) (hz : C.color z = .reddish)
      (hzh : z ≠ h) (hzu : z ≠ u) (hzv : z ≠ v) :
      ¬ G.Adj i z := by
    exact not_adj_fourth_neighbor_of_degree_three hideg hih hiu hiv
      (Ne.symm huh) (Ne.symm hvh) huv
      hzh hzu hzv
  have hig : i ≠ Q.g := by
    intro eig
    subst i
    exact hNoRedI a Q.hag.symm ha
  have hie : i ≠ Q.e := by
    intro e
    subst i
    exact heh hih

  by_cases hdu : G.Adj d u
  · have hdv : ¬ G.Adj d v :=
      C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hdh hdu
        (color_ne hc hh (by decide)) (color_ne hc hu (by decide))
        (Ne.symm huh) (color_ne hvv hc (by decide)) hvh (Ne.symm huv)
    exact lemma5_13_case4_exact_no_red_shared_d C hd hi hh hu hvv
      hdh hdu hih hiu hiv (fun z => hid z.symm) hdv (by
        simp [hih.ne, hiu.ne, hiv.ne, huh, hvh, huv,
          Ne.symm huh, Ne.symm hvh, Ne.symm huv,
          color_ne hd hi (by decide), color_ne hd hh (by decide),
          color_ne hd hu (by decide), color_ne hd hvv (by decide),
          color_ne hi hh (by decide), color_ne hi hu (by decide),
          color_ne hi hvv (by decide)])
  by_cases hdv : G.Adj d v
  · have hdu' : ¬ G.Adj d u :=
      C.not_adj_fourth_neighbor (Or.inr hd) hcd.symm hdh hdv
        (color_ne hc hh (by decide)) (color_ne hc hvv (by decide))
        (Ne.symm hvh) (color_ne hu hc (by decide)) huh huv
    exact lemma5_13_case4_exact_no_red_shared_d C hd hi hh hvv hu
      hdh hdv hih hiv hiu (fun z => hid z.symm) hdu' (by
        simp [hih.ne, hiu.ne, hiv.ne, huh, hvh, huv,
          Ne.symm huh, Ne.symm hvh, Ne.symm huv,
          color_ne hd hi (by decide), color_ne hd hh (by decide),
          color_ne hd hu (by decide), color_ne hd hvv (by decide),
          color_ne hi hh (by decide), color_ne hi hu (by decide),
          color_ne hi hvv (by decide)])

  by_cases hgu : G.Adj Q.g u
  · have hux : u = x := by
      rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
          (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh hgu with e | e | e
      · exact (color_ne hu ha (by decide) e).elim
      · exact e
      · exact (huh e).elim
    have hgv : ¬ G.Adj Q.g v := notG v hvv
        (color_ne hvv ha (by decide))
        (by intro e; exact huv (hux.trans e.symm))
        hvh
    by_cases hif : G.Adj i Q.f
    · rcases neighbor_eq_of_degree_three hideg hih hiu hiv
        (Ne.symm huh) (Ne.symm hvh) huv hif
        with hfEq | hfEq | hfEq
      · exact (hhf hfEq.symm).elim
      · exact (hgf (hfEq.symm ▸ hgu)).elim
      · cases hfEq
        exact lemma5_13_case4_exact_no_red_shared_g_meets_f C ha hb hc hi Q.hg
          hh hu Q.hf hih hiu hif hgh hgu Q.hag.symm Q.hcf hbc.symm hab
          hic hia hib hgc hgf hgb hch
          (notC u hu huv) hca (by
            simp [hih.ne, hiu.ne, hif.ne, hgh.ne, hgu.ne, Q.hag.ne,
              Q.hcf.ne, hbc.ne, hab.ne, huh, huv, hig, hhf,
              Ne.symm huh, Ne.symm huv, Ne.symm hhf,
              color_ne hi hc (by decide),
              color_ne hi hh (by decide), color_ne hi hu (by decide),
              color_ne hi Q.hf (by decide), color_ne hi ha (by decide),
              color_ne hi hb (by decide), color_ne Q.hg hc (by decide),
              color_ne Q.hg hh (by decide), color_ne Q.hg hu (by decide),
              color_ne Q.hg Q.hf (by decide), color_ne Q.hg ha (by decide),
              color_ne Q.hg hb (by decide), color_ne hc hh (by decide),
              color_ne hc hu (by decide), color_ne hc Q.hf (by decide),
              color_ne hc ha (by decide), color_ne hc hb (by decide),
              color_ne hh ha (by decide), color_ne hh hb (by decide),
              color_ne hu ha (by decide), color_ne hu hb (by decide),
              color_ne Q.hf ha (by decide), color_ne Q.hf hb (by decide)])
    · have huf : u ≠ Q.f := fun e => hgf (e ▸ hgu)
      have hvf : v ≠ Q.f := fun e => hif (e ▸ hiv)
      have hcu := notC u hu huf
      exact lemma5_13_case4_exact_no_red_shared_g_avoids_f C ha hb hc hi Q.hg
        hvv hh hu Q.hf hiv hih hiu hgh hgu Q.hag.symm hbc.symm Q.hcf hab
        hic hia hib hif hgc hgv hgb hgf (notC v hvv
          (by intro e; subst v; exact hif hiv)) hch
        (notC u hu huf) hca (by
          simp [hih.ne, hiu.ne, hiv.ne, huv, hgh.ne, hgu.ne, Q.hag.ne,
            hab.ne, Q.hcf.ne, hif, hig, huh, hvh,
            Ne.symm huh, Ne.symm hvh, Ne.symm huv, huf, hvf,
            hhf, Ne.symm hhf,
            color_ne hi hc (by decide),
            color_ne hi hh (by decide), color_ne hi hu (by decide),
            color_ne hi hvv (by decide), color_ne hi ha (by decide),
            color_ne hi hb (by decide), color_ne hi Q.hf (by decide),
            color_ne Q.hg hc (by decide), color_ne Q.hg hh (by decide),
            color_ne Q.hg hu (by decide), color_ne Q.hg hvv (by decide),
            color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
            color_ne Q.hg Q.hf (by decide), color_ne hc hh (by decide),
            color_ne hc hu (by decide), color_ne hc hvv (by decide),
            color_ne hc ha (by decide), color_ne hc hb (by decide),
            color_ne hc Q.hf (by decide), color_ne hh ha (by decide),
            color_ne hh hb (by decide), color_ne hu ha (by decide),
            color_ne hu hb (by decide), color_ne hvv ha (by decide),
            color_ne hvv hb (by decide), color_ne ha Q.hf (by decide),
            color_ne hb Q.hf (by decide)])
  by_cases hgv : G.Adj Q.g v
  · have hvx : v = x := by
      rcases neighbor_eq_of_degree_three hgdeg Q.hag.symm hgx hgh
          (color_ne ha hx (by decide)) (color_ne ha hh (by decide)) hxh hgv with e | e | e
      · exact (color_ne hvv ha (by decide) e).elim
      · exact e
      · exact (hvh e).elim
    by_cases hif : G.Adj i Q.f
    · rcases neighbor_eq_of_degree_three hideg hih hiu hiv
          (Ne.symm huh) (Ne.symm hvh) huv hif
          with hfEq | hfEq | hfEq
      · exact (hhf hfEq.symm).elim
      · cases hfEq
        exact lemma5_13_case4_exact_no_red_shared_g_meets_f C ha hb hc hi Q.hg
          hh hvv Q.hf hih hiv hif hgh hgv Q.hag.symm Q.hcf hbc.symm hab
          hic hia hib hgc hgf hgb hch
          (notC v hvv (Ne.symm huv)) hca (by
            simp [hih.ne, hiv.ne, hif.ne, hgh.ne, hgv.ne, Q.hag.ne,
              Q.hcf.ne, hbc.ne, hab.ne, hvh, huv, hig, hhf,
              Ne.symm hvh, Ne.symm huv, Ne.symm hhf,
              color_ne hi hc (by decide),
              color_ne hi hh (by decide), color_ne hi hvv (by decide),
              color_ne hi Q.hf (by decide), color_ne hi ha (by decide),
              color_ne hi hb (by decide), color_ne Q.hg hc (by decide),
              color_ne Q.hg hh (by decide), color_ne Q.hg hvv (by decide),
              color_ne Q.hg Q.hf (by decide), color_ne Q.hg ha (by decide),
              color_ne Q.hg hb (by decide), color_ne hc hh (by decide),
              color_ne hc hvv (by decide), color_ne hc Q.hf (by decide),
              color_ne hc ha (by decide), color_ne hc hb (by decide),
              color_ne hh ha (by decide), color_ne hh hb (by decide),
              color_ne hvv ha (by decide), color_ne hvv hb (by decide),
              color_ne Q.hf ha (by decide), color_ne Q.hf hb (by decide)])
      · exact (hgf (hfEq.symm ▸ hgv)).elim
    · have huf : u ≠ Q.f := fun e => hif (e ▸ hiu)
      have hvf : v ≠ Q.f := fun e => hgf (e ▸ hgv)
      exact lemma5_13_case4_exact_no_red_shared_g_avoids_f C ha hb hc hi Q.hg
        hu hh hvv Q.hf hiu hih hiv hgh hgv Q.hag.symm hbc.symm Q.hcf hab
        hic hia hib hif hgc hgu hgb hgf
        (notC u hu huf) hch
        (notC v hvv hvf) hca (by
          simp [hih.ne, hiu.ne, hiv.ne, huv, hgh.ne, hgv.ne,
            Q.hag.ne, hab.ne, Q.hcf.ne, hif, hig, huh, hvh,
            Ne.symm huh, Ne.symm hvh, Ne.symm huv, huf, hvf, hhf, Ne.symm hhf,
            color_ne hi hc (by decide),
            color_ne hi hu (by decide), color_ne hi hh (by decide),
            color_ne hi hvv (by decide), color_ne hi ha (by decide),
            color_ne hi hb (by decide), color_ne hi Q.hf (by decide),
            color_ne Q.hg hc (by decide), color_ne Q.hg hu (by decide),
            color_ne Q.hg hh (by decide), color_ne Q.hg hvv (by decide),
            color_ne Q.hg ha (by decide), color_ne Q.hg hb (by decide),
            color_ne Q.hg Q.hf (by decide), color_ne hc hu (by decide),
            color_ne hc hh (by decide), color_ne hc hvv (by decide),
            color_ne hc ha (by decide), color_ne hc hb (by decide),
            color_ne hc Q.hf (by decide), color_ne hu ha (by decide),
            color_ne hu hb (by decide), color_ne hh ha (by decide),
            color_ne hh hb (by decide), color_ne hvv ha (by decide),
            color_ne hvv hb (by decide), color_ne ha Q.hf (by decide),
            color_ne hb Q.hf (by decide)])

  by_cases hif : G.Adj i Q.f
  · have hfCases := neighbor_eq_of_degree_three hideg hih hiu hiv
        (Ne.symm huh) (Ne.symm hvh) huv hif
    rcases hfCases with hfEq | hfEq | hfEq
    · exact (hhf hfEq.symm).elim
    · cases hfEq
      have hxu : x ≠ Q.f := fun e => hgu (e.symm ▸ hgx)
      have hxv : x ≠ v := fun e => hgv (e.symm ▸ hgx)
      exact lemma5_13_case4_exact_no_red_meets_f C ha hb hc hi Q.hg hvv hx hh
        Q.hf hiv hih hiu hgx hgh Q.hag.symm Q.hcf hbc.symm hab hic
        (notI x hx hxh hxu hxv) hia hib hgc hgv hgf hgb
        (notC v hvv (Ne.symm huv)) hcx hch hca (by
          simp [hih.ne, hiu.ne, hiv.ne, huv, hgx.ne, hgh.ne,
            Q.hag.ne, Q.hcf.ne, hab.ne, hgf, hig, huh, hvh,
            Ne.symm huh, Ne.symm hvh, Ne.symm huv, hxu, hxv,
            Ne.symm hxv, hxh, hhf, Ne.symm hhf,
            color_ne hi hc (by decide),
            color_ne hi hvv (by decide), color_ne hi hx (by decide),
            color_ne hi hh (by decide), color_ne hi Q.hf (by decide),
            color_ne hi ha (by decide), color_ne hi hb (by decide),
            color_ne Q.hg hc (by decide), color_ne Q.hg hvv (by decide),
            color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
            color_ne Q.hg Q.hf (by decide), color_ne Q.hg ha (by decide),
            color_ne Q.hg hb (by decide), color_ne hc hvv (by decide),
            color_ne hc hx (by decide), color_ne hc hh (by decide),
            color_ne hc Q.hf (by decide), color_ne hc ha (by decide),
            color_ne hc hb (by decide), color_ne hvv ha (by decide),
            color_ne hvv hb (by decide), color_ne hx ha (by decide),
            color_ne hx hb (by decide), color_ne hh ha (by decide),
            color_ne hh hb (by decide), color_ne Q.hf ha (by decide),
            color_ne Q.hf hb (by decide)])
    · cases hfEq
      have hxv : x ≠ Q.f := fun e => hgv (e.symm ▸ hgx)
      have hxu : x ≠ u := fun e => hgu (e.symm ▸ hgx)
      exact lemma5_13_case4_exact_no_red_meets_f C ha hb hc hi Q.hg hu hx hh
        Q.hf hiu hih hiv hgx hgh Q.hag.symm Q.hcf hbc.symm hab hic
        (notI x hx hxh hxu hxv) hia hib hgc hgu hgf hgb
        (notC u hu huv) hcx hch hca (by
          simp [hih.ne, hiu.ne, hiv.ne, huv, hgx.ne, hgh.ne,
            Q.hag.ne, Q.hcf.ne, hab.ne, hgf, hig, huh, hvh,
            Ne.symm huh, Ne.symm hvh, Ne.symm huv, hxu, hxv,
            Ne.symm hxu, hxh, hhf, Ne.symm hhf,
            color_ne hi hc (by decide),
            color_ne hi hu (by decide), color_ne hi hx (by decide),
            color_ne hi hh (by decide), color_ne hi Q.hf (by decide),
            color_ne hi ha (by decide), color_ne hi hb (by decide),
            color_ne Q.hg hc (by decide), color_ne Q.hg hu (by decide),
            color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
            color_ne Q.hg Q.hf (by decide), color_ne Q.hg ha (by decide),
            color_ne Q.hg hb (by decide), color_ne hc hu (by decide),
            color_ne hc hx (by decide), color_ne hc hh (by decide),
            color_ne hc Q.hf (by decide), color_ne hc ha (by decide),
            color_ne hc hb (by decide), color_ne hu ha (by decide),
            color_ne hu hb (by decide), color_ne hx ha (by decide),
            color_ne hx hb (by decide), color_ne hh ha (by decide),
            color_ne hh hb (by decide), color_ne Q.hf ha (by decide),
            color_ne Q.hf hb (by decide)])

  by_cases heu : G.Adj Q.e u
  · have hur : u = Q.r := by
      rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm Q.heaEdge Q.her
          hab.ne.symm (color_ne hb Q.hr (by decide))
          (color_ne ha Q.hr (by decide)) heu with e | e | e
      · exact (color_ne hu hb (by decide) e).elim
      · exact (color_ne hu ha (by decide) e).elim
      · exact e
    have hvr : v ≠ Q.r := fun e => huv (hur.trans e.symm)
    have hsu : s ≠ u := fun e => hdu (e ▸ hds)
    have hsv : s ≠ v := fun e => hdv (e ▸ hds)
    exact lemma5_13_case4_exact_no_red_shared_e C ha hb hd hi Q.he hvv hh hu hs
      hiv hih hiu heu Q.heaEdge Q.hbe.symm hdh hds hab hid hia hib
      (notI s hs hsh hsu hsv)
      (C.bluish_not_adj_blueSide Q.he (Or.inl hd))
      (notE v hvv (color_ne hvv hb (by decide)) (color_ne hvv ha (by decide))
        hvr) heh hes hdv hdu
      (by simpa using nonedge 3 0 (by native_decide))
      (by simpa using nonedge 3 1 (by native_decide)) (by
        simp [hih.ne, hiu.ne, hiv.ne, huv, heu.ne, Q.heaEdge.ne,
          Q.hbe.ne, hdh.ne, hds.ne, hab.ne, hie, hsh, huh, hvh,
          Ne.symm hsh, Ne.symm huh, Ne.symm hvh, Ne.symm huv,
          hsu, hsv, Ne.symm hsu, Ne.symm hsv,
          color_ne ha hs (by decide), color_ne hb hs (by decide),
          color_ne hi hd (by decide),
          color_ne hi hvv (by decide), color_ne hi hh (by decide),
          color_ne hi hu (by decide), color_ne hi ha (by decide),
          color_ne hi hb (by decide), color_ne hi hs (by decide),
          color_ne Q.he hd (by decide), color_ne Q.he hvv (by decide),
          color_ne Q.he hh (by decide), color_ne Q.he hu (by decide),
          color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
          color_ne Q.he hs (by decide), color_ne hd hvv (by decide),
          color_ne hd hh (by decide), color_ne hd hu (by decide),
          color_ne hd ha (by decide), color_ne hd hb (by decide),
          color_ne hd hs (by decide), color_ne hvv ha (by decide),
          color_ne hvv hb (by decide), color_ne hh ha (by decide),
          color_ne hh hb (by decide), color_ne hu ha (by decide),
          color_ne hu hb (by decide), color_ne hs ha (by decide),
          color_ne hs hb (by decide)])
  by_cases hev : G.Adj Q.e v
  · have hvr : v = Q.r := by
      rcases neighbor_eq_of_degree_three Q.hedeg Q.hbe.symm Q.heaEdge Q.her
          hab.ne.symm (color_ne hb Q.hr (by decide))
          (color_ne ha Q.hr (by decide)) hev with e | e | e
      · exact (color_ne hvv hb (by decide) e).elim
      · exact (color_ne hvv ha (by decide) e).elim
      · exact e
    have hur : u ≠ Q.r := fun e => huv (e.trans hvr.symm)
    have hsu : s ≠ u := fun e => hdu (e ▸ hds)
    have hsv : s ≠ v := fun e => hdv (e ▸ hds)
    exact lemma5_13_case4_exact_no_red_shared_e C ha hb hd hi Q.he hu hh hvv hs
      hiu hih hiv hev Q.heaEdge Q.hbe.symm hdh hds hab hid hia hib
      (notI s hs hsh hsu hsv)
      (C.bluish_not_adj_blueSide Q.he (Or.inl hd))
      (notE u hu (color_ne hu hb (by decide)) (color_ne hu ha (by decide))
        hur) heh hes hdu hdv
      (by simpa using nonedge 3 0 (by native_decide))
      (by simpa using nonedge 3 1 (by native_decide)) (by
        simp [hih.ne, hiu.ne, hiv.ne, huv, hev.ne, Q.heaEdge.ne,
          Q.hbe.ne, hdh.ne, hds.ne, hab.ne, hie, hsh, huh, hvh,
          Ne.symm hsh, Ne.symm huh, Ne.symm hvh, Ne.symm huv,
          hsu, hsv, Ne.symm hsu, Ne.symm hsv,
          color_ne ha hs (by decide), color_ne hb hs (by decide),
          color_ne hi hd (by decide),
          color_ne hi hu (by decide), color_ne hi hh (by decide),
          color_ne hi hvv (by decide), color_ne hi ha (by decide),
          color_ne hi hb (by decide), color_ne hi hs (by decide),
          color_ne Q.he hd (by decide), color_ne Q.he hu (by decide),
          color_ne Q.he hh (by decide), color_ne Q.he hvv (by decide),
          color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
          color_ne Q.he hs (by decide), color_ne hd hu (by decide),
          color_ne hd hh (by decide), color_ne hd hvv (by decide),
          color_ne hd ha (by decide), color_ne hd hb (by decide),
          color_ne hd hs (by decide), color_ne hu ha (by decide),
          color_ne hu hb (by decide), color_ne hh ha (by decide),
          color_ne hh hb (by decide), color_ne hvv ha (by decide),
          color_ne hvv hb (by decide), color_ne hs ha (by decide),
          color_ne hs hb (by decide)])

  have hux : u ≠ x := fun eq => hgu (eq.symm ▸ hgx)
  have hvx : v ≠ x := fun eq => hgv (eq.symm ▸ hgx)
  have hur : u ≠ Q.r := fun eq => heu (eq.symm ▸ Q.her)
  have hvr : v ≠ Q.r := fun eq => hev (eq.symm ▸ Q.her)
  have huf : u ≠ Q.f := fun eq => hif (eq ▸ hiu)
  have hvf : v ≠ Q.f := fun eq => hif (eq ▸ hiv)
  have hus : u ≠ s := fun eq => hdu (eq ▸ hds)
  have hvs : v ≠ s := fun eq => hdv (eq ▸ hds)
  have hxr : x ≠ Q.r := fun eq => hex (eq.symm ▸ Q.her)
  have hxs : x ≠ s := fun eq => hdx (eq ▸ hds)
  have hhr : h ≠ Q.r := fun eq => heh (eq.symm ▸ Q.her)
  have hhs : h ≠ s := hsh.symm
  have hrf : Q.r ≠ Q.f := fun eq => Q.hef (eq ▸ Q.her)
  have hrs : Q.r ≠ s := fun eq => hes (eq ▸ Q.her)
  have hfs : Q.f ≠ s := hsf.symm
  have hix : ¬ G.Adj i x := notI x hx hxh hux.symm hvx.symm
  have hir : ¬ G.Adj i Q.r := notI Q.r Q.hr hhr.symm hur.symm hvr.symm
  have his : ¬ G.Adj i s := notI s hs hsh hus.symm hvs.symm
  exact lemma5_13_case4_exact_no_overlap C ha hb hc hd Q hh hi hu hvv hx hs
    hih hiu hiv Q.hag.symm hgx hgh hcd hdh hds hbc hab
    hix hir hif his hgu hgv hgr hgf hgs heu hev hex heh hes (by
      simp [hih.ne, hiu.ne, hiv.ne, huv, Q.hag.ne, hgx.ne, hgh.ne,
        hcd.ne, hdh.ne, hds.ne, hbc.ne, hab.ne, Q.her.ne,
        Q.heaEdge.ne, Q.hbe.ne, Q.hcf.ne, Q.hef, hig, hie, Q.hge,
        color_ne hi hc (by decide), color_ne hi hd (by decide),
        color_ne hi hu (by decide), color_ne hi hvv (by decide),
        color_ne hi hx (by decide), color_ne hi hh (by decide),
        color_ne hi Q.hr (by decide), color_ne hi ha (by decide),
        color_ne hi hb (by decide), color_ne hi Q.hf (by decide),
        color_ne hi hs (by decide),
        color_ne Q.hg hc (by decide), color_ne Q.hg hd (by decide),
        color_ne Q.hg hu (by decide), color_ne Q.hg hvv (by decide),
        color_ne Q.hg hx (by decide), color_ne Q.hg hh (by decide),
        color_ne Q.hg Q.hr (by decide), color_ne Q.hg ha (by decide),
        color_ne Q.hg hb (by decide), color_ne Q.hg Q.hf (by decide),
        color_ne Q.hg hs (by decide), color_ne Q.he hc (by decide),
        color_ne Q.he hd (by decide), color_ne Q.he hu (by decide),
        color_ne Q.he hvv (by decide), color_ne Q.he hx (by decide),
        color_ne Q.he hh (by decide), color_ne Q.he Q.hr (by decide),
        color_ne Q.he ha (by decide), color_ne Q.he hb (by decide),
        color_ne Q.he Q.hf (by decide), color_ne Q.he hs (by decide),
        color_ne hc hu (by decide), color_ne hc hvv (by decide),
        color_ne hc hx (by decide), color_ne hc hh (by decide),
        color_ne hc Q.hr (by decide), color_ne hc ha (by decide),
        color_ne hc hb (by decide), color_ne hc Q.hf (by decide),
        color_ne hc hs (by decide),
        color_ne hd hu (by decide), color_ne hd hvv (by decide),
        color_ne hd hx (by decide), color_ne hd hh (by decide),
        color_ne hd Q.hr (by decide), color_ne hd ha (by decide),
        color_ne hd hb (by decide), color_ne hd Q.hf (by decide),
        color_ne hd hs (by decide),
        color_ne hu ha (by decide), color_ne hu hb (by decide),
        color_ne hvv ha (by decide), color_ne hvv hb (by decide),
        color_ne hx ha (by decide), color_ne hx hb (by decide),
        color_ne hh ha (by decide), color_ne hh hb (by decide),
        color_ne Q.hr ha (by decide), color_ne Q.hr hb (by decide),
        color_ne ha Q.hf (by decide), color_ne ha hs (by decide),
        color_ne hb Q.hf (by decide), color_ne hb hs (by decide),
        hux, hvx, huh, hvh, hur, hvr, huf, hvf, hus, hvs,
        hxr, hxh, hxf, hxs, hhr, hhf, hhs, hrf, hrs, hfs,
        hsh, hdx, hgs, hgr, hgf, hex, heh, hes, hdr, hdf,
        hdu, hdv, hgu, hgv, heu, hev, hif])

end Subcubic
