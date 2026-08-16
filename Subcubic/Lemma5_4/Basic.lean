import Subcubic.NegativeReduction
import Subcubic.NegativeTailReducerWitnesses

/-!
# Lemma 5.4: initial overlap split

This file mirrors the first paragraph of the prose proof.  The four bluish
neighbor occurrences of the isolated red edge overlap in zero, one, or two
vertices.  The zero- and two-overlap cases immediately give `g-` and `c-`.
For one overlap, `ntr-dc-a` handles degree two; the remaining configuration records
the third neighbor needed by the rest of the proof.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_4SharedConfiguration (C : MatchingCutColoring G) (a b : V) where
  c : V
  d : V
  e : V
  f : V
  hc : C.color c = .bluish
  hd : C.color d = .bluish
  he : C.color e = .bluish
  hf : C.color f = .red ∨ C.color f = .reddish
  hac : G.Adj a c
  had : G.Adj a d
  hbd : G.Adj b d
  hbe : G.Adj b e
  hdf : G.Adj d f
  hcd : c ≠ d
  hce : c ≠ e
  hde : d ≠ e
  hfa : f ≠ a
  hfb : f ≠ b
  hdDegree : vertexDegree G d = 3

/-- Exchange the two endpoints of the isolated red edge, together with their
exclusive bluish neighbors.  This packages the only left-right symmetry used
in the later cases of Lemma 5.4. -/
def Lemma5_4SharedConfiguration.reverse {C : MatchingCutColoring G} {a b : V}
    (Q : Lemma5_4SharedConfiguration C a b) :
    Lemma5_4SharedConfiguration C b a where
  c := Q.e
  d := Q.d
  e := Q.c
  f := Q.f
  hc := Q.he
  hd := Q.hd
  he := Q.hc
  hf := Q.hf
  hac := Q.hbe
  had := Q.hbd
  hbd := Q.had
  hbe := Q.hac
  hdf := Q.hdf
  hcd := Q.hde.symm
  hce := Q.hce.symm
  hde := Q.hcd.symm
  hfa := Q.hfb
  hfb := Q.hfa
  hdDegree := Q.hdDegree

private theorem contains_negativeC
    (C : MatchingCutColoring G) {a b c d : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbc : G.Adj b c) (hbd : G.Adj b d) (hcd : c ≠ d) :
    ContainsNegativeTailReducer C := by
  apply containsNegativeC C ha hb hc hd hab hac had hbc hbd
  simp [hab.ne, hac.ne, had.ne, hbc.ne, hbd.ne, hcd]

private theorem contains_negativeG
    (C : MatchingCutColoring G) {a b c d e f : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hc : C.color c = .bluish) (hd : C.color d = .bluish)
    (he : C.color e = .bluish) (hf : C.color f = .bluish)
    (hab : G.Adj a b) (hac : G.Adj a c) (had : G.Adj a d)
    (hbe : G.Adj b e) (hbf : G.Adj b f)
    (hcd : c ≠ d) (hef : e ≠ f)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) :
    ContainsNegativeTailReducer C := by
  apply containsNegativeG C ha hb hc hd he hf hab hac had hbe hbf
  simp [hab.ne, hac.ne, had.ne, hbe.ne, hbf.ne, hcd, hef,
    hce, hcf, hde, hdf,
    vertex_ne_of_color_eq ha he (by decide),
    vertex_ne_of_color_eq ha hf (by decide),
    vertex_ne_of_color_eq hb hc (by decide),
    vertex_ne_of_color_eq hb hd (by decide)]

theorem lemma5_4_initial
    (C : MatchingCutColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (ha_other : ∀ v, G.Adj a v → v ≠ b → C.color v = .bluish)
    (hb_other : ∀ v, G.Adj b v → v ≠ a → C.color v = .bluish) :
    HasReachableNegativeReduction C ∨
      Nonempty (Lemma5_4SharedConfiguration C a b) := by
  by_cases hdone : HasReachableNegativeReduction C
  · exact Or.inl hdone
  have degree_of_color {v : V}
      (hv : C.color v = .red ∨ C.color v = .blue) :
      vertexDegree G v = 3 := by
    rcases lemma3_6_negative C hv with hdegree | hntr | hce
    · exact hdegree
    · exact (hdone (.of_current_ntr C hntr)).elim
    · exact (hdone (.of_current_ce C hce)).elim
  obtain ⟨c, d, hac, had, hcb, hdb, hcd⟩ :=
    C.exists_two_other_neighbors (degree_of_color (Or.inl ha)) hab
  obtain ⟨e, f, hbe, hbf, hea, hfa, hef⟩ :=
    C.exists_two_other_neighbors (degree_of_color (Or.inl hb)) hab.symm
  have hc := ha_other c hac hcb
  have hd := ha_other d had hdb
  have he := hb_other e hbe hea
  have hf := hb_other f hbf hfa
  by_cases hce : c = e
  · subst e
    by_cases hdf : d = f
    · subst f
      exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
        (contains_negativeC C ha hb hc hd hab hac had hbe hbf hcd))
    · have lower : 2 ≤ vertexDegree G c := by
        have hs : ({a, b} : Set V) ⊆ G.neighborSet c := by
          intro z hz
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
          rcases hz with rfl | rfl
          · exact hac.symm
          · exact hbe.symm
        unfold vertexDegree
        simpa [hab.ne] using Set.ncard_le_ncard hs
      by_cases hcdeg2 : vertexDegree G c = 2
      · have hntrSwap := containsNegativeDcA C.swapSides
            (a := c) (b := a) (c := b)
            (by simp [hc]) (by simp [ha]) (by simp [hb]) hcdeg2
            hac.symm hbe.symm hab
            (by simp [List.nodup_cons, hac.ne.symm, hbe.ne.symm, hab.ne])
        exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
          ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap))
      · have hcdeg3 : vertexDegree G c = 3 := by
          have upper := C.subcubic c
          omega
        obtain ⟨g, hcg, hga, hgb⟩ :=
          exists_third_neighbor_of_degree_three hcdeg3 hab.ne
        have hg : C.color g = .red ∨ C.color g = .reddish := by
          cases hgc : C.color g with
          | red => exact Or.inl rfl
          | reddish => exact Or.inr rfl
          | blue => exact (C.bluish_not_adj_blueSide hc (Or.inl hgc) hcg).elim
          | bluish => exact (C.bluish_not_adj_blueSide hc (Or.inr hgc) hcg).elim
        exact Or.inr ⟨⟨d, c, f, g, hd, hc, hf, hg, had, hac, hbe, hbf,
          hcg, hcd.symm, hdf, hef, hga, hgb, hcdeg3⟩⟩
  · by_cases hcf : c = f
    · subst f
      by_cases hde : d = e
      · subst e
        exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
          (contains_negativeC C ha hb hc hd hab hac had hbf hbe hcd))
      · -- One shared vertex, normalized by exchanging `c,d`.
        have lower : 2 ≤ vertexDegree G c := by
          have hs : ({a, b} : Set V) ⊆ G.neighborSet c := by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact hac.symm
            · exact hbf.symm
          unfold vertexDegree
          simpa [hab.ne] using Set.ncard_le_ncard hs
        by_cases hcdeg2 : vertexDegree G c = 2
        · have hntrSwap := containsNegativeDcA C.swapSides
              (a := c) (b := a) (c := b)
              (by simp [hc]) (by simp [ha]) (by simp [hb]) hcdeg2
              hac.symm hbf.symm hab
              (by simp [List.nodup_cons, hac.ne.symm, hbf.ne.symm, hab.ne])
          exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
            ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap))
        · have hcdeg3 : vertexDegree G c = 3 := by
            have upper := C.subcubic c
            omega
          obtain ⟨g, hcg, hga, hgb⟩ :=
            exists_third_neighbor_of_degree_three hcdeg3 hab.ne
          have hg : C.color g = .red ∨ C.color g = .reddish := by
            cases hgc : C.color g with
            | red => exact Or.inl rfl
            | reddish => exact Or.inr rfl
            | blue => exact (C.bluish_not_adj_blueSide hc (Or.inl hgc) hcg).elim
            | bluish => exact (C.bluish_not_adj_blueSide hc (Or.inr hgc) hcg).elim
          exact Or.inr ⟨⟨d, c, e, g, hd, hc, he, hg, had, hac,
            hbf, hbe, hcg, hcd.symm, hde, hce, hga, hgb, hcdeg3⟩⟩
    · by_cases hde : d = e
      · subst e
        -- Exactly one shared vertex, already in the desired orientation.
        have lower : 2 ≤ vertexDegree G d := by
          have hs : ({a, b} : Set V) ⊆ G.neighborSet d := by
            intro z hz
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
            rcases hz with rfl | rfl
            · exact had.symm
            · exact hbe.symm
          unfold vertexDegree
          simpa [hab.ne] using Set.ncard_le_ncard hs
        by_cases hddeg2 : vertexDegree G d = 2
        · have hntrSwap := containsNegativeDcA C.swapSides
              (a := d) (b := a) (c := b)
              (by simp [hd]) (by simp [ha]) (by simp [hb]) hddeg2
              had.symm hbe.symm hab
              (by simp [List.nodup_cons, had.ne.symm, hbe.ne.symm, hab.ne])
          exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
            ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap))
        · have hddeg3 : vertexDegree G d = 3 := by
            have upper := C.subcubic d
            omega
          obtain ⟨g, hdg, hga, hgb⟩ :=
            exists_third_neighbor_of_degree_three hddeg3 hab.ne
          have hg : C.color g = .red ∨ C.color g = .reddish := by
            cases hgc : C.color g with
            | red => exact Or.inl rfl
            | reddish => exact Or.inr rfl
            | blue => exact (C.bluish_not_adj_blueSide hd (Or.inl hgc) hdg).elim
            | bluish => exact (C.bluish_not_adj_blueSide hd (Or.inr hgc) hdg).elim
          exact Or.inr ⟨⟨c, d, f, g, hc, hd, hf, hg, hac, had,
            hbe, hbf, hdg, hcd, hcf, hef, hga, hgb, hddeg3⟩⟩
      · by_cases hdf : d = f
        · subst f
          -- Exactly one shared vertex, exchanging the two neighbors of `b`.
          have lower : 2 ≤ vertexDegree G d := by
            have hs : ({a, b} : Set V) ⊆ G.neighborSet d := by
              intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact had.symm
              · exact hbf.symm
            unfold vertexDegree
            simpa [hab.ne] using Set.ncard_le_ncard hs
          by_cases hddeg2 : vertexDegree G d = 2
          · have hntrSwap := containsNegativeDcA C.swapSides
                (a := d) (b := a) (c := b)
                (by simp [hd]) (by simp [ha]) (by simp [hb]) hddeg2
                had.symm hbf.symm hab
                (by simp [List.nodup_cons, had.ne.symm, hbf.ne.symm, hab.ne])
            exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
              ((containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 hntrSwap))
          · have hddeg3 : vertexDegree G d = 3 := by
              have upper := C.subcubic d
              omega
            obtain ⟨g, hdg, hga, hgb⟩ :=
              exists_third_neighbor_of_degree_three hddeg3 hab.ne
            have hg : C.color g = .red ∨ C.color g = .reddish := by
              cases hgc : C.color g with
              | red => exact Or.inl rfl
              | reddish => exact Or.inr rfl
              | blue => exact (C.bluish_not_adj_blueSide hd (Or.inl hgc) hdg).elim
              | bluish => exact (C.bluish_not_adj_blueSide hd (Or.inr hgc) hdg).elim
            exact Or.inr ⟨⟨c, d, e, g, hc, hd, he, hg, hac, had,
              hbf, hbe, hdg, hcd, hce, hde, hga, hgb, hddeg3⟩⟩
        · exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
            (contains_negativeG C ha hb hc hd he hf hab hac had hbe hbf
              hcd hef hce hcf hde hdf))

end Subcubic
