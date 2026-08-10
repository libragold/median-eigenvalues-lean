import Subcubic.MatchingCut
import Subcubic.ColoringLemmas
import Subcubic.Lemma3_3

/-!
# Local verification of cut-preserver flips

This file isolates the routine matching-cut check used after Lemma 3.3 has
identified the two previously unmatched neighbors of a cut preserver.
-/

namespace Subcubic

open Set
open scoped symmDiff

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A red--blue edge may be flipped when the red endpoint has displayed
neighbors `rr` (red) and `rb` on the blue side, and the blue endpoint has
displayed neighbors `ss` (blue) and `sr` (reddish). The neighbor `rb` may be
bluish, or it may coincide with `ss`; in the latter case `ss` loses `s` as its
blue mate exactly when it gains `r`. -/
theorem exists_flipAt_of_local
    (C : GoodColoring G) {r s rr ss rb sr : V}
    (hr : C.color r = .red) (hs : C.color s = .blue)
    (hrr : C.color rr = .red) (hss : C.color ss = .blue)
    (hrb : C.color rb = .bluish ∨ rb = ss)
    (hsr : C.color sr = .reddish ∨ sr = rr)
    (hrrEdge : G.Adj r rr) (hrsEdge : G.Adj r s)
    (hrbEdge : G.Adj r rb) (hssEdge : G.Adj s ss)
    (hsrEdge : G.Adj s sr) :
    ∃ M' : MatchingCut G, C.toMatchingCut.IsFlipAt M' r s := by
  classical
  let A := C.redSide
  let A' := A ∆ ({r, s} : Set V)
  have hrA : r ∈ A := by simp [A, hr]
  have hsA : s ∉ A := by simp [A, hs]
  have hrrA : rr ∈ A := by simp [A, hrr]
  have hssA : ss ∉ A := by simp [A, hss]
  have hrbA : rb ∉ A := by
    rcases hrb with hrb | rfl
    · simp [A, hrb]
    · exact hssA
  have hsrA : sr ∈ A := by
    rcases hsr with hsr | rfl
    · simp [A, hsr]
    · exact hrrA
  have hrs : rr ≠ s := by intro h; subst s; simp_all
  have hrrb : rr ≠ rb := by
    intro h
    subst rb
    rcases hrb with hrb | hrb
    · simp_all
    · subst ss; simp_all
  have hsrb : s ≠ rb := by intro h; subst rb; simp_all
  have hssr : ss ≠ r := by intro h; subst ss; simp_all
  have hsssr : ss ≠ sr := by
    rcases hsr with hsr | rfl
    · intro h; subst sr; simp_all
    · intro h; subst ss; simp_all
  have hrsr : r ≠ sr := by
    rcases hsr with hsr | rfl
    · intro h; subst sr; simp_all
    · exact hrrEdge.ne
  have hA' : A' = (A \ {r}) ∪ {s} := by
    ext z
    by_cases hzr : z = r
    · subst z; simp [A', Set.mem_symmDiff, hrA, hrsEdge.ne]
    · by_cases hzs : z = s
      · subst z; simp [A', Set.mem_symmDiff, hsA, hrsEdge.ne.symm]
      · simp [A', Set.mem_symmDiff, hzr, hzs]
  have r_neighbors (z : V) (hz : G.Adj r z) :
      z = rr ∨ z = s ∨ z = rb :=
    C.neighbor_eq_of_three_neighbors (Or.inl hr)
      hrrEdge hrsEdge hrbEdge hrs hrrb hsrb hz
  have s_neighbors (z : V) (hz : G.Adj s z) :
      z = ss ∨ z = r ∨ z = sr :=
    C.neighbor_eq_of_three_neighbors (Or.inr hs)
      hssEdge hrsEdge.symm hsrEdge hssr hsssr hrsr hz
  have hmatching : IsMatchingCut G A' := by
    constructor
    · intro q hq
      rw [Set.ncard_le_one_iff]
      intro x y hx hy
      rcases hx with ⟨hqx, hxA'⟩
      rcases hy with ⟨hqy, hyA'⟩
      rw [hA'] at hq hxA' hyA'
      simp only [mem_union, mem_sdiff, mem_singleton_iff] at hq hxA' hyA'
      by_cases hqs : q = s
      · subst q
        have xeq : x = sr := by
          rcases s_neighbors x hqx with rfl | rfl | rfl
          · rcases hxA' with hx | hx <;> simp_all
          · rcases hxA' with hx | hx <;> simp_all
          · rfl
        have yeq : y = sr := by
          rcases s_neighbors y hqy with rfl | rfl | rfl
          · rcases hyA' with hy | hy <;> simp_all
          · rcases hyA' with hy | hy <;> simp_all
          · rfl
        exact xeq.trans yeq.symm
      · by_cases hqsr : q = sr
        · subst q
          have one_neighbor : ∀ {z}, G.Adj sr z →
              ((z ∈ A ∧ z ≠ r) ∨ z = s) → z = s := by
            intro z hsz hz
            rcases hz with hz | hz
            · rcases hsr with hsr | rfl
              · have hcorrect := C.color_correct sr
                rw [hsr] at hcorrect
                exact (hcorrect.2 ⟨z, hz.1, hsz⟩).elim
              · exact (C.redSide_not_adj_second_neighbor hrrA hrA hz.1
                  hrrEdge.symm hz.2.symm) hsz |>.elim
            · exact hz
          exact (one_neighbor hqx hxA').trans
            (one_neighbor hqy hyA').symm
        · have qrA : q ∈ A := by rcases hq with hq | hq <;> simp_all
          have qne : q ≠ r := by rcases hq with hq | hq <;> simp_all
          have to_old : ∀ {z}, G.Adj q z →
              ((z ∈ A ∧ z ≠ r) ∨ z = s) → z ∈ A := by
            intro z hqz hz
            rcases hz with hz | rfl
            · exact hz.1
            · rcases s_neighbors q hqz.symm with rfl | rfl | rfl
              · exact (hssA qrA).elim
              · exact (qne rfl).elim
              · exact (hqsr rfl).elim
          have hold := C.matching.1 q qrA
          rw [Set.ncard_le_one_iff] at hold
          exact hold ⟨hqx, to_old hqx hxA'⟩ ⟨hqy, to_old hqy hyA'⟩
    · intro q hq
      rw [Set.ncard_le_one_iff]
      intro x y hx hy
      rcases hx with ⟨hqx, hxA'⟩
      rcases hy with ⟨hqy, hyA'⟩
      simp only [mem_compl_iff] at hxA' hyA'
      rw [hA'] at hq hxA' hyA'
      simp only [mem_union, mem_sdiff, mem_singleton_iff, not_or,
        not_and, not_not] at hq hxA' hyA'
      by_cases hqr : q = r
      · subst q
        have xeq : x = rb := by
          rcases r_neighbors x hqx with rfl | rfl | rfl
          · simp_all
          · simp_all
          · rfl
        have yeq : y = rb := by
          rcases r_neighbors y hqy with rfl | rfl | rfl
          · simp_all
          · simp_all
          · rfl
        exact xeq.trans yeq.symm
      · by_cases hqrb : q = rb
        · subst q
          have one_neighbor : ∀ {z}, G.Adj rb z →
              ((z ∈ A → z = r) ∧ z ≠ s) → z = r := by
            intro z hrbz hz
            by_cases hzA : z ∈ A
            · exact hz.1 hzA
            · rcases hrb with hrb | hrb
              · have hcorrect := C.color_correct rb
                rw [hrb] at hcorrect
                exact (hcorrect.2 ⟨z, hzA, hrbz⟩).elim
              · have hrbBlue : C.color rb = .blue := by simpa [hrb] using hss
                have hsBlue : s ∉ C.redSide := by simp [hs]
                have hzBlue : z ∉ C.redSide := by simpa [A] using hzA
                exact ((C.blueSide_not_adj_second_neighbor
                  (by simp [hrbBlue]) hsBlue hzBlue
                  (by simpa [hrb] using hssEdge.symm) hz.2.symm) hrbz).elim
          exact (one_neighbor hqx hxA').trans
            (one_neighbor hqy hyA').symm
        · have qnotA : q ∉ A := by
            intro qA
            exact hqr (hq.1 qA)
          have qne : q ≠ s := hq.2
          have to_old : ∀ {z}, G.Adj q z →
              ((z ∈ A → z = r) ∧ z ≠ s) → z ∉ A := by
            intro z hqz hz zA
            have hzEq : z = r := by
              by_contra hzr
              exact hzr (hz.1 zA)
            subst z
            rcases r_neighbors q hqz.symm with rfl | rfl | rfl
            · exact qnotA hrrA
            · exact (qne rfl).elim
            · exact (hqrb rfl).elim
          have hold := C.matching.2 q qnotA
          rw [Set.ncard_le_one_iff] at hold
          exact hold ⟨hqx, to_old hqx hxA'⟩ ⟨hqy, to_old hqy hyA'⟩
  let M' : MatchingCut G := {
    side := A'
    subcubic := C.subcubic
    matching := hmatching }
  refine ⟨M', ⟨?_, rfl⟩⟩
  exact ⟨hrsEdge, by simpa [GoodColoring.toMatchingCut_color] using hr,
    by simpa [GoodColoring.toMatchingCut_color] using hs⟩

/-- A reusable form of the paper's instruction "flip the cut preserver".
Once the red mate `rr` and blue mate `ss` are displayed, Lemma 3.3 identifies
the two remaining neighbors needed by `exists_flipAt_of_local`.  The mild
nonedge `s-rr` rules out the only shared-mate degeneracy on the red side. -/
theorem exists_flipAt_or_cutEnhancer
    (C : GoodColoring G) {r s rr ss : V}
    (hr : C.color r = .red) (hs : C.color s = .blue)
    (hrr : C.color rr = .red) (hss : C.color ss = .blue)
    (hrDegree : vertexDegree G r = 3)
    (hsDegree : vertexDegree G s = 3)
    (hrrEdge : G.Adj r rr) (hrsEdge : G.Adj r s)
    (hssEdge : G.Adj s ss) :
    (∃ M' : MatchingCut G, C.toMatchingCut.IsFlipAt M' r s) ∨
      ContainsCutEnhancer C := by
  have hrrs : rr ≠ s := by intro h; subst rr; simp_all
  obtain ⟨rb, hrbEdge, hrbrr, hrbs⟩ :=
    C.exists_third_neighbor hrDegree hrrs
  have hrbSide : C.color rb = .blue ∨ C.color rb = .bluish :=
    C.other_neighbor_of_red_is_blueSide hr hrr hrrEdge hrbEdge hrbrr
  have finish (hrbSafe : C.color rb = .bluish ∨ rb = ss) :
      (∃ M' : MatchingCut G, C.toMatchingCut.IsFlipAt M' r s) ∨
        ContainsCutEnhancer C := by
    by_cases hsrr : G.Adj s rr
    · exact Or.inl (exists_flipAt_of_local C hr hs hrr hss hrbSafe
        (Or.inr rfl) hrrEdge hrsEdge hrbEdge hssEdge hsrr)
    have hssr : ss ≠ r := by intro h; subst ss; simp_all
    obtain ⟨sr, hsrEdge, hsrss, hsrrV⟩ :=
      C.exists_third_neighbor hsDegree hssr
    have hsrSide : C.color sr = .red ∨ C.color sr = .reddish :=
      C.other_neighbor_of_blue_is_redSide hs hss hssEdge hsrEdge hsrss
    have hsrrr : rr ≠ sr := by
      intro h
      subst sr
      exact hsrr hsrEdge
    rcases lemma3_3_reversed C hs hr hrr hsrSide hrsEdge.symm hsrEdge
        hrrEdge hsrrV.symm hsrrr with hsr | hce
    · exact Or.inl (exists_flipAt_of_local C hr hs hrr hss hrbSafe (Or.inl hsr)
        hrrEdge hrsEdge hrbEdge hssEdge hsrEdge)
    · exact Or.inr hce
  by_cases hrbss : rb = ss
  · exact finish (Or.inr hrbss)
  rcases lemma3_3 C hr hs hss hrbSide hrsEdge hrbEdge hssEdge
      hrbs.symm (Ne.symm hrbss) with hrb | hce
  · exact finish (Or.inl hrb)
  · exact Or.inr hce

/-! Small color-recomputation lemmas.  They keep later flip proofs focused on
the displayed graph rather than on symmetric-difference bookkeeping. -/

theorem mem_side_iff_of_flipAt (C : GoodColoring G)
    {M : MatchingCut G} {r s z : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hzr : z ≠ r) (hzs : z ≠ s) :
    z ∈ M.side ↔ z ∈ C.redSide := by
  rw [hflip.2]
  simp [Set.mem_symmDiff, hzr, hzs]

theorem red_of_untouched_red_edge (C : GoodColoring G)
    {M : MatchingCut G} {r s x y : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : x ∈ C.redSide) (hy : y ∈ C.redSide) (hxy : G.Adj x y)
    (hxr : x ≠ r) (hxs : x ≠ s) (hyr : y ≠ r) (hys : y ≠ s) :
    M.toGoodColoring.color x = .red := by
  change colorOfCut G M.side x = .red
  rw [colorOfCut_eq_red_iff]
  exact ⟨(mem_side_iff_of_flipAt C hflip hxr hxs).2 hx, y,
    (mem_side_iff_of_flipAt C hflip hyr hys).2 hy, hxy⟩

theorem blue_of_untouched_blue_edge (C : GoodColoring G)
    {M : MatchingCut G} {r s x y : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : x ∉ C.redSide) (hy : y ∉ C.redSide) (hxy : G.Adj x y)
    (hxr : x ≠ r) (hxs : x ≠ s) (hyr : y ≠ r) (hys : y ≠ s) :
    M.toGoodColoring.color x = .blue := by
  change colorOfCut G M.side x = .blue
  rw [colorOfCut_eq_blue_iff]
  refine ⟨fun hxM => hx ((mem_side_iff_of_flipAt C hflip hxr hxs).1 hxM),
    y, ?_, hxy⟩
  intro hyM
  exact hy ((mem_side_iff_of_flipAt C hflip hyr hys).1 hyM)

theorem red_of_reddish_gains_flipped_blue (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .reddish) (hxs : G.Adj x s)
    (hxr : x ≠ r) (hxsV : x ≠ s) :
    M.toGoodColoring.color x = .red := by
  have hxOld : x ∈ C.redSide := by simp [hx]
  have hxM := (mem_side_iff_of_flipAt C hflip hxr hxsV).2 hxOld
  have hsM : s ∈ M.side := by
    rw [hflip.2]
    have hsOld : s ∉ C.redSide := by
      exact (C.not_mem_redSide_iff s).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2))
    simp [Set.mem_symmDiff, hsOld, hflip.1.1.ne.symm]
  exact (colorOfCut_eq_red_iff G M.side x).2 ⟨hxM, s, hsM, hxs⟩

theorem blue_of_bluish_gains_flipped_red (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .bluish) (hxrEdge : G.Adj x r)
    (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color x = .blue := by
  have hxOld : x ∉ C.redSide := by simp [hx]
  have hxM : x ∉ M.side := by
    intro hxNew
    exact hxOld ((mem_side_iff_of_flipAt C hflip hxr hxs).1 hxNew)
  have hrM : r ∉ M.side := by
    rw [hflip.2]
    have hrOld : r ∈ C.redSide := by
      exact (C.mem_redSide_iff r).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1))
    simp [Set.mem_symmDiff, hrOld, hflip.1.1.ne]
  exact (colorOfCut_eq_blue_iff G M.side x).2 ⟨hxM, r, hrM, hxrEdge⟩

theorem reddish_of_red_loses_flipped_mate (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .red) (hxrEdge : G.Adj x r)
    (hxsEdge : ¬ G.Adj x s) (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color x = .reddish := by
  have hxOld : x ∈ C.redSide := by simp [hx]
  have hxM := (mem_side_iff_of_flipAt C hflip hxr hxs).2 hxOld
  apply (colorOfCut_eq_reddish_iff G M.side x).2
  refine ⟨hxM, ?_⟩
  rintro ⟨z, hzM, hxz⟩
  by_cases hzr : z = r
  · subst z
    have hrOld : r ∈ C.redSide := by
      exact (C.mem_redSide_iff r).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1))
    have : r ∉ M.side := by
      rw [hflip.2]
      simp [Set.mem_symmDiff, hrOld, hflip.1.1.ne]
    exact this hzM
  by_cases hzs : z = s
  · subst z
    exact hxsEdge hxz
  have hzOld := (mem_side_iff_of_flipAt C hflip hzr hzs).1 hzM
  have hnot := C.redSide_not_adj_second_neighbor hxOld
    (by
      exact (C.mem_redSide_iff r).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1))) hzOld
    hxrEdge (Ne.symm hzr)
  exact hnot hxz

theorem bluish_of_blue_loses_flipped_mate (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .blue) (hxsEdge : G.Adj x s)
    (hxrEdge : ¬ G.Adj x r) (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color x = .bluish := by
  have hxOld : x ∉ C.redSide := by simp [hx]
  have hxM : x ∉ M.side := by
    intro hxNew
    exact hxOld ((mem_side_iff_of_flipAt C hflip hxr hxs).1 hxNew)
  apply (colorOfCut_eq_bluish_iff G M.side x).2
  refine ⟨hxM, ?_⟩
  rintro ⟨z, hzM, hxz⟩
  by_cases hzr : z = r
  · subst z
    exact hxrEdge hxz
  by_cases hzs : z = s
  · subst z
    have hsOld : s ∉ C.redSide := by
      exact (C.not_mem_redSide_iff s).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2))
    have : s ∈ M.side := by
      rw [hflip.2]
      simp [Set.mem_symmDiff, hsOld, hflip.1.1.ne.symm]
    exact hzM this
  have hzOld : z ∉ C.redSide := by
    intro hzOld
    exact hzM ((mem_side_iff_of_flipAt C hflip hzr hzs).2 hzOld)
  have hsOld : s ∉ C.redSide := by
    exact (C.not_mem_redSide_iff s).2 (Or.inl (by
      simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2))
  exact (C.blueSide_not_adj_second_neighbor hxOld hsOld hzOld
    hxsEdge (Ne.symm hzs)) hxz

theorem reddish_of_untouched_reddish (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .reddish) (hxsEdge : ¬ G.Adj x s)
    (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color x = .reddish := by
  have hxOld : x ∈ C.redSide := by simp [hx]
  have hxM := (mem_side_iff_of_flipAt C hflip hxr hxs).2 hxOld
  apply (colorOfCut_eq_reddish_iff G M.side x).2
  refine ⟨hxM, ?_⟩
  rintro ⟨z, hzM, hxz⟩
  by_cases hzr : z = r
  · subst z
    have hrOld : r ∈ C.redSide :=
      (C.mem_redSide_iff r).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1))
    have : r ∉ M.side := by
      rw [hflip.2]
      simp [Set.mem_symmDiff, hrOld, hflip.1.1.ne]
    exact this hzM
  by_cases hzs : z = s
  · subst z
    exact hxsEdge hxz
  have hzOld := (mem_side_iff_of_flipAt C hflip hzr hzs).1 hzM
  exact (C.reddish_not_adj_redSide hx
    ((C.mem_redSide_iff z).1 hzOld)) hxz

theorem bluish_of_untouched_bluish (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .bluish) (hxrEdge : ¬ G.Adj x r)
    (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color x = .bluish := by
  have hxOld : x ∉ C.redSide := by simp [hx]
  have hxM : x ∉ M.side := by
    intro hxNew
    exact hxOld ((mem_side_iff_of_flipAt C hflip hxr hxs).1 hxNew)
  apply (colorOfCut_eq_bluish_iff G M.side x).2
  refine ⟨hxM, ?_⟩
  rintro ⟨z, hzM, hxz⟩
  by_cases hzr : z = r
  · subst z
    exact hxrEdge hxz
  by_cases hzs : z = s
  · subst z
    have hsOld : s ∉ C.redSide :=
      (C.not_mem_redSide_iff s).2 (Or.inl (by
        simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2))
    have : s ∈ M.side := by
      rw [hflip.2]
      simp [Set.mem_symmDiff, hsOld, hflip.1.1.ne.symm]
    exact hzM this
  have hzOld : z ∉ C.redSide := by
    intro hzOld
    exact hzM ((mem_side_iff_of_flipAt C hflip hzr hzs).2 hzOld)
  exact (C.bluish_not_adj_blueSide hx
    ((C.not_mem_redSide_iff z).1 hzOld)) hxz

theorem red_of_flipped_blue_with_reddish_neighbor (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .reddish) (hsx : G.Adj s x)
    (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color s = .red := by
  have hsOld : s ∉ C.redSide :=
    (C.not_mem_redSide_iff s).2 (Or.inl (by
      simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2))
  have hsM : s ∈ M.side := by
    rw [hflip.2]
    simp [Set.mem_symmDiff, hsOld, hflip.1.1.ne.symm]
  have hxOld : x ∈ C.redSide := by simp [hx]
  have hxM := (mem_side_iff_of_flipAt C hflip hxr hxs).2 hxOld
  exact (colorOfCut_eq_red_iff G M.side s).2 ⟨hsM, x, hxM, hsx⟩

theorem blue_of_flipped_red_with_bluish_neighbor (C : GoodColoring G)
    {M : MatchingCut G} {r s x : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hx : C.color x = .bluish) (hrx : G.Adj r x)
    (hxr : x ≠ r) (hxs : x ≠ s) :
    M.toGoodColoring.color r = .blue := by
  have hrOld : r ∈ C.redSide :=
    (C.mem_redSide_iff r).2 (Or.inl (by
      simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1))
  have hrM : r ∉ M.side := by
    rw [hflip.2]
    simp [Set.mem_symmDiff, hrOld, hflip.1.1.ne]
  have hxOld : x ∉ C.redSide := by simp [hx]
  have hxM : x ∉ M.side := by
    intro hxNew
    exact hxOld ((mem_side_iff_of_flipAt C hflip hxr hxs).1 hxNew)
  exact (colorOfCut_eq_blue_iff G M.side r).2 ⟨hrM, x, hxM, hrx⟩

/-- The red endpoint of a valid flip becomes blue.  Its old red mate and the
blue endpoint account for two neighbors; degree three supplies a third old
blue-side neighbor which is not flipped. -/
theorem blue_of_flipped_red_endpoint (C : GoodColoring G)
    {M : MatchingCut G} {r s rr : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hrr : C.color rr = .red) (hrrEdge : G.Adj r rr)
    (hrDegree : vertexDegree G r = 3)
    (hrrs : rr ≠ s) : M.toGoodColoring.color r = .blue := by
  have hr : C.color r = .red := by
    simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.1
  obtain ⟨z, hrz, hzrr, hzs⟩ :=
    C.exists_third_neighbor hrDegree hrrs
  have hzBlue : z ∉ C.redSide := by
    rw [C.not_mem_redSide_iff]
    exact C.other_neighbor_of_red_is_blueSide hr hrr hrrEdge hrz hzrr
  have hrM : r ∉ M.side := by
    rw [hflip.2]
    have hrOld : r ∈ C.redSide := by simp [hr]
    simp [Set.mem_symmDiff, hrOld, hflip.1.1.ne]
  have hzM : z ∉ M.side := by
    intro hzNew
    exact hzBlue ((mem_side_iff_of_flipAt C hflip hrz.ne.symm hzs).1 hzNew)
  exact (colorOfCut_eq_blue_iff G M.side r).2 ⟨hrM, z, hzM, hrz⟩

/-- The blue endpoint of a valid flip becomes red; this is the color-reversed
form of `blue_of_flipped_red_endpoint`. -/
theorem red_of_flipped_blue_endpoint (C : GoodColoring G)
    {M : MatchingCut G} {r s ss : V}
    (hflip : C.toMatchingCut.IsFlipAt M r s)
    (hss : C.color ss = .blue) (hssEdge : G.Adj s ss)
    (hsDegree : vertexDegree G s = 3)
    (hssr : ss ≠ r) : M.toGoodColoring.color s = .red := by
  have hs : C.color s = .blue := by
    simpa [GoodColoring.toMatchingCut_color] using hflip.1.2.2
  obtain ⟨z, hsz, hzss, hzr⟩ :=
    C.exists_third_neighbor hsDegree hssr
  have hzRed : z ∈ C.redSide := by
    rw [C.mem_redSide_iff]
    exact C.other_neighbor_of_blue_is_redSide hs hss hssEdge hsz hzss
  have hsM : s ∈ M.side := by
    rw [hflip.2]
    have hsOld : s ∉ C.redSide := by simp [hs]
    simp [Set.mem_symmDiff, hsOld, hflip.1.1.ne.symm]
  have hzM : z ∈ M.side :=
    (mem_side_iff_of_flipAt C hflip hzr hsz.ne.symm).2 hzRed
  exact (colorOfCut_eq_red_iff G M.side s).2 ⟨hsM, z, hzM, hsz⟩

end Subcubic
