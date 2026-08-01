import Subcubic.MatchingCut
import Subcubic.ColoringLemmas

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
neighbors `rr` (red) and `rb` (bluish), and the blue endpoint has displayed
neighbors `ss` (blue) and `sr` (reddish).  The degree-three assumption makes
these the complete neighbor lists, so the new same-side edges are exactly
`r-rb` and `s-sr`. -/
theorem exists_flipAt_of_local
    (C : GoodColoring G) {r s rr ss rb sr : V}
    (hr : C.color r = .red) (hs : C.color s = .blue)
    (hrr : C.color rr = .red) (hss : C.color ss = .blue)
    (hrb : C.color rb = .bluish) (hsr : C.color sr = .reddish)
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
  have hrbA : rb ∉ A := by simp [A, hrb]
  have hsrA : sr ∈ A := by simp [A, hsr]
  have hrs : rr ≠ s := by intro h; subst s; simp_all
  have hrrb : rr ≠ rb := by intro h; subst rb; simp_all
  have hsrb : s ≠ rb := by intro h; subst rb; simp_all
  have hssr : ss ≠ r := by intro h; subst ss; simp_all
  have hsssr : ss ≠ sr := by intro h; subst sr; simp_all
  have hrsr : r ≠ sr := by intro h; subst sr; simp_all
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
            · have hcorrect := C.color_correct sr
              rw [hsr] at hcorrect
              exact (hcorrect.2 ⟨z, hz.1, hsz⟩).elim
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
            · have hcorrect := C.color_correct rb
              rw [hrb] at hcorrect
              exact (hcorrect.2 ⟨z, hzA, hrbz⟩).elim
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

end Subcubic
