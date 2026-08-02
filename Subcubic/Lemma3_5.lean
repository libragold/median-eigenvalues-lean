import Subcubic.FlipLemmas
import Subcubic.Lemma3_3

/-!
# Lemma 3.5

The paper phrases this under the standing assumption that cut enhancers do
not occur. In this development that assumption is made explicit in the
conclusion: either the reddish vertex has degree three, or the local argument
has already found a cut enhancer.
-/

namespace Subcubic

open Set
open scoped symmDiff

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 3.5.** If `a` is red, `b` is blue, `c` is reddish, and
`a-b-c` is a path, then `c` has degree three unless there is already a cut
enhancer. The degree conclusion is obtained after flipping the cut preserver
`ab`, at which point `c` is red. -/
theorem lemma3_5
    (C : GoodColoring G) {a b c : V}
    (ha : C.color a = .red) (hb : C.color b = .blue)
    (hc : C.color c = .reddish)
    (hab : G.Adj a b) (hbc : G.Adj b c) :
    vertexDegree G c = 3 ∨ ContainsCutEnhancer C := by
  classical
  have haCorrect := C.color_correct a
  rw [ha] at haCorrect
  obtain ⟨_, rr, hrrSide, harr⟩ := haCorrect
  have hrrSide' : C.color rr = .red ∨ C.color rr = .reddish :=
    (C.mem_redSide_iff rr).1 hrrSide
  have hrr : C.color rr = .red := by
    rcases hrrSide' with hrr | hrr
    · exact hrr
    · exact (C.reddish_not_adj_redSide hrr (Or.inl ha) harr.symm).elim
  have hbCorrect := C.color_correct b
  rw [hb] at hbCorrect
  obtain ⟨_, ss, hssSide, hbss⟩ := hbCorrect
  have hssSide' : C.color ss = .blue ∨ C.color ss = .bluish :=
    (C.not_mem_redSide_iff ss).1 hssSide
  have hss : C.color ss = .blue := by
    rcases hssSide' with hss | hss
    · exact hss
    · exact (C.bluish_not_adj_blueSide hss (Or.inl hb) hbss.symm).elim
  have hrrb : rr ≠ b := by intro h; subst rr; simp_all
  obtain ⟨d, had, hdrr, hdb⟩ :=
    C.exists_third_neighbor (Or.inl ha) hrrb
  have hdSide : C.color d = .blue ∨ C.color d = .bluish :=
    C.other_neighbor_of_red_is_blueSide ha hrr harr had hdrr
  have hca : c ≠ a := by intro h; subst c; simp_all
  have hcb : c ≠ b := by intro h; subst c; simp_all
  have degree_of_flip
      (hsafe : C.color d = .bluish ∨ d = ss) : vertexDegree G c = 3 := by
    obtain ⟨M, hflip⟩ := exists_flipAt_of_local C
      ha hb hrr hss hsafe (Or.inl hc) harr hab had hbss hbc
    have hside : M.side = C.redSide ∆ ({a, b} : Set V) := hflip.2
    have hcM : c ∈ M.side := by
      rw [hside]
      simp [Set.mem_symmDiff, C.mem_redSide_iff, hc, hca, hcb]
    have hbM : b ∈ M.side := by
      rw [hside]
      simp [Set.mem_symmDiff, hb]
    have hcRed : M.toGoodColoring.color c = .red := by
      change colorOfCut G M.side c = .red
      exact (colorOfCut_eq_red_iff G M.side c).2
        ⟨hcM, b, hbM, hbc.symm⟩
    exact M.toGoodColoring.red_or_blue_degree c (Or.inl hcRed)
  by_cases hds : d = ss
  · exact Or.inl (degree_of_flip (Or.inr hds))
  rcases lemma3_3 C ha hb hss hdSide hab had hbss hdb.symm (Ne.symm hds) with
    hd | hce
  · exact Or.inl (degree_of_flip (Or.inl hd))
  · exact Or.inr hce

end Subcubic
