import Subcubic.CutEnhancers
import Subcubic.PositiveTailReducerWitnesses
import Subcubic.NegativeTailReducerWitnesses
import Subcubic.ColoringLemmas
import Subcubic.MatchingCut

/-!
# Lemma 3.4

This file proves the constructive, disjunctive form intended to replace the
former exact degree-three axiom. A red or blue vertex has ambient degree three
unless one of the two explicit low-degree configurations already gives an
absolute tail reducer or a cut enhancer.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The new two-vertex catalogue entry is simultaneously a positive and a
negative tail reducer. -/
def ContainsAbsoluteTailReducer (C : GoodColoring G) : Prop :=
  ContainsPositiveTailReducer C ∧ ContainsNegativeTailReducer C

/-- The alternatives to the degree-three conclusion in Lemma 3.4. -/
def ContainsLemma3_4Obstruction (C : GoodColoring G) : Prop :=
  ContainsAbsoluteTailReducer C ∨ ContainsCutEnhancer C

/-- A Lemma 3.4 obstruction found after zero or more valid flips. -/
def HasReachableLemma3_4Obstruction (C : GoodColoring G) : Prop :=
  ∃ M : MatchingCut G, C.toMatchingCut.FlipReachable M ∧
    ContainsLemma3_4Obstruction M.toGoodColoring

theorem HasReachableLemma3_4Obstruction.after_flip
    (C : GoodColoring G) {M₁ : MatchingCut G} {r s : V}
    (hflip : C.toMatchingCut.IsFlipAt M₁ r s)
    (h : HasReachableLemma3_4Obstruction M₁.toGoodColoring) :
    HasReachableLemma3_4Obstruction C := by
  rcases h with ⟨M, hreach, hfound⟩
  have hround : M₁.toGoodColoring.toMatchingCut = M₁ := by
    apply MatchingCut.ext _ _
    simp [GoodColoring.toMatchingCut_side, GoodColoring.redSide,
      MatchingCut.redSideOf_color]
  rw [hround] at hreach
  have prepend : ∀ {N : MatchingCut G},
      M₁.FlipReachable N → C.toMatchingCut.FlipReachable N := by
    intro N hN
    induction hN with
    | refl => exact .step .refl hflip
    | @step N₁ N₂ x y hN hxy ih => exact .step ih hxy
  exact ⟨M, prepend hreach, hfound⟩

/-- Lemma 3.4 obstructions depend only on the recomputed color function. -/
theorem containsLemma3_4Obstruction_congr_color
    {C D : GoodColoring G} (hcolor : C.color = D.color) :
    ContainsLemma3_4Obstruction C ↔ ContainsLemma3_4Obstruction D := by
  unfold ContainsLemma3_4Obstruction ContainsAbsoluteTailReducer
    ContainsPositiveTailReducer ContainsNegativeTailReducer ContainsCutEnhancer
  rw [containsInducedUpToSwap_congr_color IsPositiveTailReducer hcolor,
    containsInducedUpToSwap_congr_color IsNegativeTailReducer hcolor,
    containsInducedUpToSwap_congr_color IsCutEnhancer hcolor]

theorem HasReachableLemma3_4Obstruction.of_current
    (C : GoodColoring G) (h : ContainsLemma3_4Obstruction C) :
    HasReachableLemma3_4Obstruction C := by
  refine ⟨C.toMatchingCut, .refl, ?_⟩
  exact (containsLemma3_4Obstruction_congr_color (by simp)).1 h

/-- A red vertex has a red mate, directly from the meaning of `red`. -/
theorem GoodColoring.exists_red_mate
    (C : GoodColoring G) {v : V} (hv : C.color v = .red) :
    ∃ m, C.color m = .red ∧ G.Adj v m := by
  have hcorrect := C.color_correct v
  rw [hv] at hcorrect
  obtain ⟨_, m, hmSide, hvm⟩ := hcorrect
  have hmCases := (C.mem_redSide_iff m).1 hmSide
  rcases hmCases with hm | hm
  · exact ⟨m, hm, hvm⟩
  · exact (C.reddish_not_adj_redSide hm (Or.inl hv) hvm.symm).elim

/-- **Lemma 3.4, red-edge form.** If `ab` is a red edge, then `a` has
degree three, or the degree-one/two local configuration is already an
absolute tail reducer or a cut enhancer. -/
theorem lemma3_4_redEdge
    (C : GoodColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red)
    (hab : G.Adj a b) :
    vertexDegree G a = 3 ∨ ContainsLemma3_4Obstruction C := by
  have hpositive : 0 < vertexDegree G a := by
    unfold vertexDegree
    rw [Set.ncard_pos]
    exact ⟨b, hab⟩
  have hle := C.subcubic a
  rcases (show vertexDegree G a = 1 ∨ vertexDegree G a = 2 ∨
      vertexDegree G a = 3 by omega) with haDegree | haDegree | haDegree
  · exact Or.inr (Or.inr
      (containsCutEnhancerDegreeOne_of C ha haDegree))
  · obtain ⟨c, hac, hcb⟩ :=
      exists_other_neighbor_of_degree_two haDegree hab
    have hcSide := C.other_neighbor_of_red_is_blueSide ha hb hab hac hcb
    rcases hcSide with hc | hc
    · exact Or.inr (Or.inr
        (containsCutEnhancerDegreeTwoCross_of C ha hc hac haDegree))
    · exact Or.inr (Or.inl ⟨
        containsPositiveAbs C ha hc hac haDegree,
        containsNegativeAbs C ha hc hac haDegree⟩)
  · exact Or.inl haDegree

/-- **Lemma 3.4.** The color-reversed form is included automatically because
all three catalog predicates are defined up to exchange of the two sides. -/
theorem lemma3_4
    (C : GoodColoring G) {a : V}
    (ha : C.color a = .red ∨ C.color a = .blue) :
    vertexDegree G a = 3 ∨ ContainsLemma3_4Obstruction C := by
  rcases ha with ha | ha
  · obtain ⟨b, hb, hab⟩ := C.exists_red_mate ha
    exact lemma3_4_redEdge C ha hb hab
  · obtain ⟨b, hb, hab⟩ := C.exists_blue_mate ha
    have h := lemma3_4_redEdge C.swapSides
      (by simp [ha]) (by simp [hb]) hab
    rcases h with hdegree | habsolute | hce
    · exact Or.inl hdegree
    · exact Or.inr (Or.inl ⟨
        (containsInducedUpToSwap_swapSides IsPositiveTailReducer C).1 habsolute.1,
        (containsInducedUpToSwap_swapSides IsNegativeTailReducer C).1 habsolute.2⟩)
    · exact Or.inr (Or.inr
        ((containsInducedUpToSwap_swapSides IsCutEnhancer C).1 hce))

/-- Lemma 3.4 specialized to proofs hunting positive tail reducers. -/
theorem lemma3_4_positive
    (C : GoodColoring G) {a : V}
    (ha : C.color a = .red ∨ C.color a = .blue) :
    vertexDegree G a = 3 ∨
      (ContainsPositiveTailReducer C ∨ ContainsCutEnhancer C) := by
  rcases lemma3_4 C ha with hdegree | habsolute | hce
  · exact Or.inl hdegree
  · exact Or.inr (Or.inl habsolute.1)
  · exact Or.inr (Or.inr hce)

/-- Lemma 3.4 specialized to proofs hunting negative tail reducers. -/
theorem lemma3_4_negative
    (C : GoodColoring G) {a : V}
    (ha : C.color a = .red ∨ C.color a = .blue) :
    vertexDegree G a = 3 ∨
      (ContainsNegativeTailReducer C ∨ ContainsCutEnhancer C) := by
  rcases lemma3_4 C ha with hdegree | habsolute | hce
  · exact Or.inl hdegree
  · exact Or.inr (Or.inl habsolute.2)
  · exact Or.inr (Or.inr hce)

end Subcubic
