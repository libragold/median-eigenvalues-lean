import Subcubic.Basic
import Mathlib.Data.Set.SymmDiff

/-!
# Matching cuts and cut-preserver flips

Unlike `GoodColoring`, a `MatchingCut` stores the cut itself.  This is the
right representation while flipping cut preservers: the side is changed and
all four colors are then recomputed from the new side.
-/

open Set
open scoped symmDiff

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Both sides of `A, Aᶜ` induce graphs of maximum degree at most one. -/
def IsMatchingCut (G : SimpleGraph V) (A : Set V) : Prop :=
  (∀ v ∈ A, (G.neighborSet v ∩ A).ncard ≤ 1) ∧
  (∀ v ∉ A, (G.neighborSet v ∩ Aᶜ).ncard ≤ 1)

/-- Recompute the exact four-coloring determined by a cut. -/
noncomputable def colorOfCut (G : SimpleGraph V) (A : Set V) (v : V) : Color := by
  classical
  exact if v ∈ A then
    if ∃ w ∈ A, G.Adj v w then .red else .reddish
  else if ∃ w ∉ A, G.Adj v w then .blue else .bluish

@[simp] theorem colorOfCut_eq_red_iff (G : SimpleGraph V) (A : Set V) (v : V) :
    colorOfCut G A v = .red ↔ v ∈ A ∧ ∃ w ∈ A, G.Adj v w := by
  classical
  by_cases hv : v ∈ A
  · by_cases hn : ∃ w ∈ A, G.Adj v w <;> simp [colorOfCut, hv, hn]
  · by_cases hn : ∃ w ∉ A, G.Adj v w <;> simp [colorOfCut, hv, hn]

@[simp] theorem colorOfCut_eq_reddish_iff (G : SimpleGraph V) (A : Set V) (v : V) :
    colorOfCut G A v = .reddish ↔ v ∈ A ∧ ¬ ∃ w ∈ A, G.Adj v w := by
  classical
  by_cases hv : v ∈ A
  · by_cases hn : ∃ w ∈ A, G.Adj v w <;> simp [colorOfCut, hv, hn]
  · by_cases hn : ∃ w ∉ A, G.Adj v w <;> simp [colorOfCut, hv, hn]

@[simp] theorem colorOfCut_eq_blue_iff (G : SimpleGraph V) (A : Set V) (v : V) :
    colorOfCut G A v = .blue ↔ v ∉ A ∧ ∃ w ∉ A, G.Adj v w := by
  classical
  by_cases hv : v ∈ A
  · by_cases hn : ∃ w ∈ A, G.Adj v w <;> simp [colorOfCut, hv, hn]
  · by_cases hn : ∃ w ∉ A, G.Adj v w <;> simp [colorOfCut, hv, hn]

@[simp] theorem colorOfCut_eq_bluish_iff (G : SimpleGraph V) (A : Set V) (v : V) :
    colorOfCut G A v = .bluish ↔ v ∉ A ∧ ¬ ∃ w ∉ A, G.Adj v w := by
  classical
  by_cases hv : v ∈ A
  · by_cases hn : ∃ w ∈ A, G.Adj v w <;> simp [colorOfCut, hv, hn]
  · by_cases hn : ∃ w ∉ A, G.Adj v w <;> simp [colorOfCut, hv, hn]

@[simp] theorem redSideOf_colorOfCut (G : SimpleGraph V) (A : Set V) :
    redSideOf (colorOfCut G A) = A := by
  classical
  ext v
  by_cases hv : v ∈ A
  · by_cases hn : ∃ w ∈ A, G.Adj v w <;>
      simp [redSideOf, colorOfCut, Color.IsRedSide, hv, hn]
  · by_cases hn : ∃ w ∉ A, G.Adj v w <;>
      simp [redSideOf, colorOfCut, Color.IsRedSide, hv, hn]

/-- A matching cut in a fixed subcubic graph. -/
structure MatchingCut (G : SimpleGraph V) where
  side : Set V
  subcubic : IsSubcubic G
  matching : IsMatchingCut G side

namespace MatchingCut

/-- Matching cuts in the same graph are equal when their chosen side is
equal; the remaining fields are propositions. -/
@[ext] theorem ext (M N : MatchingCut G) (hside : M.side = N.side) : M = N := by
  cases M
  cases N
  simp_all

/-- Exchange the two sides of a matching cut. -/
def swapSides (M : MatchingCut G) : MatchingCut G where
  side := M.sideᶜ
  subcubic := M.subcubic
  matching := by
    constructor
    · intro v hv
      exact M.matching.2 v (by simpa using hv)
    · intro v hv
      simpa using M.matching.1 v (by simpa using hv)

@[simp] theorem swapSides_side (M : MatchingCut G) :
    M.swapSides.side = M.sideᶜ := rfl

@[simp] theorem swapSides_swapSides (M : MatchingCut G) :
    M.swapSides.swapSides = M := by
  apply MatchingCut.ext
  simp

/-- The exact colors obtained by inspecting the two induced matchings. -/
noncomputable def color (M : MatchingCut G) : V → Color :=
  colorOfCut G M.side

@[simp] theorem swapSides_color (M : MatchingCut G) (v : V) :
    M.swapSides.color v = (M.color v).swap := by
  classical
  unfold color colorOfCut
  by_cases hv : v ∈ M.side
  · have hv' : v ∉ M.sideᶜ := by simpa
    by_cases hn : ∃ w ∈ M.side, G.Adj v w
    · have hn' : ∃ w ∉ M.sideᶜ, G.Adj v w := by simpa
      simp [hv, hv', hn, hn', Color.swap]
    · have hn' : ¬ ∃ w ∉ M.sideᶜ, G.Adj v w := by
        rintro ⟨w, hw, hvw⟩
        exact hn ⟨w, by simpa using hw, hvw⟩
      simp [hv, hv', hn, hn', Color.swap]
  · have hv' : v ∈ M.sideᶜ := by simpa
    by_cases hn : ∃ w ∉ M.side, G.Adj v w
    · have hn' : ∃ w ∈ M.sideᶜ, G.Adj v w := by simpa
      simp [hv, hv', hn, hn', Color.swap]
    · have hn' : ¬ ∃ w ∈ M.sideᶜ, G.Adj v w := by
        rintro ⟨w, hw, hvw⟩
        exact hn ⟨w, by simpa using hw, hvw⟩
      simp [hv, hv', hn, hn', Color.swap]

@[simp] theorem redSideOf_color (M : MatchingCut G) :
    redSideOf M.color = M.side := by
  exact redSideOf_colorOfCut G M.side

theorem color_correct (M : MatchingCut G) (v : V) :
    HasGraphColor G M.color v (M.color v) := by
  classical
  unfold color
  by_cases hv : v ∈ M.side
  · by_cases hn : ∃ w ∈ M.side, G.Adj v w
    · simp [colorOfCut, hv, hn, HasGraphColor, redSideOf_colorOfCut]
    · simp [colorOfCut, hv, hn, HasGraphColor, redSideOf_colorOfCut]
  · by_cases hn : ∃ w ∉ M.side, G.Adj v w
    · simp [colorOfCut, hv, hn, HasGraphColor, redSideOf_colorOfCut]
    · simp [colorOfCut, hv, hn, HasGraphColor, redSideOf_colorOfCut]

/-!
`lemma3_4_red_or_blue_degree` is intentionally the single paper-specific
axiom in this layer.  In the paper it is Lemma 3.4: for every matching cut
under consideration in the fixed subcubic graph, vertices that are red or
blue have degree three.  Taking it as an axiom lets later flip arguments use
the same `GoodColoring` API without formalizing the earlier minimal-counterexample
infrastructure.
-/

/-- **Axiom (Lemma 3.4 of the paper).** -/
axiom lemma3_4_red_or_blue_degree (M : MatchingCut G) (v : V)
    (hv : M.color v = .red ∨ M.color v = .blue) :
    vertexDegree G v = 3

/-- View a matching cut through the existing color-based API. -/
noncomputable def toGoodColoring (M : MatchingCut G) : GoodColoring G where
  color := M.color
  subcubic := M.subcubic
  matching := by
    simpa [IsMatchingColoring, IsMatchingCut, M.redSideOf_color] using M.matching
  color_correct := M.color_correct
  red_or_blue_degree := M.lemma3_4_red_or_blue_degree

@[simp] theorem toGoodColoring_color (M : MatchingCut G) :
    M.toGoodColoring.color = M.color := rfl

/-- A directed red--blue edge in the current, recomputed coloring. -/
def IsCutPreserver (M : MatchingCut G) (a b : V) : Prop :=
  G.Adj a b ∧ M.color a = .red ∧ M.color b = .blue

/-- `M'` is obtained by toggling precisely the endpoints of the cut
preserver `ab`.  Because `M'` is itself a `MatchingCut`, a proof of this
predicate includes the obligation that both new sides are still matchings. -/
def IsFlipAt (M M' : MatchingCut G) (a b : V) : Prop :=
  M.IsCutPreserver a b ∧ M'.side = M.side ∆ ({a, b} : Set V)

/-- Reachability by zero or more valid cut-preserver flips.  Colors are
recomputed at every intermediate `MatchingCut`. -/
inductive FlipReachable (M : MatchingCut G) : MatchingCut G → Prop
  | refl : FlipReachable M M
  | step {M₁ M₂ : MatchingCut G} {a b : V} :
      FlipReachable M M₁ → M₁.IsFlipAt M₂ a b → FlipReachable M M₂

/-- Complementing both cuts turns a flip at the red--blue edge `ab` into a
flip at the blue--red edge `ba`. -/
theorem IsFlipAt.swapSides {M N : MatchingCut G} {a b : V}
    (h : M.IsFlipAt N a b) :
    M.swapSides.IsFlipAt N.swapSides b a := by
  constructor
  · exact ⟨h.1.1.symm, by simpa using h.1.2.2,
      by simpa using h.1.2.1⟩
  · ext z
    simp only [swapSides_side, Set.mem_compl_iff, h.2,
      Set.mem_symmDiff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto

theorem FlipReachable.swapSides {M N : MatchingCut G}
    (h : M.FlipReachable N) : M.swapSides.FlipReachable N.swapSides := by
  induction h with
  | refl => exact .refl
  | step hreach hflip ih => exact .step ih hflip.swapSides

end MatchingCut

namespace GoodColoring

/-- Recover the matching cut represented by a good coloring. -/
noncomputable def toMatchingCut (C : GoodColoring G) : MatchingCut G where
  side := C.redSide
  subcubic := C.subcubic
  matching := by
    simpa [IsMatchingCut, IsMatchingColoring, GoodColoring.redSide] using C.matching

@[simp] theorem toMatchingCut_side (C : GoodColoring G) :
    C.toMatchingCut.side = C.redSide := rfl

@[simp] theorem toMatchingCut_color (C : GoodColoring G) :
    C.toMatchingCut.color = C.color := by
  funext v
  have hc := C.color_correct v
  cases h : C.color v <;> rw [h] at hc
  · simp [MatchingCut.color, colorOfCut, hc.1, hc.2, GoodColoring.redSide]
  · simp [MatchingCut.color, colorOfCut, hc.1, hc.2, GoodColoring.redSide]
  · simp [MatchingCut.color, colorOfCut, hc.1, hc.2, GoodColoring.redSide]
  · simp [MatchingCut.color, colorOfCut, hc.1, hc.2, GoodColoring.redSide]

end GoodColoring

end Subcubic
