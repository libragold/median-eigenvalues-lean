import Subcubic.Lemma4_8.Cases1And2Setup3
import Subcubic.Lemma5_6
import Subcubic.NegativeReduction

/-!
# Lemma 5.9: basic configuration

Lemma 5.9 uses the same induced eight-vertex path and the same third-neighbor
configuration as Lemma 4.8.  We deliberately reuse that data structure: only
the reducer sought by the case analysis changes from positive to negative.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

abbrev Lemma5_9Case3Configuration (C : MatchingCutColoring G)
    (a b c d e f g h : V) :=
  Lemma4_8Case3Configuration C a b c d e f g h

omit [Fintype V] in
theorem FormsInducedPath8.prefix6 {a b c d e f g h : V}
    (hp : FormsInducedPath8 G a b c d e f g h) :
    FormsInducedPath6 G a b c d e f := by
  classical
  dsimp [FormsInducedPath8, FormsInducedPath6] at hp ⊢
  rcases hp with ⟨hinj, hedge⟩
  let ι : Fin 6 → Fin 8 := fun x => ⟨x, by omega⟩
  have hι : Function.Injective ι := by
    intro x y hxy
    exact Fin.ext (by simpa [ι] using congrArg Fin.val hxy)
  have hmap (x : Fin 6) :
      ![a, b, c, d, e, f] x = ![a, b, c, d, e, f, g, h] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hι
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

omit [Fintype V] in
theorem FormsInducedPath8.suffix6 {a b c d e f g h : V}
    (hp : FormsInducedPath8 G a b c d e f g h) :
    FormsInducedPath6 G c d e f g h := by
  classical
  dsimp [FormsInducedPath8, FormsInducedPath6] at hp ⊢
  rcases hp with ⟨hinj, hedge⟩
  let ι : Fin 6 → Fin 8 := ![2, 3, 4, 5, 6, 7]
  have hι : Function.Injective ι := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [ι]
  have hmap (x : Fin 6) :
      ![c, d, e, f, g, h] x = ![a, b, c, d, e, f, g, h] (ι x) := by
    fin_cases x <;> rfl
  refine ⟨?_, ?_⟩
  · intro x y hxy
    apply hι
    apply hinj
    simpa [hmap] using hxy
  · intro x y
    rw [hmap x, hmap y, ← hedge]
    fin_cases x <;> fin_cases y <;> simp [ι, graphOfEdges]

end Subcubic
