import Subcubic.Lemma4_8.Initial
import Subcubic.TailReducerWitnesses

/-!
# Lemma 4.8: the direct cases (3.1)--(3.3)

This module removes the three configurations dealt with before the long
case (3.4): a shared third neighbor of `a,b`, an edge `i-j`, or both edges
`i-c` and `j-f`.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The residual data after cases (3.1)--(3.3). -/
structure Lemma4_8LateConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8DeepConfiguration C a b c d e f g h where
  hxy : x ≠ y
  hij : ¬ G.Adj i j
  hnotBoth : ¬ (G.Adj i c ∧ G.Adj j f)


end Subcubic
