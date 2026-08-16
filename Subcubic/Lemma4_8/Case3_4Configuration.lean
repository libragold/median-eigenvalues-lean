import Subcubic.Lemma4_8.Cases1And2Setup3
import Subcubic.PositiveTailReducerWitnesses

/-!
# Lemma 4.8: configuration entering Case (3.4)

The additional fields record the failure of Cases (3.1)--(3.3), leaving
exactly the configuration considered in the long Case (3.4).
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The configuration entering Case (3.4), after Cases (3.1)--(3.3) fail. -/
structure Lemma4_8Case3_4Configuration (C : MatchingCutColoring G)
    (a b c d e f g h : V) extends
    Lemma4_8Case3Configuration C a b c d e f g h where
  hxy : x ≠ y
  hij : ¬ G.Adj i j
  hnotBoth : ¬ (G.Adj i c ∧ G.Adj j f)


end Subcubic
