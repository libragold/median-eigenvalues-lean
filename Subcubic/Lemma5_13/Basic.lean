import Subcubic.Lemma4_12.Basic
import Subcubic.NegativeReduction

/-! Shared local configuration for Lemma 5.13. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The two third neighbors introduced at the start of Lemma 5.13. -/
abbrev Lemma5_13ThirdNeighborConfiguration (C : MatchingCutColoring G)
    (a b c d : V) := Lemma4_12ThirdNeighborConfiguration C a b c d

end Subcubic
