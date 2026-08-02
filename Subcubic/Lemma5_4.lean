import Subcubic.Lemma5_4.ReddishF

/-!
# Lemma 5.4

The complete case split for the negative-tail analogue of Lemma 4.4.
The conclusion exposes one residual configuration in Case 2.2.5.3.3: the
printed cut-enhancer argument requires the induced nonedge `h-k`, whereas the
hypotheses also permit `h-k` to be the red matching edge.
-/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- **Lemma 5.4, audited form.** Let `ab` be an isolated red edge.  Then a
negative tail reducer or cut enhancer is reachable by cut-preserver flips,
unless the explicit unresolved configuration from Case 2.2.5.3.3 occurs. -/
theorem lemma5_4_or_residual
    (C : GoodColoring G) {a b : V}
    (ha : C.color a = .red) (hb : C.color b = .red) (hab : G.Adj a b)
    (ha_other : ∀ v, G.Adj a v → v ≠ b → C.color v = .bluish)
    (hb_other : ∀ v, G.Adj b v → v ≠ a → C.color v = .bluish) :
    HasReachableNegativeReduction C ∨ Nonempty (Lemma5_4Residual C) := by
  rcases lemma5_4_initial C ha hb hab ha_other hb_other with hdone | hconfig
  · exact Or.inl hdone
  · obtain ⟨Q⟩ := hconfig
    by_cases hblue : ∃ g, C.color g = .blue ∧ G.Adj Q.f g
    · obtain ⟨g, hg, hfg⟩ := hblue
      by_cases hfe : G.Adj Q.f Q.e
      · exact Or.inl (lemma5_4_blue_meets_e C ha hb hab Q hfe hg hfg)
      · by_cases hfc : G.Adj Q.f Q.c
        · exact Or.inl
            (lemma5_4_blue_meets_e C hb ha hab.symm Q.reverse hfc hg hfg)
        · rcases Q.hf with hf | hf
          · exact Or.inl (lemma5_4_red_f_blue_neighbor C ha hb hab Q hf hg hfg)
          · exact lemma5_4_reddish_f_blue_neighbor C ha hb hab Q hf hg hfg hfc hfe
    · have hnoBlue : ∀ v, G.Adj Q.f v → C.color v ≠ .blue := by
        intro v hfv hv
        exact hblue ⟨v, hv, hfv⟩
      by_cases hfe : G.Adj Q.f Q.e
      · exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
          (lemma5_4_noBlue_meets_e C ha hb hab Q hfe hnoBlue))
      · by_cases hfc : G.Adj Q.f Q.c
        · exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
            (lemma5_4_noBlue_meets_e C hb ha hab.symm Q.reverse hfc hnoBlue))
        · exact Or.inl (HasReachableNegativeReduction.of_current_ntr C
            (lemma5_4_noBlue_meets_neither C ha hb hab Q hfc hfe hnoBlue))

end Subcubic
