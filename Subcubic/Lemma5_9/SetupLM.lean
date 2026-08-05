import Subcubic.Lemma5_9.CaseKJBlueFlip

/-! Lemma 5.9, Case (3.4.4): expose the other two neighbors of `k`. -/

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

structure Lemma5_9LMConfiguration (C : GoodColoring G)
    (a b c d e f g h : V) extends
    Lemma5_9KConfiguration C a b c d e f g h where
  hkj : ¬ G.Adj k j
  hkh : ¬ G.Adj k h
  l : V
  m : V
  hkl : G.Adj k l
  hkm : G.Adj k m
  hlc : l ≠ c
  hmc : m ≠ c
  hlm : l ≠ m
  hlSide : C.color l = .blue ∨ C.color l = .bluish
  hmSide : C.color m = .blue ∨ C.color m = .bluish

theorem lemma5_9_setup_lm
    (C : GoodColoring G) {a b c d e f g h : V}
    (Q : Lemma5_9KConfiguration C a b c d e f g h)
    (hkj : ¬ G.Adj Q.k Q.j) (hkh : ¬ G.Adj Q.k h) :
    Nonempty (Lemma5_9LMConfiguration C a b c d e f g h) := by
  obtain ⟨l, m, hkl, hkm, hlc, hmc, hlm⟩ :=
    exists_two_other_neighbors_of_degree_three Q.hkdeg Q.hck.symm
  have side {z : V} (hkz : G.Adj Q.k z) :
      C.color z = .blue ∨ C.color z = .bluish := by
    rw [← C.not_mem_redSide_iff]
    intro hz
    have hkCorrect := C.color_correct Q.k
    rw [Q.hk] at hkCorrect
    exact hkCorrect.2 ⟨z, hz, hkz⟩
  exact ⟨{ Q with
    hkj := hkj, hkh := hkh, l := l, m := m,
    hkl := hkl, hkm := hkm, hlc := hlc, hmc := hmc, hlm := hlm,
    hlSide := side hkl, hmSide := side hkm }⟩

end Subcubic
