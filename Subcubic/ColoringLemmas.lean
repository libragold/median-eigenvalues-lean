import Subcubic.Basic
import Mathlib.Tactic.FinCases

/-!
# Reusable facts about good colorings

This file contains graph- and color-theoretic consequences of `GoodColoring`.
It deliberately contains no tail-reducer or cut-enhancer data, so later local
configuration proofs can reuse these results without importing a catalog.
-/

namespace Subcubic

open Set

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- In a subcubic graph, three displayed distinct neighbors exclude every
fourth distinct neighbor; no color or exact-degree hypothesis is needed. -/
theorem not_adj_fourth_neighbor_of_subcubic
    (hsub : IsSubcubic G) {v x y z w : V}
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    ¬ G.Adj v w := by
  intro hvw
  have hsubset : ({x, y, z, w} : Set V) ⊆ G.neighborSet v := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact hvx
    · exact hvy
    · exact hvz
    · exact hvw
  have hcard : ({x, y, z, w} : Set V).ncard = 4 := by
    exact Set.ncard_eq_four.2 ⟨x, y, z, w, hxy, hxz, Ne.symm hwx,
      hyz, Ne.symm hwy, Ne.symm hwz, rfl⟩
  have hlower := Set.ncard_le_ncard hsubset
  have hupper := hsub v
  unfold vertexDegree at hupper
  omega

/-- A vertex on the red side cannot have two distinct red-side neighbors. -/
theorem GoodColoring.redSide_not_adj_second_neighbor
    (C : GoodColoring G) {v x y : V}
    (hv : v ∈ C.redSide) (hx : x ∈ C.redSide) (hy : y ∈ C.redSide)
    (hvx : G.Adj v x) (hxy : x ≠ y) :
    ¬ G.Adj v y := by
  intro hvy
  have hsubset : ({x, y} : Set V) ⊆
      G.neighborSet v ∩ redSideOf C.color := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact ⟨hvx, hx⟩
    · exact ⟨hvy, hy⟩
  have hlower := Set.ncard_le_ncard hsubset
  have hupper := C.matching.1 v hv
  rw [Set.ncard_pair hxy] at hlower
  omega

/-- A vertex on the blue side cannot have two distinct blue-side neighbors. -/
theorem GoodColoring.blueSide_not_adj_second_neighbor
    (C : GoodColoring G) {v x y : V}
    (hv : v ∉ C.redSide) (hx : x ∉ C.redSide) (hy : y ∉ C.redSide)
    (hvx : G.Adj v x) (hxy : x ≠ y) :
    ¬ G.Adj v y := by
  intro hvy
  have hsubset : ({x, y} : Set V) ⊆
      G.neighborSet v ∩ (redSideOf C.color)ᶜ := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · refine ⟨hvx, ?_⟩
      exact hx
    · refine ⟨hvy, ?_⟩
      exact hy
  have hlower := Set.ncard_le_ncard hsubset
  have hupper := C.matching.2 v hv
  rw [Set.ncard_pair hxy] at hlower
  omega

/-- A bluish vertex has no neighbor whose color is blue or bluish. -/
@[simp] theorem GoodColoring.bluish_not_adj_blueSide
    (C : GoodColoring G) {v w : V}
    (hv : C.color v = .bluish)
    (hw : C.color w = .blue ∨ C.color w = .bluish) :
    ¬ G.Adj v w := by
  have hv_correct := C.color_correct v
  rw [hv] at hv_correct
  rcases hv_correct with ⟨_, hnone⟩
  intro hvw
  apply hnone
  refine ⟨w, ?_, hvw⟩
  change w ∉ C.redSide
  exact (C.not_mem_redSide_iff w).2 hw

/-- A reddish vertex has no neighbor whose color is red or reddish. -/
@[simp] theorem GoodColoring.reddish_not_adj_redSide
    (C : GoodColoring G) {v w : V}
    (hv : C.color v = .reddish)
    (hw : C.color w = .red ∨ C.color w = .reddish) :
    ¬ G.Adj v w := by
  have hv_correct := C.color_correct v
  rw [hv] at hv_correct
  rcases hv_correct with ⟨_, hnone⟩
  intro hvw
  apply hnone
  refine ⟨w, ?_, hvw⟩
  change w ∈ C.redSide
  exact (C.mem_redSide_iff w).2 hw

/-- A red vertex already using its red-side edge can only have any distinct
additional neighbor on the blue side. -/
theorem GoodColoring.other_neighbor_of_red_is_blueSide
    (C : GoodColoring G) {v x y : V}
    (hv : C.color v = .red) (hx : C.color x = .red)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hyx : y ≠ x) :
    C.color y = .blue ∨ C.color y = .bluish := by
  rw [← C.not_mem_redSide_iff]
  intro hy
  have hv' : v ∈ C.redSide := by simp [hv]
  have hx' : x ∈ C.redSide := by simp [hx]
  exact (C.redSide_not_adj_second_neighbor hv' hx' hy hvx hyx.symm) hvy

/-- The red/blue reverse of `other_neighbor_of_red_is_blueSide`. -/
theorem GoodColoring.other_neighbor_of_blue_is_redSide
    (C : GoodColoring G) {v x y : V}
    (hv : C.color v = .blue) (hx : C.color x = .blue)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hyx : y ≠ x) :
    C.color y = .red ∨ C.color y = .reddish := by
  rw [← C.mem_redSide_iff]
  by_contra hy
  have hv' : v ∉ C.redSide := by simp [hv]
  have hx' : x ∉ C.redSide := by simp [hx]
  exact (C.blueSide_not_adj_second_neighbor hv' hx' hy hvx hyx.symm) hvy

/-- A red or blue vertex has degree three, so outside any two distinct
vertices it has another neighbor. -/
theorem GoodColoring.exists_third_neighbor
    (C : GoodColoring G) {v x y : V}
    (hv : C.color v = .red ∨ C.color v = .blue)
    (hxy : x ≠ y) :
    ∃ z, G.Adj v z ∧ z ≠ x ∧ z ≠ y := by
  have hdegree : (G.neighborSet v).ncard = 3 := by
    simpa [vertexDegree] using C.red_or_blue_degree v hv
  by_contra h
  push Not at h
  have hsubset : G.neighborSet v ⊆ ({x, y} : Set V) := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (h z hz hzx)
  have hle := Set.ncard_le_ncard hsubset
  rw [hdegree, Set.ncard_pair hxy] at hle
  omega

/-- A red or blue vertex with one displayed neighbor has two distinct other
neighbors. -/
theorem GoodColoring.exists_two_other_neighbors
    (C : GoodColoring G) {v mate : V}
    (hv : C.color v = .red ∨ C.color v = .blue)
    (hvm : G.Adj v mate) :
    ∃ x y, G.Adj v x ∧ G.Adj v y ∧
      x ≠ mate ∧ y ≠ mate ∧ x ≠ y := by
  obtain ⟨x, hvx, hxmate, _⟩ :=
    C.exists_third_neighbor hv hvm.ne.symm
  obtain ⟨y, hvy, hymate, hyx⟩ :=
    C.exists_third_neighbor hv hxmate.symm
  exact ⟨x, y, hvx, hvy, hxmate, hymate, hyx.symm⟩

/-- A degree-three vertex with one displayed neighbor has two distinct other
neighbors.  Unlike `GoodColoring.exists_two_other_neighbors`, this version
also applies to a reddish or bluish vertex once its degree has separately
been established (as in Lemma 3.5). -/
theorem exists_two_other_neighbors_of_degree_three
    {v mate : V} (hdeg : vertexDegree G v = 3) (_hvm : G.Adj v mate) :
    ∃ x y, G.Adj v x ∧ G.Adj v y ∧
      x ≠ mate ∧ y ≠ mate ∧ x ≠ y := by
  have hcard : (G.neighborSet v).ncard = 3 := by
    simpa [vertexDegree] using hdeg
  have first : ∃ x, G.Adj v x ∧ x ≠ mate := by
    by_contra h
    push Not at h
    have hsubset : G.neighborSet v ⊆ ({mate} : Set V) := by
      intro z hz
      simp only [Set.mem_singleton_iff]
      by_contra hzm
      exact hzm (h z hz)
    have := Set.ncard_le_ncard hsubset
    simp [hcard] at this
  obtain ⟨x, hvx, hxm⟩ := first
  have second : ∃ y, G.Adj v y ∧ y ≠ mate ∧ y ≠ x := by
    by_contra h
    push Not at h
    have hsubset : G.neighborSet v ⊆ ({mate, x} : Set V) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hzm : z = mate
      · exact Or.inl hzm
      · exact Or.inr (by
          by_contra hzx
          exact hzx (h z hz hzm))
    have hle := Set.ncard_le_ncard hsubset
    rw [Set.ncard_pair hxm.symm, hcard] at hle
    omega
  obtain ⟨y, hvy, hym, hyx⟩ := second
  exact ⟨x, y, hvx, hvy, hxm, hym, hyx.symm⟩

/-- If a degree-three red or blue vertex already has three pairwise-distinct
displayed neighbors, it has no fourth neighbor. -/
theorem GoodColoring.not_adj_fourth_neighbor
    (C : GoodColoring G) {v x y z w : V}
    (hv : C.color v = .red ∨ C.color v = .blue)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hwx : w ≠ x) (hwy : w ≠ y) (hwz : w ≠ z) :
    ¬ G.Adj v w := by
  have hdegree : (G.neighborSet v).ncard = 3 := by
    simpa [vertexDegree] using C.red_or_blue_degree v hv
  have htriple : ({x, y, z} : Set V).ncard = 3 := by
    simp [hxy, hxz, hyz]
  have hsubset : ({x, y, z} : Set V) ⊆ G.neighborSet v := by
    intro q hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl
    · exact hvx
    · exact hvy
    · exact hvz
  have heq : ({x, y, z} : Set V) = G.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsubset (by omega)
  intro hvw
  have hwmem : w ∈ ({x, y, z} : Set V) := by
    rw [heq]
    exact hvw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwmem
  rcases hwmem with h | h | h
  · exact hwx h
  · exact hwy h
  · exact hwz h

/-- Every neighbor of a degree-three red or blue vertex is one of any three
displayed pairwise-distinct neighbors. -/
theorem GoodColoring.neighbor_eq_of_three_neighbors
    (C : GoodColoring G) {v x y z w : V}
    (hv : C.color v = .red ∨ C.color v = .blue)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hvw : G.Adj v w) : w = x ∨ w = y ∨ w = z := by
  by_cases hwx : w = x
  · exact Or.inl hwx
  by_cases hwy : w = y
  · exact Or.inr (Or.inl hwy)
  by_cases hwz : w = z
  · exact Or.inr (Or.inr hwz)
  exact (C.not_adj_fourth_neighbor hv hvx hvy hvz hxy hxz hyz
    hwx hwy hwz) hvw |>.elim

end Subcubic
