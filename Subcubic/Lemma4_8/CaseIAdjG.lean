import Subcubic.Lemma4_8.ThirdNeighbors

namespace Subcubic

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The first case in the proof: the reddish third neighbor of `d` is also
adjacent to `g`, giving the color-reversed copy of positive reducer `c+`. -/
theorem lemma4_8_case_i_adj_g
    (C : MatchingCutColoring G) {d e f g i : V}
    (hd : C.color d = .blue) (he : C.color e = .red)
    (hf : C.color f = .red) (hg : C.color g = .blue)
    (hi : C.color i = .reddish)
    (hde : G.Adj d e) (hdi : G.Adj d i)
    (hfg : G.Adj f g) (hgi : G.Adj g i) (hef : G.Adj e f)
    (hdg : ¬ G.Adj d g) (hdf : ¬ G.Adj d f)
    (hge : ¬ G.Adj g e) (hn : [d, g, e, f, i].Nodup) :
    HasReachableReduction C := by
  have hei : ¬ G.Adj e i := fun hei =>
    C.reddish_not_adj_redSide hi (Or.inl he) hei.symm
  have hfi : ¬ G.Adj f i := fun hfi =>
    C.reddish_not_adj_redSide hi (Or.inl hf) hfi.symm
  have heg : ¬ G.Adj e g := fun heg => hge heg.symm
  have hptr : ContainsPositiveTailReducer C := by
    refine ⟨positiveTailReducer .c, ⟨.c, rfl⟩, Or.inr ?_⟩
    refine ⟨[d, g, e, f, i].get, hn.injective_get, ?_, ?_, by
      intro x d hdegree; exfalso; revert hdegree; native_decide +revert⟩
    · intro x y
      fin_cases x <;> fin_cases y <;>
        simp [ColoredPattern.swapSides, positiveTailReducer,
          positiveTailReducerData, PatternData.toPattern, graphOfEdges,
          G.adj_comm, hde, hdi, hfg, hgi, hef,
          hdg, hdf, heg, hei, hfi]
    · intro x
      have hcolors : (positiveTailReducer .c).swapSides.color =
          ![.blue, .blue, .red, .red, .reddish] := by native_decide
      rw [hcolors]
      fin_cases x <;> simp [hd, he, hf, hg, hi] <;> native_decide
  exact HasReachableReduction.of_current_ptr C hptr

end Subcubic
