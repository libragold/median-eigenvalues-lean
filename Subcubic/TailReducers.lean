import Subcubic.Pattern

open Set

namespace Subcubic

/-- Names of the positive tail reducers in the supplied catalog. -/
inductive PositiveTailReducerName
  | a
  | b
  | c
  | d
  | e
  | f
  | g
  | h
  | i
  | j
  | k
  | l
  | m
  | mMinus
  | n
  | o
  | p
  | q
  | r
  | s
  | t
  | u
  | v
  | w
  | x
  | y
  deriving DecidableEq, Repr

/-- Exact graph and color data for every positive tail reducer. -/
def positiveTailReducerData : PositiveTailReducerName → PatternData
  | .a => {
      label := "a+"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3), -- bd
        (2, 3) -- cd
      ]
    }
  | .b => {
      label := "b+"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3) -- bd
      ]
    }
  | .c => {
      label := "c+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 2), -- ac
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (2, 3) -- cd
      ]
    }
  | .d => {
      label := "d+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 4), -- be
        (2, 3) -- cd
      ]
    }
  | .e => {
      label := "e+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 4), -- ae
        (1, 2), -- bc
        (1, 4), -- be
        (2, 3) -- cd
      ]
    }
  | .f => {
      label := "f+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (2, 3) -- cd
      ]
    }
  | .g => {
      label := "g+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 4) -- be
      ]
    }
  | .h => {
      label := "h+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 4) -- be
      ]
    }
  | .i => {
      label := "i+"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 4), -- be
        (1, 5), -- bf
        (3, 4) -- de
      ]
    }
  | .j => {
      label := "j+"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 5), -- bf
        (3, 4) -- de
      ]
    }
  | .k => {
      label := "k+"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 4), -- be
        (1, 5) -- bf
      ]
    }
  | .l => {
      label := "l+"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .m => {
      label := "m+"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 5), -- bf
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .mMinus => {
      label := "m-minus+"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 4), -- be
        (3, 4) -- de
      ]
      reddish := [0] -- a
    }
  | .n => {
      label := "n+"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 5), -- bf
        (2, 4), -- ce
        (2, 6), -- cg
        (5, 6) -- fg
      ]
    }
  | .o => {
      label := "o+"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 2), -- bc
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 6), -- cg
        (3, 4) -- de
      ]
      reddish := [0] -- a
    }
  | .p => {
      label := "p+"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 7), -- ch
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .q => {
      label := "q+"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 2), -- bc
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 6), -- cg
        (2, 7), -- ch
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .r => {
      label := "r+"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 3), -- bd
        (1, 5), -- bf
        (2, 6), -- cg
        (2, 8), -- ci
        (4, 5), -- ef
        (6, 7) -- gh
      ]
      reddish := [0] -- a
    }
  | .s => {
      label := "s+"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 3), -- bd
        (1, 5), -- bf
        (2, 7), -- ch
        (2, 8), -- ci
        (4, 5), -- ef
        (6, 7) -- gh
      ]
      reddish := [0] -- a
    }
  | .t => {
      label := "t+"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 2), -- bc
        (1, 6), -- bg
        (1, 7), -- bh
        (2, 7), -- ch
        (2, 8), -- ci
        (5, 6) -- fg
      ]
      reddish := [0] -- a
    }
  | .u => {
      label := "u+"
      vertexCount := 10
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i, j.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 7), -- ah
        (1, 2), -- bc
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 7), -- ch
        (2, 9), -- cj
        (7, 8) -- hi
      ]
      reddish := [0] -- a
    }
  | .v => {
      label := "v+"
      vertexCount := 10
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 8), -- ai
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3), -- cd
        (2, 6), -- cg
        (2, 9), -- cj
        (3, 7), -- dh
        (3, 9), -- dj
        (5, 6), -- fg
        (7, 8) -- hi
      ]
    }
  | .w => {
      label := "w+"
      vertexCount := 11
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 10), -- ck
        (3, 8), -- di
        (3, 10), -- dk
        (6, 7), -- gh
        (8, 9) -- ij
      ]
    }
  | .x => {
      label := "x+"
      vertexCount := 11
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 5), -- bf
        (1, 7), -- bh
        (2, 6), -- cg
        (2, 9), -- cj
        (3, 7), -- dh
        (3, 8), -- di
        (3, 10), -- dk
        (7, 8), -- hi
        (9, 10) -- jk
      ]
      reddish := [3] -- d
    }
  | .y => {
      label := "y+"
      vertexCount := 12
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k, l.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 11), -- cl
        (3, 8), -- di
        (3, 10), -- dk
        (6, 7), -- gh
        (8, 9) -- ij
      ]
    }

/-- The exact colored induced pattern associated with a positive reducer name. -/
def positiveTailReducer (name : PositiveTailReducerName) : ColoredPattern :=
  (positiveTailReducerData name).toPattern

instance (name : PositiveTailReducerName) :
    DecidableRel (positiveTailReducer name).graph.Adj := by
  unfold positiveTailReducer PatternData.toPattern
  infer_instance

/-- Every listed positive reducer graph is subcubic. -/
theorem positiveTailReducer_subcubic (name : PositiveTailReducerName) :
    IsSubcubic (positiveTailReducer name).graph := by
  cases name <;>
    change IsSubcubic (graphOfEdges _) <;>
    intro v <;>
    unfold vertexDegree <;>
    rw [Set.ncard_eq_toFinset_card'] <;>
    native_decide +revert

/-! Generated induced-occurrence certificates for positive reducers
whose every nonedge follows from saturation or the matching cut. -/

theorem positiveA_automaticNonedges (x y : Fin (positiveTailReducer .a).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .a).graph.Adj x y) :
    (positiveTailReducer .a).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveB_automaticNonedges (x y : Fin (positiveTailReducer .b).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .b).graph.Adj x y) :
    (positiveTailReducer .b).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveD_automaticNonedges (x y : Fin (positiveTailReducer .d).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .d).graph.Adj x y) :
    (positiveTailReducer .d).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveE_automaticNonedges (x y : Fin (positiveTailReducer .e).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .e).graph.Adj x y) :
    (positiveTailReducer .e).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveF_automaticNonedges (x y : Fin (positiveTailReducer .f).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .f).graph.Adj x y) :
    (positiveTailReducer .f).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveH_automaticNonedges (x y : Fin (positiveTailReducer .h).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .h).graph.Adj x y) :
    (positiveTailReducer .h).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveI_automaticNonedges (x y : Fin (positiveTailReducer .i).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .i).graph.Adj x y) :
    (positiveTailReducer .i).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveJ_automaticNonedges (x y : Fin (positiveTailReducer .j).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .j).graph.Adj x y) :
    (positiveTailReducer .j).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveK_automaticNonedges (x y : Fin (positiveTailReducer .k).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .k).graph.Adj x y) :
    (positiveTailReducer .k).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveV_automaticNonedges (x y : Fin (positiveTailReducer .v).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .v).graph.Adj x y) :
    (positiveTailReducer .v).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveW_automaticNonedges (x y : Fin (positiveTailReducer .w).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .w).graph.Adj x y) :
    (positiveTailReducer .w).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem positiveY_automaticNonedges (x y : Fin (positiveTailReducer .y).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .y).graph.Adj x y) :
    (positiveTailReducer .y).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

/-! Generated lists of the remaining boundary nonedges. -/

theorem positiveC_boundaryNonedges (x y : Fin (positiveTailReducer .c).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .c).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .c).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveG_boundaryNonedges (x y : Fin (positiveTailReducer .g).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .g).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .g).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveL_boundaryNonedges (x y : Fin (positiveTailReducer .l).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .l).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .l).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveM_boundaryNonedges (x y : Fin (positiveTailReducer .m).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .m).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .m).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveMMinus_boundaryNonedges (x y : Fin (positiveTailReducer .mMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .mMinus).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .mMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveN_boundaryNonedges (x y : Fin (positiveTailReducer .n).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .n).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .n).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveO_boundaryNonedges (x y : Fin (positiveTailReducer .o).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .o).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .o).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveP_boundaryNonedges (x y : Fin (positiveTailReducer .p).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .p).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .p).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveQ_boundaryNonedges (x y : Fin (positiveTailReducer .q).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .q).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .q).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveR_boundaryNonedges (x y : Fin (positiveTailReducer .r).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .r).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .r).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveS_boundaryNonedges (x y : Fin (positiveTailReducer .s).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .s).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .s).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveT_boundaryNonedges (x y : Fin (positiveTailReducer .t).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .t).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .t).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveU_boundaryNonedges (x y : Fin (positiveTailReducer .u).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .u).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .u).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

theorem positiveX_boundaryNonedges (x y : Fin (positiveTailReducer .x).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (positiveTailReducer .x).graph.Adj x y)
    (hauto : ¬ (positiveTailReducer .x).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨10, by native_decide⟩), (⟨3, by native_decide⟩, ⟨4, by native_decide⟩), (⟨3, by native_decide⟩, ⟨5, by native_decide⟩), (⟨3, by native_decide⟩, ⟨6, by native_decide⟩), (⟨3, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨10, by native_decide⟩), (⟨3, by native_decide⟩, ⟨4, by native_decide⟩), (⟨3, by native_decide⟩, ⟨5, by native_decide⟩), (⟨3, by native_decide⟩, ⟨6, by native_decide⟩), (⟨3, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

/-- Names of the negative tail reducers in the supplied catalog. -/
inductive NegativeTailReducerName
  | a0
  | a1
  | b
  | c
  | d
  | e
  | e0Minus
  | e1Minus
  | f
  | g
  | h
  | i
  | j
  | k
  | l1
  | m
  | n
  | o
  | p
  | q
  | r
  | s
  | s0Minus
  | s1Minus
  | s0Minus2
  | s1Minus2
  | t
  | u
  | uMinus
  | v
  | w0
  | w1
  | w0Minus
  | x
  | y
  | z
  | aa
  | ab
  | ac
  | ad
  | ae
  | af
  | ag
  | ah
  | ai
  | aj
  | ak
  | al
  | am
  | an
  | ao
  | abMinus
  | acMinus
  | adMinus
  | anMinus
  | anMinus2
  | l0
  deriving DecidableEq, Repr

/-- Exact graph and color data for every negative tail reducer. -/
def negativeTailReducerData : NegativeTailReducerName → PatternData
  | .a0 => {
      label := "a0-"
      vertexCount := 3
      sideCount := 1
      -- Red side: a. Blue side: b, c.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (1, 2) -- bc
      ]
      reddish := [0] -- a
    }
  | .a1 => {
      label := "a1-"
      vertexCount := 3
      sideCount := 1
      -- Red side: a. Blue side: b, c.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (1, 2) -- bc
      ]
    }
  | .b => {
      label := "b-"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3) -- bd
      ]
    }
  | .c => {
      label := "c-"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3) -- bd
      ]
    }
  | .d => {
      label := "d-"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 4) -- be
      ]
    }
  | .e => {
      label := "e-"
      vertexCount := 5
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3), -- bd
        (1, 4) -- be
      ]
      reddish := [1] -- b
    }
  | .e0Minus => {
      label := "e0-minus-"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3) -- bd
      ]
      reddish := [1] -- b
    }
  | .e1Minus => {
      label := "e1-minus-"
      vertexCount := 4
      sideCount := 2
      -- Red side: a, b. Blue side: c, d.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 2), -- bc
        (1, 3) -- bd
      ]
    }
  | .f => {
      label := "f-"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 4), -- be
        (1, 5), -- bf
        (3, 4) -- de
      ]
    }
  | .g => {
      label := "g-"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 4), -- be
        (1, 5) -- bf
      ]
    }
  | .h => {
      label := "h-"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 2), -- ac
        (0, 3), -- ad
        (1, 3), -- bd
        (1, 4), -- be
        (1, 5), -- bf
        (4, 5) -- ef
      ]
      reddish := [1] -- b
    }
  | .i => {
      label := "i-"
      vertexCount := 6
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3) -- cd
      ]
      reddish := [1] -- b
    }
  | .j => {
      label := "j-"
      vertexCount := 7
      sideCount := 2
      -- Red side: a, b. Blue side: c, d, e, f, g.
      edges := [
        (0, 2), -- ac
        (0, 4), -- ae
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (3, 4), -- de
        (5, 6) -- fg
      ]
      reddish := [1] -- b
    }
  | .k => {
      label := "k-"
      vertexCount := 6
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3), -- cd
        (2, 4), -- ce
        (2, 5), -- cf
        (3, 4) -- de
      ]
      reddish := [2] -- c
    }
  | .l1 => {
      label := "l1-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 5), -- bf
        (2, 4), -- ce
        (2, 6), -- cg
        (5, 6) -- fg
      ]
    }
  | .m => {
      label := "m-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6), -- cg
        (3, 4) -- de
      ]
    }
  | .n => {
      label := "n-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3), -- cd
        (2, 4), -- ce
        (2, 6), -- cg
        (3, 4) -- de
      ]
      reddish := [2] -- c
    }
  | .o => {
      label := "o-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 3), -- bd
        (1, 4), -- be
        (2, 5), -- cf
        (2, 6), -- cg
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .p => {
      label := "p-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [0] -- a
    }
  | .q => {
      label := "q-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 7), -- ch
        (4, 5) -- ef
      ]
      reddish := [0] -- a
    }
  | .r => {
      label := "r-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3), -- cd
        (2, 5), -- cf
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [2] -- c
    }
  | .s => {
      label := "s-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6), -- cg
        (2, 7) -- ch
      ]
      reddish := [2] -- c
    }
  | .s0Minus => {
      label := "s0-minus-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6) -- cg
      ]
      reddish := [2] -- c
    }
  | .s1Minus => {
      label := "s1-minus-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6) -- cg
      ]
    }
  | .s0Minus2 => {
      label := "s0-minus2-"
      vertexCount := 6
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5) -- cf
      ]
      reddish := [2] -- c
    }
  | .s1Minus2 => {
      label := "s1-minus2-"
      vertexCount := 6
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5) -- cf
      ]
    }
  | .t => {
      label := "t-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 7), -- ah
        (1, 4), -- be
        (1, 5), -- bf
        (2, 3), -- cd
        (2, 5), -- cf
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [2] -- c
    }
  | .u => {
      label := "u-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 6), -- cg
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [0, 1] -- a, b
    }
  | .uMinus => {
      label := "u-minus-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6), -- cg
        (4, 5) -- ef
      ]
      reddish := [0, 1] -- a, b
    }
  | .v => {
      label := "v-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 3), -- bd
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 7), -- ch
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .w0 => {
      label := "w0-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 6), -- cg
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [0, 1] -- a, b
    }
  | .w1 => {
      label := "w1-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 6), -- cg
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [1] -- b
    }
  | .w0Minus => {
      label := "w0-minus-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (1, 5), -- bf
        (2, 5), -- cf
        (2, 6), -- cg
        (4, 5) -- ef
      ]
      reddish := [0, 1] -- a, b
    }
  | .x => {
      label := "x-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 5), -- af
        (1, 3), -- bd
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 6), -- cg
        (2, 8), -- ci
        (4, 5), -- ef
        (6, 7) -- gh
      ]
      reddish := [2] -- c
    }
  | .y => {
      label := "y-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 6), -- cg
        (2, 8), -- ci
        (6, 7) -- gh
      ]
      reddish := [1] -- b
    }
  | .z => {
      label := "z-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 2), -- bc
        (1, 4), -- be
        (1, 5), -- bf
        (2, 6), -- cg
        (2, 8), -- ci
        (6, 7) -- gh
      ]
      reddish := [0] -- a
    }
  | .aa => {
      label := "aa-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 4), -- be
        (1, 5), -- bf
        (2, 6), -- cg
        (2, 7), -- ch
        (2, 8), -- ci
        (5, 6), -- fg
        (7, 8) -- hi
      ]
      reddish := [2] -- c
    }
  | .ab => {
      label := "ab-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 7), -- ch
        (2, 8), -- ci
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .ac => {
      label := "ac-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 5), -- af
        (0, 6), -- ag
        (1, 4), -- be
        (1, 5), -- bf
        (1, 7), -- bh
        (2, 6), -- cg
        (2, 8), -- ci
        (7, 8) -- hi
      ]
      reddish := [0, 1] -- a, b
    }
  | .ad => {
      label := "ad-"
      vertexCount := 9
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 5), -- af
        (1, 5), -- bf
        (1, 6), -- bg
        (1, 7), -- bh
        (2, 4), -- ce
        (2, 8), -- ci
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .ae => {
      label := "ae-"
      vertexCount := 10
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i, j.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 6), -- ag
        (1, 3), -- bd
        (1, 7), -- bh
        (2, 6), -- cg
        (2, 7), -- ch
        (2, 9), -- cj
        (5, 6), -- fg
        (7, 8) -- hi
      ]
      reddish := [2] -- c
    }
  | .af => {
      label := "af-"
      vertexCount := 10
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h, i, j.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (0, 7), -- ah
        (1, 2), -- bc
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 7), -- ch
        (2, 9), -- cj
        (7, 8) -- hi
      ]
      reddish := [0] -- a
    }
  | .ag => {
      label := "ag-"
      vertexCount := 10
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j.
      edges := [
        (0, 4), -- ae
        (0, 6), -- ag
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (1, 7), -- bh
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 8), -- ci
        (3, 8), -- di
        (3, 9), -- dj
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .ah => {
      label := "ah-"
      vertexCount := 10
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j.
      edges := [
        (0, 4), -- ae
        (0, 6), -- ag
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (1, 7), -- bh
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 8), -- ci
        (3, 4), -- de
        (3, 9), -- dj
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .ai => {
      label := "ai-"
      vertexCount := 11
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k.
      edges := [
        (0, 4), -- ae
        (0, 5), -- af
        (0, 6), -- ag
        (1, 6), -- bg
        (1, 7), -- bh
        (1, 10), -- bk
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 8), -- ci
        (3, 8), -- di
        (3, 9), -- dj
        (4, 5), -- ef
        (9, 10) -- jk
      ]
      reddish := [0, 1] -- a, b
    }
  | .aj => {
      label := "aj-"
      vertexCount := 11
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 10), -- ck
        (3, 8), -- di
        (3, 10), -- dk
        (6, 7), -- gh
        (8, 9) -- ij
      ]
    }
  | .ak => {
      label := "ak-"
      vertexCount := 12
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k, l.
      edges := [
        (0, 1), -- ab
        (0, 4), -- ae
        (0, 9), -- aj
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 3), -- cd
        (2, 7), -- ch
        (2, 11), -- cl
        (3, 8), -- di
        (3, 10), -- dk
        (6, 7), -- gh
        (8, 9) -- ij
      ]
    }
  | .al => {
      label := "al-"
      vertexCount := 12
      sideCount := 4
      -- Red side: a, b, c, d. Blue side: e, f, g, h, i, j, k, l.
      edges := [
        (0, 4), -- ae
        (0, 5), -- af
        (0, 7), -- ah
        (1, 6), -- bg
        (1, 7), -- bh
        (1, 8), -- bi
        (2, 3), -- cd
        (2, 8), -- ci
        (2, 9), -- cj
        (3, 10), -- dk
        (3, 11), -- dl
        (7, 8) -- hi
      ]
      reddish := [0, 1] -- a, b
    }
  | .am => {
      label := "am-"
      vertexCount := 12
      sideCount := 5
      -- Red side: a, b, c, d, e. Blue side: f, g, h, i, j, k, l.
      edges := [
        (0, 5), -- af
        (0, 7), -- ah
        (0, 8), -- ai
        (1, 2), -- bc
        (1, 6), -- bg
        (1, 10), -- bk
        (2, 6), -- cg
        (2, 7), -- ch
        (3, 4), -- de
        (3, 8), -- di
        (3, 11), -- dl
        (4, 9), -- ej
        (4, 11), -- el
        (7, 8), -- hi
        (9, 10) -- jk
      ]
      reddish := [0] -- a
    }
  | .an => {
      label := "an-"
      vertexCount := 14
      sideCount := 5
      -- Red side: a, b, c, d, e. Blue side: f, g, h, i, j, k, l, m, n.
      edges := [
        (0, 5), -- af
        (0, 6), -- ag
        (0, 8), -- ai
        (1, 7), -- bh
        (1, 8), -- bi
        (1, 9), -- bj
        (2, 3), -- cd
        (2, 9), -- cj
        (2, 10), -- ck
        (3, 10), -- dk
        (3, 11), -- dl
        (4, 10), -- ek
        (4, 12), -- em
        (4, 13), -- en
        (8, 9) -- ij
      ]
      reddish := [0, 1, 4] -- a, b, e
    }
  | .ao => {
      label := "ao-"
      vertexCount := 14
      sideCount := 5
      -- Red side: a, b, c, d, e. Blue side: f, g, h, i, j, k, l, m, n.
      edges := [
        (0, 5), -- af
        (0, 6), -- ag
        (0, 8), -- ai
        (1, 7), -- bh
        (1, 8), -- bi
        (1, 10), -- bk
        (2, 9), -- cj
        (2, 10), -- ck
        (2, 11), -- cl
        (3, 4), -- de
        (3, 11), -- dl
        (3, 12), -- dm
        (4, 8), -- ei
        (4, 13), -- en
        (10, 11) -- kl
      ]
      reddish := [0, 1, 2] -- a, b, c
    }
  | .abMinus => {
      label := "ab-minus-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 4), -- be
        (1, 5), -- bf
        (2, 6), -- cg
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [0, 1] -- a, b
    }
  | .acMinus => {
      label := "ac-minus-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 4), -- ae
        (0, 5), -- af
        (1, 3), -- bd
        (1, 4), -- be
        (1, 6), -- bg
        (2, 5), -- cf
        (2, 7), -- ch
        (6, 7) -- gh
      ]
      reddish := [0, 1] -- a, b
    }
  | .adMinus => {
      label := "ad-minus-"
      vertexCount := 8
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g, h.
      edges := [
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 4), -- be
        (1, 5), -- bf
        (1, 6), -- bg
        (2, 3), -- cd
        (2, 7), -- ch
        (5, 6) -- fg
      ]
      reddish := [0, 1] -- a, b
    }
  | .anMinus => {
      label := "an-minus-"
      vertexCount := 13
      sideCount := 5
      -- Red side: a, b, c, d, e. Blue side: f, g, h, i, j, k, l, m.
      edges := [
        (0, 5), -- af
        (0, 7), -- ah
        (1, 6), -- bg
        (1, 7), -- bh
        (1, 9), -- bj
        (2, 8), -- ci
        (2, 9), -- cj
        (2, 10), -- ck
        (3, 4), -- de
        (3, 10), -- dk
        (3, 11), -- dl
        (4, 7), -- eh
        (4, 12), -- em
        (9, 10) -- jk
      ]
      reddish := [0, 1, 2] -- a, b, c
    }
  | .anMinus2 => {
      label := "an-minus2-"
      vertexCount := 12
      sideCount := 5
      -- Red side: a, b, c, d, e. Blue side: f, g, h, i, j, k, l.
      edges := [
        (0, 6), -- ag
        (1, 5), -- bf
        (1, 6), -- bg
        (1, 8), -- bi
        (2, 7), -- ch
        (2, 8), -- ci
        (2, 9), -- cj
        (3, 4), -- de
        (3, 9), -- dj
        (3, 10), -- dk
        (4, 6), -- eg
        (4, 11), -- el
        (8, 9) -- ij
      ]
      reddish := [0, 1, 2] -- a, b, c
    }
  | .l0 => {
      label := "l0-"
      vertexCount := 7
      sideCount := 3
      -- Red side: a, b, c. Blue side: d, e, f, g.
      edges := [
        (0, 1), -- ab
        (0, 3), -- ad
        (0, 4), -- ae
        (1, 3), -- bd
        (1, 5), -- bf
        (2, 4), -- ce
        (2, 6), -- cg
        (5, 6) -- fg
      ]
      reddish := [2] -- c
    }

/-- The exact colored induced pattern associated with a negative reducer name. -/
def negativeTailReducer (name : NegativeTailReducerName) : ColoredPattern :=
  (negativeTailReducerData name).toPattern

instance (name : NegativeTailReducerName) :
    DecidableRel (negativeTailReducer name).graph.Adj := by
  unfold negativeTailReducer PatternData.toPattern
  infer_instance

/-- Every listed negative reducer graph is subcubic. -/
theorem negativeTailReducer_subcubic (name : NegativeTailReducerName) :
    IsSubcubic (negativeTailReducer name).graph := by
  cases name <;>
    change IsSubcubic (graphOfEdges _) <;>
    intro v <;>
    unfold vertexDegree <;>
    rw [Set.ncard_eq_toFinset_card'] <;>
    native_decide +revert

/-! Generated induced-occurrence certificates for negative reducers
whose every nonedge follows from saturation or the matching cut. -/

theorem negativeA0_automaticNonedges (x y : Fin (negativeTailReducer .a0).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .a0).graph.Adj x y) :
    (negativeTailReducer .a0).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeA1_automaticNonedges (x y : Fin (negativeTailReducer .a1).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .a1).graph.Adj x y) :
    (negativeTailReducer .a1).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeC_automaticNonedges (x y : Fin (negativeTailReducer .c).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .c).graph.Adj x y) :
    (negativeTailReducer .c).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeF_automaticNonedges (x y : Fin (negativeTailReducer .f).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .f).graph.Adj x y) :
    (negativeTailReducer .f).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeG_automaticNonedges (x y : Fin (negativeTailReducer .g).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .g).graph.Adj x y) :
    (negativeTailReducer .g).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeK_automaticNonedges (x y : Fin (negativeTailReducer .k).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .k).graph.Adj x y) :
    (negativeTailReducer .k).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeAj_automaticNonedges (x y : Fin (negativeTailReducer .aj).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .aj).graph.Adj x y) :
    (negativeTailReducer .aj).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

theorem negativeAk_automaticNonedges (x y : Fin (negativeTailReducer .ak).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ak).graph.Adj x y) :
    (negativeTailReducer .ak).AutomaticallyForcesNonedge x y := by
  revert x y
  native_decide

/-! Generated lists of the remaining boundary nonedges. -/

theorem negativeB_boundaryNonedges (x y : Fin (negativeTailReducer .b).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .b).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .b).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeD_boundaryNonedges (x y : Fin (negativeTailReducer .d).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .d).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .d).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeE_boundaryNonedges (x y : Fin (negativeTailReducer .e).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .e).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .e).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeE0Minus_boundaryNonedges (x y : Fin (negativeTailReducer .e0Minus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .e0Minus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .e0Minus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeE1Minus_boundaryNonedges (x y : Fin (negativeTailReducer .e1Minus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .e1Minus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .e1Minus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeH_boundaryNonedges (x y : Fin (negativeTailReducer .h).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .h).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .h).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeI_boundaryNonedges (x y : Fin (negativeTailReducer .i).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .i).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .i).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeJ_boundaryNonedges (x y : Fin (negativeTailReducer .j).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .j).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .j).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeL1_boundaryNonedges (x y : Fin (negativeTailReducer .l1).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .l1).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .l1).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeM_boundaryNonedges (x y : Fin (negativeTailReducer .m).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .m).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .m).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeN_boundaryNonedges (x y : Fin (negativeTailReducer .n).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .n).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .n).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeO_boundaryNonedges (x y : Fin (negativeTailReducer .o).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .o).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .o).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeP_boundaryNonedges (x y : Fin (negativeTailReducer .p).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .p).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .p).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeQ_boundaryNonedges (x y : Fin (negativeTailReducer .q).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .q).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .q).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeR_boundaryNonedges (x y : Fin (negativeTailReducer .r).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .r).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .r).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeS_boundaryNonedges (x y : Fin (negativeTailReducer .s).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .s).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .s).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeS0Minus_boundaryNonedges (x y : Fin (negativeTailReducer .s0Minus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .s0Minus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .s0Minus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeS1Minus_boundaryNonedges (x y : Fin (negativeTailReducer .s1Minus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .s1Minus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .s1Minus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeS0Minus2_boundaryNonedges (x y : Fin (negativeTailReducer .s0Minus2).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .s0Minus2).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .s0Minus2).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeS1Minus2_boundaryNonedges (x y : Fin (negativeTailReducer .s1Minus2).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .s1Minus2).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .s1Minus2).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeT_boundaryNonedges (x y : Fin (negativeTailReducer .t).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .t).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .t).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeU_boundaryNonedges (x y : Fin (negativeTailReducer .u).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .u).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .u).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeUMinus_boundaryNonedges (x y : Fin (negativeTailReducer .uMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .uMinus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .uMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeV_boundaryNonedges (x y : Fin (negativeTailReducer .v).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .v).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .v).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeW0_boundaryNonedges (x y : Fin (negativeTailReducer .w0).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .w0).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .w0).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeW1_boundaryNonedges (x y : Fin (negativeTailReducer .w1).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .w1).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .w1).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeW0Minus_boundaryNonedges (x y : Fin (negativeTailReducer .w0Minus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .w0Minus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .w0Minus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeX_boundaryNonedges (x y : Fin (negativeTailReducer .x).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .x).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .x).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeY_boundaryNonedges (x y : Fin (negativeTailReducer .y).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .y).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .y).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeZ_boundaryNonedges (x y : Fin (negativeTailReducer .z).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .z).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .z).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAa_boundaryNonedges (x y : Fin (negativeTailReducer .aa).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .aa).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .aa).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨1, by native_decide⟩), (⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAb_boundaryNonedges (x y : Fin (negativeTailReducer .ab).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ab).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ab).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAc_boundaryNonedges (x y : Fin (negativeTailReducer .ac).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ac).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ac).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨4, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAd_boundaryNonedges (x y : Fin (negativeTailReducer .ad).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ad).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ad).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAe_boundaryNonedges (x y : Fin (negativeTailReducer .ae).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ae).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ae).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAf_boundaryNonedges (x y : Fin (negativeTailReducer .af).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .af).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .af).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAg_boundaryNonedges (x y : Fin (negativeTailReducer .ag).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ag).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ag).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAh_boundaryNonedges (x y : Fin (negativeTailReducer .ah).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ah).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ah).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAi_boundaryNonedges (x y : Fin (negativeTailReducer .ai).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ai).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ai).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAl_boundaryNonedges (x y : Fin (negativeTailReducer .al).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .al).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .al).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨4, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAm_boundaryNonedges (x y : Fin (negativeTailReducer .am).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .am).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .am).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAn_boundaryNonedges (x y : Fin (negativeTailReducer .an).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .an).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .an).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨0, by native_decide⟩, ⟨13, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨13, by native_decide⟩), (⟨4, by native_decide⟩, ⟨5, by native_decide⟩), (⟨4, by native_decide⟩, ⟨6, by native_decide⟩), (⟨4, by native_decide⟩, ⟨7, by native_decide⟩), (⟨4, by native_decide⟩, ⟨11, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨0, by native_decide⟩, ⟨13, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨13, by native_decide⟩), (⟨4, by native_decide⟩, ⟨5, by native_decide⟩), (⟨4, by native_decide⟩, ⟨6, by native_decide⟩), (⟨4, by native_decide⟩, ⟨7, by native_decide⟩), (⟨4, by native_decide⟩, ⟨11, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAo_boundaryNonedges (x y : Fin (negativeTailReducer .ao).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .ao).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .ao).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨0, by native_decide⟩, ⟨13, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨13, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨12, by native_decide⟩), (⟨2, by native_decide⟩, ⟨13, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨9, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨0, by native_decide⟩, ⟨13, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨9, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨13, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨8, by native_decide⟩), (⟨2, by native_decide⟩, ⟨12, by native_decide⟩), (⟨2, by native_decide⟩, ⟨13, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAbMinus_boundaryNonedges (x y : Fin (negativeTailReducer .abMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .abMinus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .abMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨6, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAcMinus_boundaryNonedges (x y : Fin (negativeTailReducer .acMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .acMinus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .acMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨3, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAdMinus_boundaryNonedges (x y : Fin (negativeTailReducer .adMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .adMinus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .adMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨2, by native_decide⟩), (⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨2, by native_decide⟩), (⟨1, by native_decide⟩, ⟨3, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨4, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAnMinus_boundaryNonedges (x y : Fin (negativeTailReducer .anMinus).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .anMinus).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .anMinus).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨11, by native_decide⟩), (⟨2, by native_decide⟩, ⟨12, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨6, by native_decide⟩), (⟨0, by native_decide⟩, ⟨8, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨0, by native_decide⟩, ⟨12, by native_decide⟩), (⟨1, by native_decide⟩, ⟨5, by native_decide⟩), (⟨1, by native_decide⟩, ⟨8, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨12, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨7, by native_decide⟩), (⟨2, by native_decide⟩, ⟨11, by native_decide⟩), (⟨2, by native_decide⟩, ⟨12, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeAnMinus2_boundaryNonedges (x y : Fin (negativeTailReducer .anMinus2).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .anMinus2).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .anMinus2).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨10, by native_decide⟩), (⟨2, by native_decide⟩, ⟨11, by native_decide⟩)] ∨ (y, x) ∈ [(⟨0, by native_decide⟩, ⟨5, by native_decide⟩), (⟨0, by native_decide⟩, ⟨7, by native_decide⟩), (⟨0, by native_decide⟩, ⟨10, by native_decide⟩), (⟨0, by native_decide⟩, ⟨11, by native_decide⟩), (⟨1, by native_decide⟩, ⟨7, by native_decide⟩), (⟨1, by native_decide⟩, ⟨10, by native_decide⟩), (⟨1, by native_decide⟩, ⟨11, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩), (⟨2, by native_decide⟩, ⟨6, by native_decide⟩), (⟨2, by native_decide⟩, ⟨10, by native_decide⟩), (⟨2, by native_decide⟩, ⟨11, by native_decide⟩)] := by
  revert x y
  native_decide

theorem negativeL0_boundaryNonedges (x y : Fin (negativeTailReducer .l0).vertexCount)
    (hne : x ≠ y) (hxy : ¬ (negativeTailReducer .l0).graph.Adj x y)
    (hauto : ¬ (negativeTailReducer .l0).AutomaticallyForcesNonedge x y) :
    (x, y) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] ∨ (y, x) ∈ [(⟨2, by native_decide⟩, ⟨3, by native_decide⟩), (⟨2, by native_decide⟩, ⟨5, by native_decide⟩)] := by
  revert x y
  native_decide

/-- Membership in the complete supplied catalog of positive tail reducers. -/
def IsPositiveTailReducer (P : ColoredPattern) : Prop :=
  ∃ name, P = positiveTailReducer name

/-- Membership in the complete supplied catalog of negative tail reducers. -/
def IsNegativeTailReducer (P : ColoredPattern) : Prop :=
  ∃ name, P = negativeTailReducer name

theorem IsPositiveTailReducer.subcubic {P : ColoredPattern}
    (hP : IsPositiveTailReducer P) : IsSubcubic P.graph := by
  obtain ⟨name, rfl⟩ := hP
  exact positiveTailReducer_subcubic name

theorem IsNegativeTailReducer.subcubic {P : ColoredPattern}
    (hP : IsNegativeTailReducer P) : IsSubcubic P.graph := by
  obtain ⟨name, rfl⟩ := hP
  exact negativeTailReducer_subcubic name

/-- An induced positive reducer in the catalog's displayed orientation. -/
def ContainsOrientedPositiveTailReducer {V : Type*} [Fintype V]
    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ∃ P, IsPositiveTailReducer P ∧ P.OccursInduced C

/-- An induced positive reducer, allowing all colors to be exchanged. -/
def ContainsPositiveTailReducer {V : Type*} [Fintype V]
    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ContainsInducedUpToSwap IsPositiveTailReducer C

/-- An induced negative reducer in the catalog's displayed orientation. -/
def ContainsOrientedNegativeTailReducer {V : Type*} [Fintype V]
    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ∃ P, IsNegativeTailReducer P ∧ P.OccursInduced C

/-- An induced negative reducer, allowing all colors to be exchanged. -/
def ContainsNegativeTailReducer {V : Type*} [Fintype V]
    {G : SimpleGraph V} (C : GoodColoring G) : Prop :=
  ContainsInducedUpToSwap IsNegativeTailReducer C

/-! Named color checks for exceptional entries. -/

@[simp] theorem negativeA0_color_a :
    (negativeTailReducer .a0).color ⟨0, by native_decide⟩ = .reddish := by
  native_decide

@[simp] theorem negativeA1_color_a :
    (negativeTailReducer .a1).color ⟨0, by native_decide⟩ = .red := by
  native_decide

@[simp] theorem negativeW0_color_a :
    (negativeTailReducer .w0).color ⟨0, by native_decide⟩ = .reddish := by
  native_decide

@[simp] theorem negativeW0_color_b :
    (negativeTailReducer .w0).color ⟨1, by native_decide⟩ = .reddish := by
  native_decide

@[simp] theorem negativeW1_color_a :
    (negativeTailReducer .w1).color ⟨0, by native_decide⟩ = .red := by
  native_decide

@[simp] theorem negativeW1_color_b :
    (negativeTailReducer .w1).color ⟨1, by native_decide⟩ = .reddish := by
  native_decide

end Subcubic
