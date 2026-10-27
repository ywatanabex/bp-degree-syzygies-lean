import BPFixedPoints.Incidence.IncidenceEdgeMapTor

/-!
# Sanity check: two parallel edges mapped onto one edge

Let `G` be the multigraph on two vertices with two parallel edges `0 → 1`, and `H` the multigraph
on the same vertices with one edge `0 → 1`. The edge map `parallelEdgeMap : EdgeMap G H` sends both
edges of `G` to the edge of `H`. It is not injective on the two-edge set, so its wedge sign there is
zero (`e ∧ e = 0`), and the actual Tor class whose full state is the state of the two-edge set
(the unique state of that edge set, of twist `(2, 2)`) is nonzero and is sent to zero by the Tor map
(`parallelEdgeMap_twoEdgeClass`).
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp

/-- Two vertices joined by two parallel edges. -/
def parallelPair : Multigraph (Fin 2) (Fin 2) where
  fst _ := 0
  snd _ := 1

/-- Two vertices joined by one edge. -/
def singleEdge : Multigraph (Fin 2) (Fin 1) where
  fst _ := 0
  snd _ := 1

/-- The edge map sending both parallel edges to the single edge, without reversal. -/
def parallelEdgeMap : EdgeMap parallelPair singleEdge where
  edge _ := 0
  reversed _ := false
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The edge function of `parallelEdgeMap` is not injective on the two-edge set. -/
theorem parallelEdgeMap_not_injOn :
    ¬ Set.InjOn parallelEdgeMap.edge (Finset.univ : Finset (Fin 2)) := by
  intro h
  have : (0 : Fin 2) = 1 := h (by simp) (by simp) rfl
  exact absurd this (by decide)

/-- The wedge sign of the two-edge set is zero. -/
theorem parallelEdgeMap_wedgeSign_univ :
    parallelEdgeMap.wedgeSign (Finset.univ : Finset (Fin 2)) = 0 :=
  parallelEdgeMap.wedgeSign_of_not_injOn parallelEdgeMap_not_injOn

/-- Both vertices have degree two in the two-edge set. -/
theorem parallelPair_deg_univ (v : Fin 2) : parallelPair.deg Finset.univ v = 2 := by
  fin_cases v <;> decide

/-- The unique state of the two-edge set: twist `(2, 2)` has one-dimensional cohomology. -/
def twoEdgeState : parallelPair.IncResolutionBasis :=
  ⟨Finset.univ, fun v => ⟨0, by rw [parallelPair_deg_univ]; decide⟩⟩

/-- **Sanity check.** The actual Tor class of the two-edge state is nonzero, and the Tor map of the
edge map identifying the two parallel edges sends it to zero. -/
theorem parallelEdgeMap_twoEdgeClass :
    ∃ (p : ℕ) (y : parallelPair.incidenceTor p),
      parallelPair.incidenceTorFullState p y = single twoEdgeState 1 ∧ y ≠ 0 ∧
        parallelEdgeMap.incidenceTorEdgeMap p y = 0 := by
  let p := parallelPair.incResolutionDegree twoEdgeState
  obtain ⟨y, hy⟩ := parallelPair.exists_incidenceTorFullState_eq p (single twoEdgeState 1)
    (fun b hb => single_eq_of_ne (fun h => hb (h ▸ rfl)))
  refine ⟨p, y, hy, ?_, ?_⟩
  · intro h0
    have h1 := congrArg (fun z => z twoEdgeState) hy
    simp only [h0, map_zero, Finsupp.zero_apply, single_eq_same] at h1
    exact zero_ne_one h1
  · exact parallelEdgeMap.incidenceTorEdgeMap_eq_zero_of_single p y twoEdgeState 1 hy
      parallelEdgeMap_not_injOn

end BPFixedPoints.Multigraph
