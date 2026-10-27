import BPFixedPoints.Incidence.IncidenceSignedEdgeMapTor

/-!
# Sanity check: two parallel loops mapped onto one loop with signs

A single non-loop edge has degree one at both endpoints, and `phi 1 = 0`, so the edge set of one
non-loop edge has no resolution states. To see single-edge states, take loops: let `loopPair` be the
multigraph on one vertex with two parallel loops `0, 1`, and `singleLoop` the multigraph on one
vertex with one loop. The edge set `{e}` of one loop has degree two at the vertex and a unique state
(`loopState e`, twist `2`), of homological degree zero; its Tor class `loopClass e ∈ Tor_0` is
nonzero.

For any edge sign `ε`, the signed edge map `loopPairMap ε` sends both loops to the loop. It is
injective on each one-loop edge set, with wedge sign one, so the image of `loopClass e` is
`ε_e` times the class of the unique one-loop state of `singleLoop`
(`loopPairMap_loopClass`): although both loops are identified, each single-edge state carries its
own sign. For the sign flipping loop `0` the two images are `-singleLoopClass` and
`singleLoopClass`, so the sum of the two classes is a nonzero class in the kernel
(`loopPairMap_flip_loopClass`).
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp

/-- One vertex with two parallel loops. -/
def loopPair : Multigraph (Fin 1) (Fin 2) where
  fst _ := 0
  snd _ := 0

/-- One vertex with one loop. -/
def singleLoop : Multigraph (Fin 1) (Fin 1) where
  fst _ := 0
  snd _ := 0

/-- The signed edge map sending both loops to the loop, without reversal, with edge sign `ε`. -/
def loopPairMap (ε : EdgeSign (Fin 2)) : SignedEdgeMap loopPair singleLoop where
  edge _ := 0
  reversed _ := false
  fst_edge _ := rfl
  snd_edge _ := rfl
  edgeSign := ε

/-- A loop has degree two at the vertex. -/
theorem loopPair_deg_singleton (e : Fin 2) (v : Fin 1) : loopPair.deg {e} v = 2 := by
  fin_cases v
  simp [deg, endCount, loopPair]

/-- The loop has degree two at the vertex. -/
theorem singleLoop_deg_singleton (v : Fin 1) : singleLoop.deg {0} v = 2 := by
  fin_cases v
  simp [deg, endCount, singleLoop]

/-- The unique state of the edge set of one loop of `loopPair`: twist `2` has one-dimensional
cohomology. -/
def loopState (e : Fin 2) : loopPair.IncResolutionBasis :=
  ⟨{e}, fun v => ⟨0, by rw [loopPair_deg_singleton]; decide⟩⟩

/-- The unique state of the edge set of the loop of `singleLoop`. -/
def singleLoopState : singleLoop.IncResolutionBasis :=
  ⟨{0}, fun v => ⟨0, by rw [singleLoop_deg_singleton]; decide⟩⟩

/-- The one-loop states have homological degree zero. -/
theorem incResolutionDegree_loopState (e : Fin 2) :
    loopPair.incResolutionDegree (loopState e) = 0 := by
  have hs : loopPair.support ({e} : Finset (Fin 2)) = Finset.univ := by
    ext v
    simp [support, loopPair_deg_singleton]
  simp [incResolutionDegree, loopState, hs]

/-- The one-loop state of `singleLoop` has homological degree zero. -/
theorem incResolutionDegree_singleLoopState :
    singleLoop.incResolutionDegree singleLoopState = 0 := by
  have hs : singleLoop.support ({0} : Finset (Fin 1)) = Finset.univ := by
    ext v
    simp [support, singleLoop_deg_singleton]
  simp [incResolutionDegree, singleLoopState, hs]

/-- The Tor class of a one-loop state of `loopPair`, in `Tor_0`. -/
noncomputable def loopClass (e : Fin 2) : loopPair.incidenceTor 0 :=
  loopPair.incFreeTermToTor 0
    ⟨single (loopState e) 1, single_mem_supported _ _ (incResolutionDegree_loopState e)⟩

/-- The Tor class of the one-loop state of `singleLoop`, in `Tor_0`. -/
noncomputable def singleLoopClass : singleLoop.incidenceTor 0 :=
  singleLoop.incFreeTermToTor 0
    ⟨single singleLoopState 1, single_mem_supported _ _ incResolutionDegree_singleLoopState⟩

/-- The full state vector of a loop class is the basis vector of its one-loop state. -/
theorem incidenceTorFullState_loopClass (e : Fin 2) :
    loopPair.incidenceTorFullState 0 (loopClass e) = single (loopState e) 1 := by
  rw [loopClass, incidenceTorFullState_class, mapRange_single, map_one]

/-- The full state vector of the class of `singleLoop` is the basis vector of its one-loop
state. -/
theorem incidenceTorFullState_singleLoopClass :
    singleLoop.incidenceTorFullState 0 singleLoopClass = single singleLoopState 1 := by
  rw [singleLoopClass, incidenceTorFullState_class, mapRange_single, map_one]

/-- The Tor class of a one-loop state is nonzero. -/
theorem loopClass_ne_zero (e : Fin 2) : loopClass e ≠ 0 := by
  intro h
  have h' := incidenceTorFullState_loopClass e
  rw [h, map_zero] at h'
  exact one_ne_zero (single_eq_zero.mp h'.symm)

/-- The Tor class of the one-loop state of `singleLoop` is nonzero. -/
theorem singleLoopClass_ne_zero : singleLoopClass ≠ 0 := by
  intro h
  have h' := incidenceTorFullState_singleLoopClass
  rw [h, map_zero] at h'
  exact one_ne_zero (single_eq_zero.mp h'.symm)

/-- The edge function is injective on each one-loop edge set. -/
theorem loopPairMap_injOn (ε : EdgeSign (Fin 2)) (e : Fin 2) :
    Set.InjOn (loopPairMap ε).edge ((loopState e).1 : Finset (Fin 2)) := by
  change Set.InjOn _ ((({e} : Finset (Fin 2)) : Set (Fin 2)))
  rw [Finset.coe_singleton]
  exact Set.injOn_singleton _ _

/-- Both one-loop states go to the one-loop state of `singleLoop`. -/
theorem loopPairMap_stateIndex (ε : EdgeSign (Fin 2)) (e : Fin 2)
    (h : Set.InjOn (loopPairMap ε).edge ((loopState e).1 : Finset (Fin 2))) :
    (loopPairMap ε).toEdgeMap.stateIndex (loopState e) h = singleLoopState := by
  have hS : (loopPairMap ε).toEdgeMap.edgeSet ({e} : Finset (Fin 2)) = {0} := by
    rw [EdgeMap.edgeSet_def, Finset.image_singleton]
    rfl
  apply Sigma.ext hS
  change HEq (cast (congrArg CechProduct.HBasis ((loopPairMap ε).toEdgeMap.deg_edgeSet h).symm)
    (loopState e).2) singleLoopState.2
  refine (cast_heq _ _).trans (Function.hfunext rfl fun v v' hv => ?_)
  cases hv
  rw [Fin.heq_ext_iff (by
    change phi (loopPair.deg {e} v) = phi (singleLoop.deg {0} v)
    rw [loopPair_deg_singleton, singleLoop_deg_singleton])]
  rfl

/-- The wedge sign of a one-loop edge set is one. -/
theorem loopPairMap_wedgeSign (ε : EdgeSign (Fin 2)) (e : Fin 2) :
    (loopPairMap ε).toEdgeMap.wedgeSign ({e} : Finset (Fin 2)) = 1 := by
  rw [EdgeMap.wedgeSign_of_injOn (S := {e}) _ (loopPairMap_injOn ε e)]
  simp [EdgeMap.inversions, Finset.filter_singleton]

/-- **Sanity check.** Under the signed edge map identifying the two parallel loops, the full state
of the image of the class of the one-loop state of loop `e` is `ε_e` times the one-loop state of
`singleLoop`. -/
theorem incidenceTorFullState_loopPairMap_loopClass (ε : EdgeSign (Fin 2)) (e : Fin 2) :
    singleLoop.incidenceTorFullState 0 ((loopPairMap ε).incidenceTorSignedEdgeMap 0 (loopClass e)) =
      single singleLoopState ((ε e : ℤ) : ℂ) := by
  rw [SignedEdgeMap.incidenceTorFullState_signedEdgeMap_of_single _ 0 _ (loopState e) 1
    (incidenceTorFullState_loopClass e) (loopPairMap_injOn ε e), loopPairMap_stateIndex]
  congr 1
  change ((loopPairMap ε).toEdgeMap.wedgeSign ({e} : Finset (Fin 2)) : ℂ) *
    (loopPairMap ε).edgeSign.setSign ℂ {e} * 1 = _
  rw [loopPairMap_wedgeSign, EdgeSign.setSign, Finset.prod_singleton, Int.cast_one, one_mul,
    mul_one]
  rfl

/-- **Sanity check.** The image of the class of the one-loop state of loop `e` is `ε_e` times the
class of the one-loop state of `singleLoop`: each single-edge state carries its own sign. -/
theorem loopPairMap_loopClass (ε : EdgeSign (Fin 2)) (e : Fin 2) :
    (loopPairMap ε).incidenceTorSignedEdgeMap 0 (loopClass e) =
      ((ε e : ℤ) : ℂ) • singleLoopClass := by
  apply singleLoop.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_loopPairMap_loopClass, map_smul, incidenceTorFullState_singleLoopClass,
    smul_single, smul_eq_mul, mul_one]

/-- The sign flipping loop `0` and fixing loop `1`. -/
def loopFlip : EdgeSign (Fin 2) := fun e => if e = 0 then -1 else 1

/-- **Sanity check.** For the sign flipping loop `0`, the two loop classes go to
`-singleLoopClass` and `singleLoopClass`; hence the nonzero class `loopClass 0 + loopClass 1` is
sent to zero. -/
theorem loopPairMap_flip_loopClass :
    (loopPairMap loopFlip).incidenceTorSignedEdgeMap 0 (loopClass 0) = -singleLoopClass ∧
      (loopPairMap loopFlip).incidenceTorSignedEdgeMap 0 (loopClass 1) = singleLoopClass ∧
      loopClass 0 + loopClass 1 ≠ 0 ∧
      (loopPairMap loopFlip).incidenceTorSignedEdgeMap 0 (loopClass 0 + loopClass 1) = 0 := by
  have h0 : (loopPairMap loopFlip).incidenceTorSignedEdgeMap 0 (loopClass 0) = -singleLoopClass := by
    rw [loopPairMap_loopClass]
    simp [loopFlip]
  have h1 : (loopPairMap loopFlip).incidenceTorSignedEdgeMap 0 (loopClass 1) = singleLoopClass := by
    rw [loopPairMap_loopClass]
    simp [loopFlip]
  refine ⟨h0, h1, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun y => loopPair.incidenceTorFullState 0 y (loopState 0)) h
    simp only [map_add, Finsupp.add_apply, incidenceTorFullState_loopClass, map_zero,
      Finsupp.zero_apply, single_eq_same] at h'
    have hne : loopState 1 ≠ loopState 0 := fun hs => by
      have := congrArg Sigma.fst hs
      simp [loopState] at this
    rw [single_eq_of_ne hne.symm] at h'
    norm_num at h'
  · rw [map_add, h0, h1, neg_add_cancel]

end BPFixedPoints.Multigraph
