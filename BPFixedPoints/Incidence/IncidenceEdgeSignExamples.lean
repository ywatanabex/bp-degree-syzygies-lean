import BPFixedPoints.Incidence.IncidenceEdgeSignRelabel

/-!
# Sanity checks for edge signs and signed relabelings

* The graph `twoCycle` has two parallel edges `0, 1` between the vertices `0` and `1` of `Fin 2`,
  a cycle of length two. Its cycle state is the full edge set with the unique state of the twist
  `(2,2)`; it has homological degree zero, and its Tor class `twoCycleClass ∈ Tor_0` is nonzero.
  Flipping the sign of edge `0` multiplies this Tor class by `-1`
  (`incidenceTorSign_twoCycleClass`). By contrast, the relabeling of the two-cycle onto the
  opposite two-cycle that reverses both edges introduces no sign on the cycle state
  (`incidenceTorFullState_twoCycleReverse`), and the same reversal with the sign of edge `0`
  flipped introduces the sign `-1` (`incidenceTorFullState_twoCycleSignedReverse`).
* Under an unsigned relabeling reversing an edge `e`, the coefficient `c_{e,(0,0)}` goes to
  `c_{φ e,(0,0)}` and `c_{e,(0,1)}` to `c_{φ e,(1,0)}`; under a signed relabeling `c_{e,(0,0)}`
  goes to `ε_e c_{φ e,(0,0)}`. A concrete reversing relabeling of the two-cycle onto the opposite
  two-cycle, with the sign of edge `0` flipped, sends `c_{0,(0,0)}` to `-c_{0,(0,0)}`.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp MvPolynomial

/-! ## Coefficients under reversing relabelings -/

namespace EdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}

/-- Under a relabeling reversing `e`, the coefficient `c_{e,(0,0)}` goes to `c_{φ e,(0,0)}`, with no
sign. -/
theorem coeffEquiv_X_zero_zero_of_reversed (φ : EdgeRelabel G H) {e : E} (he : φ.reversed e = true) :
    φ.coeffEquiv (X (e, 0, 0)) = X (φ.edge e, 0, 0) := by
  rw [coeffEquiv_X, coeffIdxEquiv_apply, endpointIndex, he]
  rfl

/-- Under a relabeling reversing `e`, the endpoint indices of a coefficient are exchanged:
`c_{e,(0,1)} ↦ c_{φ e,(1,0)}`. -/
theorem coeffEquiv_X_zero_one_of_reversed (φ : EdgeRelabel G H) {e : E} (he : φ.reversed e = true) :
    φ.coeffEquiv (X (e, 0, 1)) = X (φ.edge e, 1, 0) := by
  rw [coeffEquiv_X, coeffIdxEquiv_apply, endpointIndex, he]
  rfl

end EdgeRelabel

namespace SignedEdgeRelabel

variable {V E E' : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] {G : Multigraph V E} {H : Multigraph V E'}

/-- Under a signed relabeling reversing `e`, the coefficient `c_{e,(0,0)}` goes to
`ε_e c_{φ e,(0,0)}`. -/
theorem signedCoeffEquiv_X_zero_zero_of_reversed (φ : SignedEdgeRelabel G H) {e : E}
    (he : φ.reversed e = true) :
    φ.signedCoeffEquiv (X (e, 0, 0)) =
      ((φ.edgeSign e : ℤ) : IncCoeffRing E') * X (φ.edge e, 0, 0) := by
  rw [signedCoeffEquiv_apply, edgeSignCoeff_X, map_mul, map_intCast,
    EdgeRelabel.coeffEquiv_X_zero_zero_of_reversed _ he]

end SignedEdgeRelabel

/-! ## The two-cycle -/

/-- Two parallel edges `0, 1` between the vertices `0` and `1`: a cycle of length two. -/
def twoCycle : Multigraph (Fin 2) (Fin 2) where
  fst _ := 0
  snd _ := 1

/-- The same two parallel edges with the opposite endpoint order. -/
def twoCycleOpp : Multigraph (Fin 2) (Fin 2) where
  fst _ := 1
  snd _ := 0

/-- The sign flipping edge `0` and fixing edge `1`. -/
def twoCycleFlip : EdgeSign (Fin 2) := fun e => if e = 0 then -1 else 1

/-- Both vertices have degree two in the full edge set of the two-cycle. -/
theorem twoCycle_deg_univ (v : Fin 2) : twoCycle.deg Finset.univ v = 2 := by
  fin_cases v <;> simp [deg, endCount, twoCycle]

/-- The sign of the full edge set under the flip of edge `0` is `-1`. -/
theorem twoCycleFlip_setSign_univ : twoCycleFlip.setSign ℂ (Finset.univ : Finset (Fin 2)) = -1 := by
  simp [EdgeSign.setSign, twoCycleFlip, Fin.prod_univ_two]

/-- The cycle state of the two-cycle: the full edge set with the unique state of its twist. -/
def twoCycleState : twoCycle.IncResolutionBasis :=
  ⟨Finset.univ, fun v => ⟨0, by rw [twoCycle_deg_univ]; decide⟩⟩

/-- The cycle state has homological degree zero. -/
theorem incResolutionDegree_twoCycleState : twoCycle.incResolutionDegree twoCycleState = 0 := by
  have hs : twoCycle.support (Finset.univ : Finset (Fin 2)) = Finset.univ := by
    ext v
    simp [support, twoCycle_deg_univ]
  simp [incResolutionDegree, twoCycleState, hs]

/-- The cycle state has internal degree two. -/
theorem incResolutionInternalDegree_twoCycleState :
    twoCycle.incResolutionInternalDegree twoCycleState = 2 := by
  simp [incResolutionInternalDegree, twoCycleState]

/-- The Tor class of the cycle state, in `Tor_0`: the specialization of the corresponding free
basis element of the actual free resolution. -/
noncomputable def twoCycleClass : twoCycle.incidenceTor 0 :=
  twoCycle.incFreeTermToTor 0
    ⟨single twoCycleState 1, single_mem_supported _ _ incResolutionDegree_twoCycleState⟩

/-- The full state vector of the cycle class is the basis vector of the cycle state. -/
theorem incidenceTorFullState_twoCycleClass :
    twoCycle.incidenceTorFullState 0 twoCycleClass = single twoCycleState 1 := by
  rw [twoCycleClass, incidenceTorFullState_class, mapRange_single, map_one]

/-- The Tor class of the cycle state is nonzero. -/
theorem twoCycleClass_ne_zero : twoCycleClass ≠ 0 := by
  intro h
  have h' := incidenceTorFullState_twoCycleClass
  rw [h, map_zero] at h'
  exact one_ne_zero (single_eq_zero.mp h'.symm)

/-- **Sanity check.** Flipping the sign of one edge of the two-cycle multiplies the Tor class of
the cycle state by `-1`. -/
theorem incidenceTorSign_twoCycleClass :
    twoCycle.incidenceTorSign twoCycleFlip 0 twoCycleClass = -twoCycleClass := by
  apply twoCycle.incidenceTorFullState_injective 0
  rw [incidenceTorFullState_sign, map_neg, incidenceTorFullState_twoCycleClass,
    edgeSignState_single, show twoCycleState.1 = Finset.univ from rfl, twoCycleFlip_setSign_univ,
    mul_one, single_neg]

/-- The relabeling of the two-cycle onto the opposite two-cycle that fixes both edges and reverses
both. -/
def twoCycleReverse : EdgeRelabel twoCycle twoCycleOpp where
  edge := Equiv.refl _
  reversed _ := true
  fst_edge _ := rfl
  snd_edge _ := rfl

/-- The reversing relabeling with the sign of edge `0` flipped. -/
def twoCycleSignedReverse : SignedEdgeRelabel twoCycle twoCycleOpp where
  toEdgeRelabel := twoCycleReverse
  edgeSign := twoCycleFlip

/-- The reversing relabeling alone sends `c_{0,(0,0)}` to `c_{0,(0,0)}`. -/
theorem twoCycleReverse_coeff :
    twoCycleReverse.coeffEquiv (X (0, 0, 0)) = X (0, 0, 0) :=
  EdgeRelabel.coeffEquiv_X_zero_zero_of_reversed twoCycleReverse rfl

/-- The reversing relabeling of the two-cycle has no inversions, hence relabeling sign one. -/
theorem twoCycleReverse_sign (S : Finset (Fin 2)) : twoCycleReverse.sign ℂ S = 1 := by
  have h : twoCycleReverse.inversions S = 0 := EdgeRelabel.inversions_refl twoCycle S
  rw [EdgeRelabel.sign, h, pow_zero]

/-- The reversing relabeling carries the Tor class of the cycle state to the class of the
relabeled cycle state, with no sign. -/
theorem incidenceTorFullState_twoCycleReverse :
    twoCycleOpp.incidenceTorFullState 0 (twoCycleReverse.incidenceTorRelabel 0 twoCycleClass) =
      single (twoCycleReverse.stateIndex twoCycleState) 1 := by
  rw [EdgeRelabel.incidenceTorFullState_relabel, incidenceTorFullState_twoCycleClass,
    EdgeRelabel.stateRelabel_single, twoCycleReverse_sign, one_mul]

/-- The signed reversing relabeling carries the Tor class of the cycle state to `-1` times the
class of the relabeled cycle state. -/
theorem incidenceTorFullState_twoCycleSignedReverse :
    twoCycleOpp.incidenceTorFullState 0
        (twoCycleSignedReverse.incidenceTorSignedRelabel 0 twoCycleClass) =
      -single (twoCycleReverse.stateIndex twoCycleState) 1 := by
  rw [SignedEdgeRelabel.incidenceTorSignedRelabel_apply]
  change twoCycleOpp.incidenceTorFullState 0
      (twoCycleReverse.incidenceTorRelabel 0 (twoCycle.incidenceTorSign twoCycleFlip 0 twoCycleClass)) = _
  rw [incidenceTorSign_twoCycleClass, map_neg, map_neg, incidenceTorFullState_twoCycleReverse]

/-- The signed reversing relabeling sends `c_{0,(0,0)}` to `-c_{0,(0,0)}`. -/
theorem twoCycleSignedReverse_coeff :
    twoCycleSignedReverse.signedCoeffEquiv (X (0, 0, 0)) = -X (0, 0, 0) := by
  rw [SignedEdgeRelabel.signedCoeffEquiv_X_zero_zero_of_reversed twoCycleSignedReverse rfl]
  simp [twoCycleSignedReverse, twoCycleFlip, twoCycleReverse]

end BPFixedPoints.Multigraph
