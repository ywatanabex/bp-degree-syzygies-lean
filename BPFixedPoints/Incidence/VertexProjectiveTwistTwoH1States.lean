import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH1Kernel
import BPFixedPoints.Incidence.CechTwoMiddleStatePiece

/-! # Actual two-vertex H1 states when the second twist is negative -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- Actual H1 equals the original degree-one state piece, including a zero first twist. -/
noncomputable def vertexTwistTwoH1PositiveSecondStateEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoH1Module R d ≃ₗ[R] twoMiddleStatePiece R d :=
  (vertexTwistTwoH1StateKernelEquiv R d hd).trans (twoRowKernelMiddleStateEquiv R d hd)

/-- Every actual H1 class retains the original first-factor projection at every original Laurent gap. -/
theorem vertexTwistTwoH1PositiveSecondStateEquiv_projection (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (x : vertexTwistTwoH1Module R d) (k : Fin (d 1-1)) :
    (twoRowH0MiddleStateEquiv R d hd).symm (vertexTwistTwoH1PositiveSecondStateEquiv R d hd x) k =
      CechLine.projectionZero R (d 0)
        (twoRowH1PairCoefficients R d (vertexTwistTwoH1StateKernelEquiv R d hd x).val k) := by
  change (twoRowH0MiddleStateEquiv R d hd).symm
    (twoRowH0MiddleStateEquiv R d hd (twoRowKernelH0Equiv R d
      (vertexTwistTwoH1StateKernelEquiv R d hd x))) k = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

/-- The inverse original degree-one state retains the original first-factor inclusion at every gap. -/
theorem vertexTwistTwoH1PositiveSecondStateEquiv_inverse (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (s : twoMiddleStatePiece R d) (k : Fin (d 1-1)) :
    twoRowH1PairCoefficients R d (vertexTwistTwoH1StateKernelEquiv R d hd
      ((vertexTwistTwoH1PositiveSecondStateEquiv R d hd).symm s)).val k =
        CechLine.inclusionZero R (d 0) ((twoRowH0MiddleStateEquiv R d hd).symm s k) := by
  change twoRowH1PairCoefficients R d ((vertexTwistTwoH1StateKernelEquiv R d hd)
    ((vertexTwistTwoH1StateKernelEquiv R d hd).symm ((twoRowKernelMiddleStateEquiv R d hd).symm s))).val k = _
  rw [LinearEquiv.apply_symm_apply]
  exact twoRowKernelH0Equiv_inverse R d ((twoRowH0MiddleStateEquiv R d hd).symm s) k

/-- Actual H1 is free over the original base for every negative second twist. -/
theorem vertexTwistTwoH1PositiveSecond_free (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Module.Free R (vertexTwistTwoH1Module R d) :=
  Module.Free.of_equiv ((vertexTwistTwoH1PositiveSecondStateEquiv R d hd).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- Actual H1 is finite over the original base, including zero first twists and zero rings. -/
theorem vertexTwistTwoH1PositiveSecond_finite (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Module.Finite R (vertexTwistTwoH1Module R d) := by
  classical
  exact Module.Finite.equiv ((vertexTwistTwoH1PositiveSecondStateEquiv R d hd).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- The original geometric rank is d(1)-1 for zero first twist and zero for negative first twist. -/
theorem vertexTwistTwoH1PositiveSecond_finrank [Nontrivial R] (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Module.finrank R (vertexTwistTwoH1Module R d) = if d 0 = 0 then d 1-1 else 0 := by
  classical
  rw [((vertexTwistTwoH1StateKernelEquiv R d hd).trans (twoRowKernelH0Equiv R d)).finrank_eq]
  by_cases h0 : d 0 = 0 <;> simp [CechLine.H0,CechLine.H0Index,h0]

/-- Actual H1 of the original twist (0,-2) is the original base module. -/
noncomputable def vertexTwistTwoH1_zero_minus_two :
    vertexTwistTwoH1Module R (![0,2] : Fin 2 → ℕ) ≃ₗ[R] R := by
  letI : Subsingleton (CechLine.H0Index 0) := by change Subsingleton (Fin 1); infer_instance
  exact (vertexTwistTwoH1StateKernelEquiv R (![0,2] : Fin 2 → ℕ) (by decide)).trans
    ((twoRowKernelH0Equiv R (![0,2] : Fin 2 → ℕ)).trans
      ((Finsupp.uniqueLinearEquiv R (CechLine.H0 R 0) (0 : Fin 1)).trans
        (Finsupp.uniqueLinearEquiv R R (⟨0,by decide⟩ : CechLine.H0Index 0))))

end BPFixedPoints.ProjectiveLine
