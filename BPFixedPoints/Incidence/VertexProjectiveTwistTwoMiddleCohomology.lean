import BPFixedPoints.Incidence.VertexProjectiveTwistTwoMiddleCocycles
import BPFixedPoints.Incidence.CechTwoMiddleCohomology

/-! # Original full degree-one cohomology computes actual H1 for negative second twist -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] [IsNoetherianRing R]

@[reducible] noncomputable local instance actualMiddleCyclesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (twoMiddleCycles R d) := (twoMiddleCycles R d).addCommGroup

@[reducible] noncomputable local instance actualZeroChainsAddCommGroup :
    AddCommGroup (twoZeroChains R) := (twoZeroChains R).addCommGroup

@[reducible] noncomputable local instance actualZeroChainsModule :
    Module R (twoZeroChains R) := (twoZeroChains R).module

@[reducible] noncomputable local instance actualMiddleCyclesModule (d : Fin 2 → ℕ) :
    Module R (twoMiddleCycles R d) := (twoMiddleCycles R d).module

/-- The native comparison kills exactly the original degree-zero boundaries. -/
theorem vertexTwistTwoMiddleCocyclesToH1_ker (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    LinearMap.range (twoMiddleBoundary R d) = LinearMap.ker (vertexTwistTwoMiddleCocyclesToH1 R d hd) := by
  rw [twoMiddleBoundary_range]
  ext c
  change twoMiddleStateProjection R d c = 0 ↔ vertexTwistTwoMiddleCocyclesToH1 R d hd c = 0
  rw [← (vertexTwistTwoH1StateEquiv R d).map_eq_zero_iff,
    vertexTwistTwoMiddleCocyclesToH1_projection]

/-- Every actual H1 class is the native comparison of an original full middle cocycle. -/
theorem vertexTwistTwoMiddleCocyclesToH1_surjective (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    Function.Surjective (vertexTwistTwoMiddleCocyclesToH1 R d hd) := by
  intro x
  obtain ⟨c,hc⟩ := twoMiddleStateProjection_surjective R d (vertexTwistTwoH1StateEquiv R d x)
  refine ⟨c,(vertexTwistTwoH1StateEquiv R d).injective ?_⟩
  rw [vertexTwistTwoMiddleCocyclesToH1_projection,hc]

/-- Cohomology of the original full coefficient complex equals actual H1, through the specified native row connecting classes. -/
noncomputable def vertexTwistTwoMiddleCohomologyEquiv (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    twoMiddleCohomology R d ≃ₗ[R] vertexTwistTwoH1Module R d :=
  quotientEquivOfExact R (A := twoZeroChains R) (B := twoMiddleCycles R d)
    (D := vertexTwistTwoH1Module R d) (twoMiddleBoundary R d) (vertexTwistTwoMiddleCocyclesToH1 R d hd)
    (vertexTwistTwoMiddleCocyclesToH1_ker R d hd) (vertexTwistTwoMiddleCocyclesToH1_surjective R d hd)

/-- Every original cocycle representative retains both original native row connecting classes. -/
theorem vertexTwistTwoMiddleCohomologyEquiv_mk (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (c : twoMiddleCycles R d) :
    vertexTwistTwoMiddleCohomologyEquiv R d hd (Submodule.Quotient.mk c) =
      vertexTwistTwoMiddleCocyclesToH1 R d hd c := rfl

/-- On every original cohomology class, the actual comparison agrees with the original full contraction. -/
theorem vertexTwistTwoMiddleCohomologyEquiv_projection (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (x : twoMiddleCohomology R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoMiddleCohomologyEquiv R d hd x) =
      twoMiddleCohomologyStateEquiv R d x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => exact vertexTwistTwoMiddleCocyclesToH1_projection R d hd c

/-- The original full inclusion maps to the specified actual inverse state, not an arbitrarily selected isomorphism. -/
theorem vertexTwistTwoMiddleCohomologyEquiv_inclusion (d : Fin 2 → ℕ) (hd : 0 < d 1)
    (s : twoMiddleStatePiece R d) :
    vertexTwistTwoMiddleCohomologyEquiv R d hd (Submodule.Quotient.mk (twoMiddleInclusion R d s)) =
      (vertexTwistTwoH1StateEquiv R d).symm s := by
  apply (vertexTwistTwoH1StateEquiv R d).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistTwoMiddleCohomologyEquiv_projection,
    twoMiddleCohomologyStateEquiv_mk,twoMiddleStateProjection_inclusion]

end BPFixedPoints.ProjectiveLine
