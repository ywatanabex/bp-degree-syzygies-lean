import BPFixedPoints.Incidence.VertexProjectiveTwistTwoMiddleZeroSecond
import BPFixedPoints.Incidence.VertexProjectiveTwistTwoMiddleCohomology

/-! # Original full degree-one cohomology and actual H1 for every nonpositive two-vertex twist -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] [IsNoetherianRing R]

@[reducible] noncomputable local instance allMiddleCyclesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (twoMiddleCycles R d) := (twoMiddleCycles R d).addCommGroup
@[reducible] noncomputable local instance allZeroChainsAddCommGroup :
    AddCommGroup (twoZeroChains R) := (twoZeroChains R).addCommGroup
@[reducible] noncomputable local instance allZeroChainsModule :
    Module R (twoZeroChains R) := (twoZeroChains R).module
@[reducible] noncomputable local instance allMiddleCyclesModule (d : Fin 2 → ℕ) :
    Module R (twoMiddleCycles R d) := (twoMiddleCycles R d).module

/-- The native comparison on all original full middle cocycles, with the specified row-kernel or glued connecting route. -/
noncomputable def vertexTwistTwoMiddleCocyclesToH1All (d : Fin 2 → ℕ) :
    twoMiddleCycles R d →ₗ[R] vertexTwistTwoH1Module R d :=
  if hd : d 1 = 0 then vertexTwistTwoMiddleZeroSecondToH1 R d hd
  else vertexTwistTwoMiddleCocyclesToH1 R d (by omega)

/-- Negative second twist retains the previously specified native row connecting classes and restriction kernel. -/
theorem vertexTwistTwoMiddleCocyclesToH1All_of_pos (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoMiddleCocyclesToH1All R d = vertexTwistTwoMiddleCocyclesToH1 R d hd := by
  simp only [vertexTwistTwoMiddleCocyclesToH1All,dite_eq_right (Nat.ne_of_gt hd)]

/-- Zero second twist retains precisely the original primitive correction, native gluing and outer connecting map. -/
theorem vertexTwistTwoMiddleCocyclesToH1All_of_zero (d : Fin 2 → ℕ) (hd : d 1 = 0) :
    vertexTwistTwoMiddleCocyclesToH1All R d = vertexTwistTwoMiddleZeroSecondToH1 R d hd := by
  simp only [vertexTwistTwoMiddleCocyclesToH1All,dite_eq_left hd]

/-- Every original full cocycle retains its original full contraction projection as actual state coordinate, including all zero twists. -/
theorem vertexTwistTwoMiddleCocyclesToH1All_projection (d : Fin 2 → ℕ) (c : twoMiddleCycles R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoMiddleCocyclesToH1All R d c) =
      twoMiddleStateProjection R d c := by
  by_cases hd : d 1 = 0
  · rw [vertexTwistTwoMiddleCocyclesToH1All_of_zero R d hd]
    exact vertexTwistTwoMiddleZeroSecondToH1_projection R d hd c
  · rw [vertexTwistTwoMiddleCocyclesToH1All_of_pos R d (by omega)]
    exact vertexTwistTwoMiddleCocyclesToH1_projection R d (by omega) c

/-- The specified native comparison kills exactly the original degree-zero boundaries for every nonpositive twist. -/
theorem vertexTwistTwoMiddleCocyclesToH1All_ker (d : Fin 2 → ℕ) :
    LinearMap.range (twoMiddleBoundary R d) = LinearMap.ker (vertexTwistTwoMiddleCocyclesToH1All R d) := by
  rw [twoMiddleBoundary_range]
  ext c
  change twoMiddleStateProjection R d c = 0 ↔ vertexTwistTwoMiddleCocyclesToH1All R d c = 0
  rw [← (vertexTwistTwoH1StateEquiv R d).map_eq_zero_iff,vertexTwistTwoMiddleCocyclesToH1All_projection]

/-- The original full inclusion supplies every actual H1 class under the specified native comparison. -/
theorem vertexTwistTwoMiddleCocyclesToH1All_surjective (d : Fin 2 → ℕ) :
    Function.Surjective (vertexTwistTwoMiddleCocyclesToH1All R d) := by
  intro x
  obtain ⟨c,hc⟩ := twoMiddleStateProjection_surjective R d (vertexTwistTwoH1StateEquiv R d x)
  refine ⟨c,(vertexTwistTwoH1StateEquiv R d).injective ?_⟩
  rw [vertexTwistTwoMiddleCocyclesToH1All_projection,hc]

/-- Original full degree-one cohomology equals actual H1 through the specified native comparison for every nonpositive two-vertex twist. -/
noncomputable def vertexTwistTwoMiddleCohomologyAllEquiv (d : Fin 2 → ℕ) :
    twoMiddleCohomology R d ≃ₗ[R] vertexTwistTwoH1Module R d :=
  quotientEquivOfExact R (A := twoZeroChains R) (B := twoMiddleCycles R d)
    (D := vertexTwistTwoH1Module R d) (twoMiddleBoundary R d) (vertexTwistTwoMiddleCocyclesToH1All R d)
    (vertexTwistTwoMiddleCocyclesToH1All_ker R d) (vertexTwistTwoMiddleCocyclesToH1All_surjective R d)

/-- Every original full cocycle class is sent by the specified native cocycle map. -/
theorem vertexTwistTwoMiddleCohomologyAllEquiv_mk (d : Fin 2 → ℕ) (c : twoMiddleCycles R d) :
    vertexTwistTwoMiddleCohomologyAllEquiv R d (Submodule.Quotient.mk c) =
      vertexTwistTwoMiddleCocyclesToH1All R d c := rfl

/-- The all-twist quotient comparison retains exactly the previous negative-second comparison. -/
theorem vertexTwistTwoMiddleCohomologyAllEquiv_of_pos (d : Fin 2 → ℕ) (hd : 0 < d 1) :
    vertexTwistTwoMiddleCohomologyAllEquiv R d = vertexTwistTwoMiddleCohomologyEquiv R d hd := by
  apply LinearEquiv.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [vertexTwistTwoMiddleCohomologyAllEquiv_mk,vertexTwistTwoMiddleCohomologyEquiv_mk,
      vertexTwistTwoMiddleCocyclesToH1All_of_pos R d hd]

/-- On every original cohomology class, the actual comparison agrees with the original full contraction. -/
theorem vertexTwistTwoMiddleCohomologyAllEquiv_projection (d : Fin 2 → ℕ) (x : twoMiddleCohomology R d) :
    vertexTwistTwoH1StateEquiv R d (vertexTwistTwoMiddleCohomologyAllEquiv R d x) =
      twoMiddleCohomologyStateEquiv R d x := by
  induction x using Submodule.Quotient.induction_on with
  | _ c => exact vertexTwistTwoMiddleCocyclesToH1All_projection R d c

/-- The original full inclusion keeps its specified actual inverse state for every nonpositive twist. -/
theorem vertexTwistTwoMiddleCohomologyAllEquiv_inclusion (d : Fin 2 → ℕ) (s : twoMiddleStatePiece R d) :
    vertexTwistTwoMiddleCohomologyAllEquiv R d (Submodule.Quotient.mk (twoMiddleInclusion R d s)) =
      (vertexTwistTwoH1StateEquiv R d).symm s := by
  apply (vertexTwistTwoH1StateEquiv R d).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistTwoMiddleCohomologyAllEquiv_projection,
    twoMiddleCohomologyStateEquiv_mk,twoMiddleStateProjection_inclusion]

end BPFixedPoints.ProjectiveLine
