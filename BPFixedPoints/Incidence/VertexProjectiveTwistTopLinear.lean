import BPFixedPoints.Incidence.VertexProjectiveTwistTopQuotient
import BPFixedPoints.Incidence.SchemeModuleMayerVietorisLinear

/-! # The original top-cohomology quotient over the geometric base ring -/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexTopLinearHasExt (n : ℕ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin (n+1)))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original top-cohomology quotient comparison is linear for the independent geometric base action. -/
noncomputable def vertexTwistSheafTopCokernelLinearEquiv (n : ℕ) (a : Fin (n+1) → ℤ) :
    letI : Module R (SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
      (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n) :=
        SchemeTools.schemeBaseMayerVietorisCokernelModule
          (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a)
          (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n
    letI : Module R ((vertexTwistAbelianSheaf R (Fin (n+1)) a).H (n+1)) :=
      SchemeTools.schemeBaseCohomologyModule
        (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a) (n+1)
    SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
      (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n ≃ₗ[R]
        (vertexTwistAbelianSheaf R (Fin (n+1)) a).H (n+1) := by
  letI : Module R (SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
    (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n) :=
      SchemeTools.schemeBaseMayerVietorisCokernelModule
        (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a)
        (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n
  letI : Module R ((vertexTwistAbelianSheaf R (Fin (n+1)) a).H (n+1)) :=
    SchemeTools.schemeBaseCohomologyModule
      (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a) (n+1)
  refine { vertexTwistSheafTopCokernelEquiv R n a with map_smul' := ?_ }
  intro r x
  refine Quotient.inductionOn' x (fun y => ?_)
  let A := vertexCoordinateOpen R (Fin (n+1)) 0 0
  let B := vertexCoordinateOpen R (Fin (n+1)) 0 1
  letI : Module R ((vertexTwistAbelianSheaf R (Fin (n+1)) a).H' n (A ⊓ B)) :=
    SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R (Fin (n+1)))
      (vertexTwistSheaf R (Fin (n+1)) a) (A ⊓ B) n
  let z : (vertexTwistAbelianSheaf R (Fin (n+1)) a).H' n (A ⊓ B) := y
  change vertexTwistSheafTopCokernelEquiv R n a (QuotientAddGroup.mk (r • z)) =
    r • vertexTwistSheafTopCokernelEquiv R n a (QuotientAddGroup.mk z)
  change SheafTools.mayerVietorisGlobalConnecting _ A B
    (vertexCoordinateOpen_cover R (Fin (n+1)) 0) n (r • z) =
      r • SheafTools.mayerVietorisGlobalConnecting _ A B
        (vertexCoordinateOpen_cover R (Fin (n+1)) 0) n z
  exact SchemeTools.schemeBaseGlobalConnecting_smul (vertexToBase R (Fin (n+1)))
    (vertexTwistSheaf R (Fin (n+1)) a) A B
      (vertexCoordinateOpen_cover R (Fin (n+1)) 0) n r z

/-- Forgetting scalars gives exactly the original specified additive top-cohomology comparison. -/
theorem vertexTwistSheafTopCokernelLinearEquiv_toAddEquiv (n : ℕ) (a : Fin (n+1) → ℤ) :
    letI : Module R (SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
      (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n) :=
        SchemeTools.schemeBaseMayerVietorisCokernelModule
          (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a)
          (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1) n
    letI : Module R ((vertexTwistAbelianSheaf R (Fin (n+1)) a).H (n+1)) :=
      SchemeTools.schemeBaseCohomologyModule
        (vertexToBase R (Fin (n+1))) (vertexTwistSheaf R (Fin (n+1)) a) (n+1)
    (vertexTwistSheafTopCokernelLinearEquiv R n a).toAddEquiv =
      vertexTwistSheafTopCokernelEquiv R n a := rfl

/-- Every original quotient representative maps to its native global connecting class. -/
theorem vertexTwistSheafTopCokernelLinearEquiv_mk (n : ℕ) (a : Fin (n+1) → ℤ)
    (x : (vertexTwistAbelianSheaf R (Fin (n+1)) a).H' n
      (vertexCoordinateOpen R (Fin (n+1)) 0 0 ⊓ vertexCoordinateOpen R (Fin (n+1)) 0 1)) :
    vertexTwistSheafTopCokernelLinearEquiv R n a (QuotientAddGroup.mk x) =
      SheafTools.mayerVietorisGlobalConnecting (vertexTwistAbelianSheaf R (Fin (n+1)) a)
        (vertexCoordinateOpen R (Fin (n+1)) 0 0) (vertexCoordinateOpen R (Fin (n+1)) 0 1)
          (vertexCoordinateOpen_cover R (Fin (n+1)) 0) n x := rfl

end BPFixedPoints.ProjectiveLine
