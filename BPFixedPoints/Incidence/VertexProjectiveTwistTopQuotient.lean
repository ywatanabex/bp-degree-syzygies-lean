import BPFixedPoints.Incidence.VertexProjectiveTwistHigherCohomology
import BPFixedPoints.Incidence.SheafGlobalCechComparison

/-! # The actual top cohomology as the original Mayer--Vietoris quotient

The first vertex direction is split off. Its two opens have one fewer binary
direction, so the required vanishing is proved from the original affine faces.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexTopQuotientHasExt (n : ℕ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin (n+1)))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Fixing the first original pivot leaves only the remaining binary directions in the degree bound. -/
theorem vertexTwistSheaf_firstOpen_higher_eq_zero (n : ℕ) (a : Fin (n+1) → ℤ)
    (b : Fin 2) (k : ℕ)
    (x : (vertexTwistAbelianSheaf R (Fin (n+1)) a).H' (n+k+1)
      (vertexCoordinateOpen R (Fin (n+1)) 0 b)) : x = 0 := by
  apply SheafTools.sheaf_cohomology_binaryCover_bound
    (vertexTwistAbelianSheaf R (Fin (n+1)) a) n
    (fun i => vertexCoordinateOpen R (Fin (n+1)) i.succ)
    (fun i => vertexCoordinateOpen_cover R (Fin (n+1)) i.succ)
    (vertexCoordinateOpen R (Fin (n+1)) 0 b) _ k x
  intro q j
  have hb : SheafTools.binaryCoverFaceFactor
      (vertexCoordinateOpen R (Fin (n+1)) 0) b.castSucc =
        vertexCoordinateOpen R (Fin (n+1)) 0 b := by
    fin_cases b <;> simp [SheafTools.binaryCoverFaceFactor]
  have he := SheafTools.binaryCoverFaceOpen_cons
    (vertexCoordinateOpen R (Fin (n+1))) b.castSucc q
  rw [hb] at he
  rw [← he]
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero _ _
    (vertexBinaryFaceOpen_isAffine R (Fin (n+1)) (Fin.cons b.castSucc q))
      (vertexTwistSheaf R (Fin (n+1)) a) j

/-- The actual top cohomology is the original restriction cokernel, with no input local vanishing assumptions. -/
noncomputable def vertexTwistSheafTopCokernelEquiv (n : ℕ) (a : Fin (n+1) → ℤ) :
    SheafTools.mayerVietorisCokernel (vertexTwistAbelianSheaf R (Fin (n+1)) a)
      (vertexCoordinateOpen R (Fin (n+1)) 0 0)
      (vertexCoordinateOpen R (Fin (n+1)) 0 1) n ≃+
        (vertexTwistAbelianSheaf R (Fin (n+1)) a).H (n+1) := by
  let F := vertexTwistAbelianSheaf R (Fin (n+1)) a
  let A := vertexCoordinateOpen R (Fin (n+1)) 0 0
  let B := vertexCoordinateOpen R (Fin (n+1)) 0 1
  let : Subsingleton (F.H' (n+1) A) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_firstOpen_higher_eq_zero R n a 0 0)
  let : Subsingleton (F.H' (n+1) B) := subsingleton_of_forall_eq 0
    (vertexTwistSheaf_firstOpen_higher_eq_zero R n a 1 0)
  exact (SheafTools.mayerVietorisCokernelEquiv F A B n).trans
    (SheafTools.localSheafCoverEquiv F (n+1) (A ⊔ B)
      (vertexCoordinateOpen_cover R (Fin (n+1)) 0))

end BPFixedPoints.ProjectiveLine
