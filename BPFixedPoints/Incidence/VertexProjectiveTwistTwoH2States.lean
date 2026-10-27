import BPFixedPoints.Incidence.VertexProjectiveTwistTwoRectangleCoordinates
import BPFixedPoints.Incidence.CechTwoTopState
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Actual negative two-vertex twist H2 and the original state basis

All comparisons use the original geometric base action, original face frames,
original fixed-enumeration contraction and original iterated connecting classes.
The stated positivity includes degree-one factors, whose original state type is empty.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexTwoH2StatesHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The actual global H2 action remains the independently defined original geometric base action. -/
@[instance_reducible] noncomputable def vertexTwistTwoH2BaseModule (d : Fin 2 → ℕ) :
    Module R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) :=
  SchemeTools.schemeBaseCohomologyModule (vertexToBase R (Fin 2))
    (vertexTwistSheaf R (Fin 2) (fun v => -(d v : ℤ))) 2

/-- Actual global H2 equals the original state module for strictly negative two-vertex twists. -/
noncomputable def vertexTwistTwoH2StateLinearEquiv (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    letI := vertexTwistTwoH2BaseModule R d
    (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2 ≃ₗ[R] H R d :=
  (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))).symm.trans
    (twoRectangleStateEquiv R d hd)

/-- Every original coefficient connecting representative has precisely its original state projection. -/
theorem vertexTwistTwoH2StateLinearEquiv_representative (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (x : FaceRing R twoTopFace) :
    vertexTwistTwoH2StateLinearEquiv R d hd
      (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ)) (Submodule.Quotient.mk x)) =
      twoTopStateProjection R d x := by
  change twoRectangleStateEquiv R d hd
    ((vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))).symm
      (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ)) (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.symm_apply_apply,twoRectangleStateEquiv_mk]

/-- Every original state retains the original contraction representative and both original connecting maps. -/
theorem vertexTwistTwoH2StateLinearEquiv_symm (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) (s : H R d) :
    (vertexTwistTwoH2StateLinearEquiv R d hd).symm s =
      vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))
        (Submodule.Quotient.mk (faceEquiv R ((contraction R d).i s) twoTopFace)) := by
  apply (vertexTwistTwoH2StateLinearEquiv R d hd).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistTwoH2StateLinearEquiv_representative,
    twoTopStateProjection_top R d hd]
  exact (LinearMap.congr_fun (contraction R d).p_i s).symm

/-- Actual negative two-vertex H2 is free over the original base, including zero state modules. -/
theorem vertexTwistTwoH2_free (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.Free R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) := by
  let := vertexTwistTwoH2BaseModule R d
  exact Module.Free.of_equiv (vertexTwistTwoH2StateLinearEquiv R d hd).symm

/-- Actual negative two-vertex H2 is finite over the original base. -/
theorem vertexTwistTwoH2_finite (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.Finite R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) := by
  let := vertexTwistTwoH2BaseModule R d
  exact Module.Finite.equiv (vertexTwistTwoH2StateLinearEquiv R d hd).symm

/-- The original state count computes actual H2 rank over a nontrivial Noetherian base. -/
theorem vertexTwistTwoH2_finrank [Nontrivial R] (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.finrank R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) =
      (d 0-1)*(d 1-1) := by
  let := vertexTwistTwoH2BaseModule R d
  rw [(vertexTwistTwoH2StateLinearEquiv R d hd).finrank_eq]
  simp [H,HBasis,Fintype.card_pi,Fin.prod_univ_succ,phi_of_pos (hd 0),phi_of_pos (hd 1)]

/-- Actual H2 of the original twist (-2,-2) is the original base ring as a module. -/
noncomputable def vertexTwistTwoH2_minus_two :
    letI := vertexTwistTwoH2BaseModule R (fun _ => 2)
    (vertexTwistAbelianSheaf R (Fin 2) (fun _ => -2)).H 2 ≃ₗ[R] R :=
  (vertexTwistTwoH2StateLinearEquiv R (fun _ => 2) (by intro v; decide)).trans
    ((Finsupp.mapDomain.linearEquiv R R
      (Equiv.piCongrRight fun _ : Fin 2 => finCongr (show phi 2 = 1 by rfl))).trans
        (Finsupp.uniqueLinearEquiv R R (fun _ : Fin 2 => (0 : Fin 1))))

/-- A degree-one factor has no original states, hence actual H2 vanishes. -/
theorem vertexTwistTwoH2_eq_zero_of_one (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (v : Fin 2) (hv : d v = 1)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) : x = 0 := by
  apply (vertexTwistTwoH2StateLinearEquiv R d hd).injective
  rw [map_zero]
  apply Finsupp.ext
  intro k
  have hk := (k v).isLt
  simp [hv,phi] at hk

end BPFixedPoints.ProjectiveLine
