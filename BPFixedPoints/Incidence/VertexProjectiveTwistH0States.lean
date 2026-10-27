import BPFixedPoints.Incidence.VertexProjectiveTwistZeroCycles
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity
import Mathlib.LinearAlgebra.Finsupp.Pi

/-! # Actual degree-zero cohomology and the original state grading

The original geometric base actions and the original chart restrictions are retained.
No Noetherian, field or nontriviality hypothesis is needed for the comparisons.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
noncomputable local instance vertexH0StateHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Actual global sections equal the original degree-zero state piece by original restriction and projection. -/
noncomputable def vertexTwistGlobalZeroStateEquiv (d : V → ℕ) :
    vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ)) ≃ₗ[R] zeroStatePiece R d :=
  (vertexTwistGlobalZeroCycleEquiv R V d).trans (zeroCycleStateEquiv R d)

/-- Every global section has exactly the original projection of its original chart restriction chain. -/
theorem vertexTwistGlobalZeroStateEquiv_val (d : V → ℕ)
    (s : vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ))) :
    (vertexTwistGlobalZeroStateEquiv R V d s).val =
      (contraction R d).p (vertexTwistGlobalZeroChain R V _ s) := rfl

/-- Every inverse state retains precisely its original contraction inclusion on all original chart coefficients. -/
theorem vertexTwistGlobalZeroStateEquiv_inverse_chain (d : V → ℕ) (s : zeroStatePiece R d) :
    vertexTwistGlobalZeroChain R V _ ((vertexTwistGlobalZeroStateEquiv R V d).symm s) =
      (contraction R d).i s :=
  congrArg Subtype.val ((vertexTwistGlobalZeroCycleEquiv R V d).apply_symm_apply
    ((zeroCycleStateEquiv R d).symm s))

/-- The actual Ext-defined H0 action is the independently defined original geometric action. -/
@[instance_reducible] noncomputable def vertexTwistH0BaseModule (d : V → ℕ) :
    Module R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) :=
  SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (fun v => -(d v : ℤ))) 0

/-- Native Ext H0 equals native global sections linearly for both original geometric actions. -/
noncomputable def vertexTwistH0SectionsLinearEquiv (d : V → ℕ) :
    letI := vertexTwistH0BaseModule R V d
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0 ≃ₗ[R]
      vertexTwistGlobalSectionModule R V (fun v => -(d v : ℤ)) := by
  letI := vertexTwistH0BaseModule R V d
  letI := SchemeTools.schemeBaseLocalCohomologyModule (vertexToBase R V)
    (vertexTwistSheaf R V (fun v => -(d v : ℤ))) ⊤ 0
  letI := SchemeTools.schemeBaseOpenModuleSections (vertexToBase R V)
    (vertexTwistSheaf R V (fun v => -(d v : ℤ))) ⊤
  exact (SchemeTools.schemeBaseLocalTopLinearEquiv (vertexToBase R V)
    (vertexTwistSheaf R V (fun v => -(d v : ℤ))) 0).symm.trans
      (SchemeTools.schemeBaseLocalH0LinearEquiv (vertexToBase R V)
        (vertexTwistSheaf R V (fun v => -(d v : ℤ))) ⊤)

/-- Actual H0 of every nonpositive multi-twist is its original degree-zero state piece. -/
noncomputable def vertexTwistH0StateLinearEquiv (d : V → ℕ) :
    letI := vertexTwistH0BaseModule R V d
    (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0 ≃ₗ[R] zeroStatePiece R d :=
  (vertexTwistH0SectionsLinearEquiv R V d).trans (vertexTwistGlobalZeroStateEquiv R V d)

/-- Every original actual H0 class keeps the original restriction-projection coordinates. -/
theorem vertexTwistH0StateLinearEquiv_val (d : V → ℕ)
    (s : (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) :
    (vertexTwistH0StateLinearEquiv R V d s).val =
      (contraction R d).p (vertexTwistGlobalZeroChain R V _ (vertexTwistH0SectionsLinearEquiv R V d s)) := rfl

/-- The actual H0 inverse class has its original inclusion on every chart coefficient. -/
theorem vertexTwistH0StateLinearEquiv_inverse_chain (d : V → ℕ) (s : zeroStatePiece R d) :
    vertexTwistGlobalZeroChain R V _
      (vertexTwistH0SectionsLinearEquiv R V d ((vertexTwistH0StateLinearEquiv R V d).symm s)) =
        (contraction R d).i s := by
  change vertexTwistGlobalZeroChain R V _
    (vertexTwistH0SectionsLinearEquiv R V d
      ((vertexTwistH0SectionsLinearEquiv R V d).symm
        ((vertexTwistGlobalZeroStateEquiv R V d).symm s))) = _
  rw [LinearEquiv.apply_symm_apply,vertexTwistGlobalZeroStateEquiv_inverse_chain]

/-- Actual H0 is free over every original commutative base ring. -/
theorem vertexTwistH0_free (d : V → ℕ) :
    letI := vertexTwistH0BaseModule R V d
    Module.Free R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) := by
  let := vertexTwistH0BaseModule R V d
  exact Module.Free.of_equiv ((vertexTwistH0StateLinearEquiv R V d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- Actual H0 is finite over every original commutative base ring. -/
theorem vertexTwistH0_finite (d : V → ℕ) :
    letI := vertexTwistH0BaseModule R V d
    Module.Finite R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) := by
  classical
  let := vertexTwistH0BaseModule R V d
  exact Module.Finite.equiv ((vertexTwistH0StateLinearEquiv R V d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- A single strictly negative factor makes actual degree-zero cohomology vanish. -/
theorem vertexTwistH0_eq_zero_of_pos (d : V → ℕ) (v : V) (hv : 0 < d v)
    (s : (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) : s = 0 := by
  apply (vertexTwistH0StateLinearEquiv R V d).injective
  rw [map_zero]
  exact zeroStatePiece_eq_zero_of_pos R d v hv _

/-- Over a nontrivial base, actual H0 has rank one exactly for the zero multi-twist. -/
theorem vertexTwistH0_finrank [Nontrivial R] (d : V → ℕ) :
    letI := vertexTwistH0BaseModule R V d
    Module.finrank R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H 0) =
      if ∀ v, d v = 0 then 1 else 0 := by
  classical
  let := vertexTwistH0BaseModule R V d
  rw [(vertexTwistH0StateLinearEquiv R V d).finrank_eq,
    (supportedEquivFinsupp (R := R) (M := R) {_κ : HBasis d | (cohomologyDegree d : ℤ) = 0}).finrank_eq]
  by_cases hd : ∀ v, d v = 0
  · have hc : cohomologyDegree d = 0 := (cohomologyDegree_zero_iff d).mpr hd
    simp [hd,hc,HBasis,Fintype.card_pi,phi_zero]
  · have hc : cohomologyDegree d ≠ 0 := (not_congr (cohomologyDegree_zero_iff d)).mpr hd
    simp [hd,hc]

/-- Actual H0 of the zero multi-twist is the original base module, including the empty product and zero ring. -/
noncomputable def vertexTwistH0_zero :
    letI : Module R ((vertexTwistAbelianSheaf R V (fun _ => 0)).H 0) :=
      SchemeTools.schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (fun _ => 0)) 0
    (vertexTwistAbelianSheaf R V (fun _ => 0)).H 0 ≃ₗ[R] R :=
  (vertexTwistH0StateLinearEquiv R V (fun _ => 0)).trans
    ((LinearEquiv.ofTop (zeroStatePiece R (fun _ : V => 0)) (by
      simp [zeroStatePiece,cohomologyDegree,lineCohomologyDegree])).trans
        ((Finsupp.mapDomain.linearEquiv R R
          (Equiv.piCongrRight fun _ : V => finCongr phi_zero)).trans
            (Finsupp.uniqueLinearEquiv R R (fun _ : V => (0 : Fin 1)))))

end BPFixedPoints.ProjectiveLine
