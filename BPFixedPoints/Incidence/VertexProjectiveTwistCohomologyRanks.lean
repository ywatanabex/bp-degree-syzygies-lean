import BPFixedPoints.Incidence.VertexProjectiveTwistStateCohomology

/-! # Actual finite free multi-twist cohomology and its original ranks

The actual Ext groups use their original geometric base action. The
specified original state comparison supplies finite free bases, concentration
in the original overlap degree, and all-degree vanishing for a minus-one factor.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
variable (V : Type) [Fintype V] [DecidableEq V]
noncomputable local instance vertexRanksHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- All actual groups of every nonpositive integral multi-twist are free over the original base ring. -/
theorem vertexTwistCohomology_free (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d j
    Module.Free R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) := by
  letI := vertexTwistStateCohomologyModule R V d j
  exact Module.Free.of_equiv ((vertexTwistStateLinearEquiv R V d j).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- All actual groups of every nonpositive integral multi-twist are finite over the original base ring. -/
theorem vertexTwistCohomology_finite (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d j
    Module.Finite R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) := by
  classical
  letI := vertexTwistStateCohomologyModule R V d j
  exact Module.Finite.equiv ((vertexTwistStateLinearEquiv R V d j).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- Actual cohomology is concentrated in the original number of nonzero twist factors. -/
theorem vertexTwistCohomology_eq_zero_off_degree (d : V → ℕ) (j : ℕ)
    (hj : cohomologyDegree d ≠ j)
    (x : (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) : x = 0 := by
  apply (vertexTwistStateLinearEquiv R V d j).injective
  rw [map_zero]
  apply Subtype.ext
  apply Finsupp.ext
  intro κ
  apply (mem_supported' R _).mp (vertexTwistStateLinearEquiv R V d j x).property
  change (cohomologyDegree d : ℤ) ≠ (j : ℤ)
  exact_mod_cast hj

/-- One minus-one factor annihilates every actual cohomology group, including degree zero and zero other factors. -/
theorem vertexTwistCohomology_eq_zero_of_one (d : V → ℕ) (v : V) (hv : d v = 1) (j : ℕ)
    (x : (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) : x = 0 := by
  apply (vertexTwistStateLinearEquiv R V d j).injective
  rw [map_zero]
  apply Subtype.ext
  apply Finsupp.ext
  intro κ
  have hκ := (κ v).isLt
  have hphi : phi (d v) = 0 := by rw [hv,phi_one]
  omega

/-- Over a nontrivial base, every actual rank is the original product of one-factor state ranks in exactly its original degree. -/
theorem vertexTwistCohomology_finrank [Nontrivial R] (d : V → ℕ) (j : ℕ) :
    letI := vertexTwistStateCohomologyModule R V d j
    Module.finrank R ((vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))).H j) =
      if cohomologyDegree d = j then ∏ v, phi (d v) else 0 := by
  classical
  letI := vertexTwistStateCohomologyModule R V d j
  rw [(vertexTwistStateLinearEquiv R V d j).finrank_eq,
    (supportedEquivFinsupp (R := R) (M := R)
      {_κ : HBasis d | (cohomologyDegree d : ℤ) = j}).finrank_eq]
  by_cases hj : cohomologyDegree d = j
  · have he : (cohomologyDegree d : ℤ) = (j : ℤ) := by exact_mod_cast hj
    simp [hj,he,HBasis,Fintype.card_pi]
  · have he : (cohomologyDegree d : ℤ) ≠ (j : ℤ) := by exact_mod_cast hj
    simp [hj,he]

end BPFixedPoints.ProjectiveLine
