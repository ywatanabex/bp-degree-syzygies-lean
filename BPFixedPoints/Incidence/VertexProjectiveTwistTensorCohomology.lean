import BPFixedPoints.Incidence.BinaryCoverActualTensorCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistAbelianPairing

/-! # Actual tensor-resolution cohomology for every original integral vertex twist

The original pair opens are intersections of original affine rectangular
faces. Existing quasicoherent vanishing proves actual term acyclicity,
rather than assuming it. The specified actual diagonal retains the
original cohomology comparison in every degree, including degree zero.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
noncomputable section
variable (R : Type) [CommRing R] [IsNoetherianRing R]
variable (V : Type) [Fintype V] [DecidableEq V]
local instance vertexTensorCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Every original tensor pair open is affine, including empty opens and the empty vertex product. -/
theorem vertexTensorPairFace_isAffine (q : (V → Fin 3) × (V → Fin 3)) :
    IsAffineOpen (pairedFaceOpen (vertexCoordinateOpen R V) q) :=
  (vertexBinaryFaceOpen_isAffine R V q.1).inf (vertexBinaryFaceOpen_isAffine R V q.2)

/-- Original actual tensor terms are acyclic against every original integer multi-twist. -/
theorem vertexTwistTensorSheaf_terms_acyclic (a : V → ℤ) :
    ComplexAcyclicAgainst (actualTensorSheafComplex (vertexCoordinateOpen R V))
      (vertexTwistAbelianSheaf R V a) := by
  apply actualTensorSheafComplex_acyclic
  intro n q k
  exact SheafTools.quasicoherent_affineOpen_local_cohomology_eq_zero (vertexScheme R V) _
    (vertexTensorPairFace_isAffine R V q.val) (vertexTwistSheaf R V a) k

/-- The original standard tensor Hom quotient computes actual Ext-defined cohomology in every degree. -/
def vertexTwistTensorActualAtEquiv (a : V → ℤ) (n : ℕ) :
    (actualTensorTower (vertexCoordinateOpen R V)).cohomologyAt (vertexTwistAbelianSheaf R V a) n ≃+
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n :=
  actualTensorActualAtEquiv _ _ (vertexCellChartOpen_cover R V)
    (vertexTwistTensorSheaf_terms_acyclic R V a) n

/-- The specified original actual tensor diagonal gives the same actual class, without supplied vanishing hypotheses. -/
theorem vertexTwistTensorDiagonal_actual (a : V → ℤ) (n : ℕ)
    (x : (actualTensorTower (vertexCoordinateOpen R V)).cohomologyAt (vertexTwistAbelianSheaf R V a) n) :
    finiteCubicalActualAtEquiv _ _ (vertexCellChartOpen_cover R V)
      (vertexTwistCellSheaf_terms_acyclic R V a) n
      ((actualTensorDiagonalSource (vertexCoordinateOpen R V)).cohomologyAt _ n x) =
        vertexTwistTensorActualAtEquiv R V a n x :=
  actualTensorDiagonal_actual _ _ (vertexCellChartOpen_cover R V)
    (vertexTwistTensorSheaf_terms_acyclic R V a) (vertexTwistCellSheaf_terms_acyclic R V a) n x

/-- The original diagonal gives a bijection of the original actual tensor and cell Hom quotients in every degree. -/
theorem vertexTwistTensorDiagonal_bijective (a : V → ℤ) (n : ℕ) :
    Function.Bijective ((actualTensorDiagonalSource (vertexCoordinateOpen R V)).cohomologyAt
      (vertexTwistAbelianSheaf R V a) n) :=
  actualTensorDiagonal_cohomology_bijective _ _ (vertexCellChartOpen_cover R V)
    (vertexTwistTensorSheaf_terms_acyclic R V a) (vertexTwistCellSheaf_terms_acyclic R V a) n

/-- The original geometric cup and original tensor cocycle determine the same actual class in every degree. -/
theorem vertexTwistTensorCup_actual (a b : V → ℤ) (n i j : ℕ)
    (x : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V a) i)
    (y : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V b) j) :
    finiteCubicalActualAtEquiv _ _ (vertexCellChartOpen_cover R V)
      (vertexTwistCellSheaf_terms_acyclic R V (a+b)) n
      ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n
        (cubicalCyclesCupAt _ (vertexTwistAbelianSectionPairing R V a b) n i j x y)) =
      vertexTwistTensorActualAtEquiv R V (a+b) n
        ((actualTensorTower (vertexCoordinateOpen R V)).classAt _ n
          (actualTensorCyclesCupAt _ (vertexTwistAbelianSectionPairing R V a b) n i j x y)) :=
  actualTensorCup_actual _ _ (vertexCellChartOpen_cover R V)
    (vertexTwistTensorSheaf_terms_acyclic R V (a+b)) (vertexTwistCellSheaf_terms_acyclic R V (a+b))
    (vertexTwistAbelianSectionPairing R V a b) n i j x y

end
end BPFixedPoints.ProjectiveLine
