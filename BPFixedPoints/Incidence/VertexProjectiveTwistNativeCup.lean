import BPFixedPoints.Incidence.BinaryCoverNativeCupRoofs
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistAbelianPairing

/-! # Original vertex twist cups retain their native tensor roofs

No Noetherian hypothesis or term Ext vanishing is needed for these native
chain and derived morphism identities. The original integral twists and
original geometric section pairing are unchanged.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace HomologicalComplex
open SheafTools.BinaryCells ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexNativeCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _

/-- The specified original vertex cell diagonal is a native quasi-isomorphism without any local vanishing hypothesis. -/
theorem vertexTensorDiagonal_quasiIso : QuasiIso (actualTensorDiagonalMap (vertexCoordinateOpen R V)) :=
  actualTensorDiagonal_quasiIso _ (vertexCellChartOpen_cover R V)

/-- The original geometric twist product on the native tensor of the two specified representative maps. -/
abbrev vertexTwistNativeTensorRoof (a b : V → ℤ) (i j : ℕ)
    (x : (sheafComplex (vertexCoordinateOpen R V)).X i ⟶ vertexTwistAbelianSheaf R V a)
    (hx : (sheafComplex (vertexCoordinateOpen R V)).d (i+1) i ≫ x=0)
    (y : (sheafComplex (vertexCoordinateOpen R V)).X j ⟶ vertexTwistAbelianSheaf R V b)
    (hy : (sheafComplex (vertexCoordinateOpen R V)).d (j+1) j ≫ y=0) :=
  actualNativeTensorProductRoof _ (vertexTwistAbelianSectionPairing R V a b)
    (vertexCellChartOpen_cover R V) i j x hx y hy

/-- The original geometric twist cup has exactly the native tensor-product roof through the original unit lift. -/
theorem vertexTwistNativeCup_roof (a b : V → ℤ) (i j : ℕ)
    (x : (sheafComplex (vertexCoordinateOpen R V)).X i ⟶ vertexTwistAbelianSheaf R V a)
    (hx : (sheafComplex (vertexCoordinateOpen R V)).d (i+1) i ≫ x=0)
    (y : (sheafComplex (vertexCoordinateOpen R V)).X j ⟶ vertexTwistAbelianSheaf R V b)
    (hy : (sheafComplex (vertexCoordinateOpen R V)).d (j+1) j ≫ y=0) :
    actualCellNativeRoof _ (vertexCellChartOpen_cover R V) (i+j)
      (actualCellCupAt _ (vertexTwistAbelianSectionPairing R V a b) (i+j) i j x y)
      (actualCellCupAt_closed _ _ (i+j) i j x y hx hy) =
      DerivedCategory.Q.map ((CochainComplex.singleFunctor _ 0).map
        (actualTensorTerminalIso (V := V) (T := vertexScheme R V)).hom) ≫
          vertexTwistNativeTensorRoof R V a b i j x hx y hy :=
  actualCellNativeRoof_cup _ (vertexTwistAbelianSectionPairing R V a b)
    (vertexCellChartOpen_cover R V) i j x hx y hy

end
end BPFixedPoints.ProjectiveLine
