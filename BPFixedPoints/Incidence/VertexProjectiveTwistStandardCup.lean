import BPFixedPoints.Incidence.BinaryCoverStandardCup
import BPFixedPoints.Incidence.VertexProjectiveTwistNativeClassCup

/-! # The standard product on actual vertex twist cohomology

Specialize the standard external product to the original multi-twists on
the product of projective lines over a Noetherian base. It is the Koszul
sign times the native roof product, it is bilinear for the original
geometric base actions, and with the original geometric Yoneda comparison
of inputs and output the original geometric quotient cup is exactly the
standard product, for all integral twists.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory TopologicalSpace
open SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance vertexStandardCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _
local instance vertexStandardCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _
variable [IsNoetherianRing R]

/-- The standard product on actual Ext-defined twist cohomology, through the original vertex cell resolution. -/
def vertexTwistStandardClassCup (a b : V → ℤ) (i j : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i →+
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j →+
        Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j) :=
  actualStandardClassCup (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
    (vertexTwistAbelianSectionPairing R V a b) (vertexTwistCellSheaf_terms_acyclic R V a)
      (vertexTwistCellSheaf_terms_acyclic R V b) i j

/-- The standard product is the Koszul sign times the native roof product. -/
theorem vertexTwistStandardClassCup_native (a b : V → ℤ) (i j : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    vertexTwistStandardClassCup R V a b i j x y =
      ((i : ℤ)*j).negOnePow • vertexTwistNativeClassCup R V a b i j x y :=
  actualStandardClassProduct_native _ _ _ _ _ i j x y

/-- With the original geometric Yoneda comparison of inputs and output, the original quotient cup is exactly the standard product. -/
theorem vertexTwistStandardClassCup_yoneda (a b : V → ℤ) (i j : ℕ)
    (x : vertexTwistCellCohomologyAt R V a i) (y : vertexTwistCellCohomologyAt R V b j) :
    vertexTwistCellActualAtLinearEquiv R V (a+b) (i+j) (vertexTwistCellCohomologyCupAt R V a b (i+j) i j x y) =
      vertexTwistStandardClassCup R V a b i j (vertexTwistCellActualAtLinearEquiv R V a i x)
        (vertexTwistCellActualAtLinearEquiv R V b j y) := by
  have hY : ∀ (c : V → ℤ) (n : ℕ) (z : vertexTwistCellCohomologyAt R V c n),
      vertexTwistCellActualAtLinearEquiv R V c n z = nativeYonedaSign n • vertexTwistNativeComparison R V c n z := by
    intro c n z
    rw [vertexTwistNativeComparison_yoneda,smul_smul,Int.units_mul_self,one_smul]
  rw [hY,hY,hY,vertexTwistStandardClassCup_native]
  simp only [Units.smul_def,map_zsmul,AddMonoidHom.zsmul_apply,vertexTwistNativeClassCup_quotient,smul_smul]
  congr 1
  rw [nativeYonedaSign_add]
  push_cast
  ring

/-- The standard product respects the original geometric action on its first input. -/
theorem vertexTwistStandardClassCup_smul_left (a b : V → ℤ) (i j : ℕ) (r : R)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
    vertexTwistStandardClassCup R V a b i j (r • x) y = r • vertexTwistStandardClassCup R V a b i j x y := by
  let _ : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
  let _ : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
  rw [vertexTwistStandardClassCup_native,vertexTwistStandardClassCup_native,
    vertexTwistNativeClassCup_smul_left,smul_comm]

/-- The standard product respects the original geometric action on its second input. -/
theorem vertexTwistStandardClassCup_smul_right (a b : V → ℤ) (i j : ℕ) (r : R)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
    vertexTwistStandardClassCup R V a b i j x (r • y) = r • vertexTwistStandardClassCup R V a b i j x y := by
  let _ : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
  let _ : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
  rw [vertexTwistStandardClassCup_native,vertexTwistStandardClassCup_native,
    vertexTwistNativeClassCup_smul_right,smul_comm]

/-- The standard product is bilinear for the original geometric base actions. -/
def vertexTwistStandardClassCupLinear (a b : V → ℤ) (i j : ℕ) :
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i →ₗ[R]
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j →ₗ[R]
        Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j) := by
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
  let p := vertexTwistStandardClassCup R V a b i j
  exact
    { toFun := fun x =>
        { toFun := p x
          map_add' := (p x).map_add
          map_smul' := fun r y => vertexTwistStandardClassCup_smul_right R V a b i j r x y }
      map_add' := fun x z => LinearMap.ext (fun y => congrArg (fun h : _ →+ _ => h y) (p.map_add x z))
      map_smul' := fun r x => LinearMap.ext (fun y => vertexTwistStandardClassCup_smul_left R V a b i j r x y) }

end
end BPFixedPoints.ProjectiveLine
