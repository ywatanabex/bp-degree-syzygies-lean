import BPFixedPoints.Incidence.BinaryCoverNativeClassProduct
import BPFixedPoints.Incidence.VertexProjectiveTwistNativeCohomology

/-! # The native roof product on actual vertex twist cohomology

The actual derived tensor roof defines the product before using state
coordinates. Its original geometric scalar actions are respected on both
inputs. The comparison is for the fixed original cubical resolution.
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
local instance vertexNativeClassCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _
local instance vertexNativeClassCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _
variable [IsNoetherianRing R]

/-- The unique original native tensor roofs define a biadditive product on actual Ext-defined twist cohomology. -/
def vertexTwistNativeClassCup (a b : V → ℤ) (i j : ℕ) :
    Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i →+
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j →+
        Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j) :=
  actualNativeClassCup (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b)
    (vertexCellChartOpen_cover R V) (vertexTwistCellSheaf_terms_acyclic R V a)
      (vertexTwistCellSheaf_terms_acyclic R V b) i j

/-- Every original quotient pair computes this actual product by the original geometric quotient cup. -/
theorem vertexTwistNativeClassCup_quotient (a b : V → ℤ) (i j : ℕ)
    (x : vertexTwistCellCohomologyAt R V a i) (y : vertexTwistCellCohomologyAt R V b j) :
    vertexTwistNativeClassCup R V a b i j
      (vertexTwistNativeComparison R V a i x) (vertexTwistNativeComparison R V b j y) =
        vertexTwistNativeComparison R V (a+b) (i+j)
          (vertexTwistCellCohomologyCupAt R V a b (i+j) i j x y) :=
  actualNativeClassCup_quotient _ _ _ _ _ i j x y

/-- The actual native product respects the independently specified geometric action on its first input. -/
theorem vertexTwistNativeClassCup_smul_left (a b : V → ℤ) (i j : ℕ) (r : R)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
    vertexTwistNativeClassCup R V a b i j (r • x) y = r • vertexTwistNativeClassCup R V a b i j x y := by
  letI := vertexTwistCellAtModule R V a i
  letI := vertexTwistCellAtModule R V b j
  letI := vertexTwistCellAtModule R V (a+b) (i+j)
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) i
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
  obtain ⟨x,rfl⟩ := (vertexTwistNativeLinearEquiv R V a i).surjective x
  obtain ⟨y,rfl⟩ := (vertexTwistNativeLinearEquiv R V b j).surjective y
  rw [← map_smul]
  change vertexTwistNativeClassCup R V a b i j (vertexTwistNativeComparison R V a i (r • x))
    (vertexTwistNativeComparison R V b j y) = _
  rw [vertexTwistNativeClassCup_quotient]
  change vertexTwistNativeLinearEquiv R V (a+b) (i+j)
    (vertexTwistCellCohomologyCupAt R V a b (i+j) i j (r • x) y) = _
  rw [vertexTwistCellCohomologyCupAt_smul_left,map_smul]
  congr 1
  exact (vertexTwistNativeClassCup_quotient R V a b i j x y).symm

/-- The actual native product respects the independently specified geometric action on its second input. -/
theorem vertexTwistNativeClassCup_smul_right (a b : V → ℤ) (i j : ℕ) (r : R)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) i)
    (y : Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
    vertexTwistNativeClassCup R V a b i j x (r • y) = r • vertexTwistNativeClassCup R V a b i j x y := by
  letI := vertexTwistCellAtModule R V a i
  letI := vertexTwistCellAtModule R V b j
  letI := vertexTwistCellAtModule R V (a+b) (i+j)
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V b) j) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V b) j
  letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V (a+b)) (i+j)) :=
    schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V (a+b)) (i+j)
  obtain ⟨x,rfl⟩ := (vertexTwistNativeLinearEquiv R V a i).surjective x
  obtain ⟨y,rfl⟩ := (vertexTwistNativeLinearEquiv R V b j).surjective y
  rw [← map_smul]
  change vertexTwistNativeClassCup R V a b i j (vertexTwistNativeComparison R V a i x)
    (vertexTwistNativeComparison R V b j (r • y)) = _
  rw [vertexTwistNativeClassCup_quotient]
  change vertexTwistNativeLinearEquiv R V (a+b) (i+j)
    (vertexTwistCellCohomologyCupAt R V a b (i+j) i j x (r • y)) = _
  rw [vertexTwistCellCohomologyCupAt_smul_right,map_smul]
  congr 1
  exact (vertexTwistNativeClassCup_quotient R V a b i j x y).symm

/-- The actual native roof product is bilinear for the original geometric base actions. -/
def vertexTwistNativeClassCupLinear (a b : V → ℤ) (i j : ℕ) :
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
  let p := vertexTwistNativeClassCup R V a b i j
  exact
    { toFun := fun x =>
        { toFun := p x
          map_add' := (p x).map_add
          map_smul' := fun r y => vertexTwistNativeClassCup_smul_right R V a b i j r x y }
      map_add' := fun x z => LinearMap.ext (fun y => congrArg (fun h : _ →+ _ => h y) (p.map_add x z))
      map_smul' := fun r x => LinearMap.ext (fun y => vertexTwistNativeClassCup_smul_left R V a b i j r x y) }

end
end BPFixedPoints.ProjectiveLine
