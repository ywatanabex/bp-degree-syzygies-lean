import BPFixedPoints.Incidence.FiniteCubicalCohomologyDegree
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCup

/-! # The geometric twist cup on the original cohomology quotients in all degrees

The original actual cochain cup descends through the original boundary
quotients, including degree zero. Its bilinearity uses the independently
specified geometric scalar endomorphisms. The existing Yoneda comparison
retains the cup representatives in actual sheaf cohomology; equality with
the canonical derived cup is a separate comparison.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open SheafTools SheafTools.BinaryCells SchemeTools ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]
local instance twistCohomologyCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) := HasExt.standard _

/-- Original vertex cell cohomology in its actual degree, with original cycles in degree zero. -/
abbrev vertexTwistCellCohomologyAt (a : V → ℤ) (n : ℕ) :=
  cubicalCohomologyAt (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V a) n

/-- The original geometric coefficient action on original classes, including zero degree. -/
@[instance_reducible] def vertexTwistCellAtModule (a : V → ℤ) (n : ℕ) :
    Module R (vertexTwistCellCohomologyAt R V a n) :=
  schemeBaseCubicalAtModule (vertexToBase R V) (vertexTwistSheaf R V a) (vertexCoordinateOpen R V) n

/-- Every positive-degree action is the existing original geometric action itself. -/
theorem vertexTwistCellAtModule_succ (a : V → ℤ) (n : ℕ) :
    vertexTwistCellAtModule R V a (n+1) = vertexTwistCellModule R V a n := rfl

/-- The original geometric cell cup descends to the original cohomology classes in every degree. -/
def vertexTwistCellCohomologyCupAt (a b : V → ℤ) (n i j : ℕ) :
    vertexTwistCellCohomologyAt R V a i →+ vertexTwistCellCohomologyAt R V b j →+
      vertexTwistCellCohomologyAt R V (a+b) n :=
  cubicalCohomologyCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j

/-- The descended geometric cup retains every original actual cell cup representative. -/
theorem vertexTwistCellCohomologyCupAt_class (a b : V → ℤ) (n i j : ℕ)
    (x : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V a) i)
    (y : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V b) j) :
    vertexTwistCellCohomologyCupAt R V a b n i j
      ((cubicalTower (vertexCoordinateOpen R V)).classAt (vertexTwistAbelianSheaf R V a) i x)
      ((cubicalTower (vertexCoordinateOpen R V)).classAt (vertexTwistAbelianSheaf R V b) j y) =
        (cubicalTower (vertexCoordinateOpen R V)).classAt (vertexTwistAbelianSheaf R V (a+b)) n
          (cubicalCyclesCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j x y) :=
  cubicalCohomologyCupAt_class _ _ n i j x y

/-- The original left geometric action descends unchanged through both original boundary quotients. -/
theorem vertexTwistCellCohomologyCupAt_smul_left (a b : V → ℤ) (n i j : ℕ) (r : R)
    (x : vertexTwistCellCohomologyAt R V a i) (y : vertexTwistCellCohomologyAt R V b j) :
    letI := vertexTwistCellAtModule R V a i
    letI := vertexTwistCellAtModule R V b j
    letI := vertexTwistCellAtModule R V (a+b) n
    vertexTwistCellCohomologyCupAt R V a b n i j (r • x) y =
      r • vertexTwistCellCohomologyCupAt R V a b n i j x y := by
  letI := vertexTwistCellAtModule R V a i
  letI := vertexTwistCellAtModule R V b j
  letI := vertexTwistCellAtModule R V (a+b) n
  change cubicalCohomologyCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j
    ((cubicalTower (vertexCoordinateOpen R V)).mapAt
      (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r) i x) y =
        (cubicalTower (vertexCoordinateOpen R V)).mapAt
          (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r) n
            (cubicalCohomologyCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j x y)
  obtain ⟨x,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ i x
  obtain ⟨y,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ j y
  dsimp only [vertexTwistAbelianSheaf] at x y ⊢
  rw [ExactTower.mapAt_class,cubicalCohomologyCupAt_class,cubicalCohomologyCupAt_class,ExactTower.mapAt_class]
  apply congrArg ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n)
  apply Subtype.ext
  exact vertexTwistCellCupAt_left_scalar R V a b n i j r x.val y.val

/-- The original right geometric action descends unchanged through both original boundary quotients. -/
theorem vertexTwistCellCohomologyCupAt_smul_right (a b : V → ℤ) (n i j : ℕ) (r : R)
    (x : vertexTwistCellCohomologyAt R V a i) (y : vertexTwistCellCohomologyAt R V b j) :
    letI := vertexTwistCellAtModule R V a i
    letI := vertexTwistCellAtModule R V b j
    letI := vertexTwistCellAtModule R V (a+b) n
    vertexTwistCellCohomologyCupAt R V a b n i j x (r • y) =
      r • vertexTwistCellCohomologyCupAt R V a b n i j x y := by
  letI := vertexTwistCellAtModule R V a i
  letI := vertexTwistCellAtModule R V b j
  letI := vertexTwistCellAtModule R V (a+b) n
  change cubicalCohomologyCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j x
    ((cubicalTower (vertexCoordinateOpen R V)).mapAt
      (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) j y) =
        (cubicalTower (vertexCoordinateOpen R V)).mapAt
          (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r) n
            (cubicalCohomologyCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j x y)
  obtain ⟨x,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ i x
  obtain ⟨y,rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ j y
  dsimp only [vertexTwistAbelianSheaf] at x y ⊢
  rw [ExactTower.mapAt_class,cubicalCohomologyCupAt_class,cubicalCohomologyCupAt_class,ExactTower.mapAt_class]
  apply congrArg ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n)
  apply Subtype.ext
  exact vertexTwistCellCupAt_right_scalar R V a b n i j r x.val y.val

/-- The same original geometric quotient cup is bilinear for the original coefficient action. -/
def vertexTwistCellCohomologyCupLinearAt (a b : V → ℤ) (n i j : ℕ) :
    letI := vertexTwistCellAtModule R V a i
    letI := vertexTwistCellAtModule R V b j
    letI := vertexTwistCellAtModule R V (a+b) n
    vertexTwistCellCohomologyAt R V a i →ₗ[R] vertexTwistCellCohomologyAt R V b j →ₗ[R]
      vertexTwistCellCohomologyAt R V (a+b) n := by
  letI := vertexTwistCellAtModule R V a i
  letI := vertexTwistCellAtModule R V b j
  letI := vertexTwistCellAtModule R V (a+b) n
  let p := vertexTwistCellCohomologyCupAt R V a b n i j
  exact
    { toFun := fun x =>
        { toFun := p x
          map_add' := (p x).map_add
          map_smul' := fun r y => vertexTwistCellCohomologyCupAt_smul_right R V a b n i j r x y }
      map_add' := fun x z => LinearMap.ext (fun y => congrArg (fun h : _ →+ _ => h y) (p.map_add x z))
      map_smul' := fun r x => LinearMap.ext (fun y => vertexTwistCellCohomologyCupAt_smul_left R V a b n i j r x y) }

/-- Linearization retains the original descended additive cup on every original class. -/
theorem vertexTwistCellCohomologyCupLinearAt_apply (a b : V → ℤ) (n i j : ℕ)
    (x : vertexTwistCellCohomologyAt R V a i) (y : vertexTwistCellCohomologyAt R V b j) :
    letI := vertexTwistCellAtModule R V a i
    letI := vertexTwistCellAtModule R V b j
    letI := vertexTwistCellAtModule R V (a+b) n
    vertexTwistCellCohomologyCupLinearAt R V a b n i j x y =
      vertexTwistCellCohomologyCupAt R V a b n i j x y := rfl

/-- The homogeneous original geometric quotient cup lands in the original sum degree. -/
def vertexTwistCellCohomologyCupLinear (a b : V → ℤ) (i j : ℕ) :
    letI := vertexTwistCellAtModule R V a i
    letI := vertexTwistCellAtModule R V b j
    letI := vertexTwistCellAtModule R V (a+b) (i+j)
    vertexTwistCellCohomologyAt R V a i →ₗ[R] vertexTwistCellCohomologyAt R V b j →ₗ[R]
      vertexTwistCellCohomologyAt R V (a+b) (i+j) :=
  vertexTwistCellCohomologyCupLinearAt R V a b (i+j) i j

/-- Original closed degree-zero cell cochains compute actual degree zero over every base ring. -/
def vertexTwistCellActualZeroLinearEquiv (a : V → ℤ) :
    letI := vertexTwistCellAtModule R V a 0
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 0) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 0
    vertexTwistCellCohomologyAt R V a 0 ≃ₗ[R] Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 0 :=
  schemeBaseFiniteCubicalZeroActualLinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a)
    (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)

variable [IsNoetherianRing R]

/-- The original vertex resolution computes actual cohomology linearly in every degree, with its original representatives. -/
def vertexTwistCellActualAtLinearEquiv (a : V → ℤ) (n : ℕ) :
    letI := vertexTwistCellAtModule R V a n
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) n
    vertexTwistCellCohomologyAt R V a n ≃ₗ[R] Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) n :=
  schemeBaseFiniteCubicalAtActualLinearEquiv (vertexToBase R V) (vertexTwistSheaf R V a)
    (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V) (vertexTwistCellSheaf_terms_acyclic R V a) n

/-- The uniform comparison retains the original augmentation-only degree-zero linear comparison. -/
theorem vertexTwistCellActualAtLinearEquiv_zero (a : V → ℤ) :
    letI := vertexTwistCellAtModule R V a 0
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) 0) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) 0
    vertexTwistCellActualAtLinearEquiv R V a 0 = vertexTwistCellActualZeroLinearEquiv R V a := rfl

/-- Every positive-degree comparison is the existing original vertex comparison itself. -/
theorem vertexTwistCellActualAtLinearEquiv_succ (a : V → ℤ) (n : ℕ) :
    letI := vertexTwistCellAtModule R V a (n+1)
    letI : Module R (Sheaf.H.{1} (vertexTwistAbelianSheaf R V a) (n+1)) :=
      schemeBaseCohomologyModule (vertexToBase R V) (vertexTwistSheaf R V a) (n+1)
    vertexTwistCellActualAtLinearEquiv R V a (n+1) = vertexTwistCellActualLinearEquiv R V a n := rfl

/-- The image of each original quotient cup class is its specified original Yoneda cup representative. -/
theorem vertexTwistCellCohomologyCup_actual_class (a b : V → ℤ) (n i j : ℕ)
    (x : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V a) i)
    (y : (cubicalTower (vertexCoordinateOpen R V)).cycles (vertexTwistAbelianSheaf R V b) j) :
    letI := augmentation_epi (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
    vertexTwistCellActualAtLinearEquiv R V (a+b) n
      (vertexTwistCellCohomologyCupAt R V a b n i j
        ((cubicalTower (vertexCoordinateOpen R V)).classAt (vertexTwistAbelianSheaf R V a) i x)
        ((cubicalTower (vertexCoordinateOpen R V)).classAt (vertexTwistAbelianSheaf R V b) j y)) =
      localSheafTopEquiv (vertexTwistAbelianSheaf R V (a+b)) n
        ((Ext.mk₀ (complexAugmentationIso _ (augmentation (vertexCoordinateOpen R V))
          (augmentation_zero (vertexCoordinateOpen R V)) (augmentation_exact (vertexCoordinateOpen R V))).inv).comp
            ((cubicalTower (vertexCoordinateOpen R V)).cocycleComparison (vertexTwistAbelianSheaf R V (a+b)) n
              (cubicalCyclesCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j x y))
                (zero_add n)) := by
  letI := augmentation_epi (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
  change finiteCubicalActualAtEquiv (vertexCoordinateOpen R V) (vertexTwistAbelianSheaf R V (a+b))
    (vertexCellChartOpen_cover R V) (vertexTwistCellSheaf_terms_acyclic R V (a+b)) n
    (vertexTwistCellCohomologyCupAt R V a b n i j _ _) = _
  rw [vertexTwistCellCohomologyCupAt_class,finiteCubicalActualAtEquiv_class]

end
end BPFixedPoints.ProjectiveLine
