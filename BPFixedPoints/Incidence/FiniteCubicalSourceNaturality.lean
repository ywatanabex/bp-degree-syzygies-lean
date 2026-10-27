import BPFixedPoints.Incidence.AcyclicResolutionAugmentedSourceNaturality
import BPFixedPoints.Incidence.FiniteCubicalCohomologyDegree
import BPFixedPoints.Incidence.AcyclicResolutionSourceLinearity

/-! # The original actual cubical comparison preserves supplied source chain maps

Use the same actual underlying abelian sheaves, original augmentations,
original quotient representatives and native Yoneda comparison. The
augmentation-preserving chain map is supplied, not assumed to exist by
projectivity of the original free-open terms.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T]
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (U : I → Fin 2 → Opens T) (W : J → Fin 2 → Opens T)
local instance cubicalSourceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (hU : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) (hW : (⊤ : Opens T) ≤ ⨆ b, chartOpen W b)
variable (f : sheafComplex U ⟶ sheafComplex W) (hf : f.f 0 ≫ augmentation W=augmentation U)
include hf

/-- The original actual cubical comparison identifies source pullback under every supplied original augmentation-preserving chain map. -/
theorem finiteCubicalActualAtEquiv_source
    (aU : ComplexAcyclicAgainst (sheafComplex U) F) (aW : ComplexAcyclicAgainst (sheafComplex W) F)
    (n : ℕ) (x : cubicalCohomologyAt W F n) :
    finiteCubicalActualAtEquiv U F hU aU n
      ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cohomologyAt F n x) =
        finiteCubicalActualAtEquiv W F hW aW n x := by
  letI := augmentation_epi U hU
  letI := augmentation_epi W hW
  obtain ⟨x,rfl⟩ := (cubicalTower W).classAt_surjective F n x
  rw [ExactTower.SourceMap.cohomologyAt_class,finiteCubicalActualAtEquiv_class,finiteCubicalActualAtEquiv_class]
  change localSheafTopEquiv F n
    (augmentedComplexCocycleComparison (sheafComplex U) F (sheafComplex_exact U)
      (augmentation U) (augmentation_zero U) (augmentation_exact U) n
        ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cycles F n x)) =
    localSheafTopEquiv F n
      (augmentedComplexCocycleComparison (sheafComplex W) F (sheafComplex_exact W)
        (augmentation W) (augmentation_zero W) (augmentation_exact W) n x)
  congr 1
  have h := augmentedComplexCocycleComparison_source F (sheafComplex_exact U)
    (augmentation U) (augmentation_zero U) (augmentation_exact U) f (sheafComplex_exact W)
      (augmentation W) (augmentation_zero W) (augmentation_exact W) (𝟙 _) (by simpa using hf) n x
  simpa only [Ext.mk₀_id_comp] using h

/-- Degree-zero source naturality uses the original augmentation only, without term acyclicity. -/
theorem finiteCubicalActualZeroEquiv_source (x : cubicalCohomologyAt W F 0) :
    finiteCubicalActualZeroEquiv U F hU
      ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cohomologyAt F 0 x) =
        finiteCubicalActualZeroEquiv W F hW x := by
  letI := augmentation_epi U hU
  letI := augmentation_epi W hW
  change localSheafTopEquiv F 0
    (augmentedComplexCocycleComparison (sheafComplex U) F (sheafComplex_exact U)
      (augmentation U) (augmentation_zero U) (augmentation_exact U) 0
        ((complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cycles F 0 x)) =
    localSheafTopEquiv F 0
      (augmentedComplexCocycleComparison (sheafComplex W) F (sheafComplex_exact W)
        (augmentation W) (augmentation_zero W) (augmentation_exact W) 0 x)
  congr 1
  have h := augmentedComplexCocycleComparison_source F (sheafComplex_exact U)
    (augmentation U) (augmentation_zero U) (augmentation_exact U) f (sheafComplex_exact W)
      (augmentation W) (augmentation_zero W) (augmentation_exact W) (𝟙 _) (by simpa using hf) 0 x
  simpa only [Ext.mk₀_id_comp] using h

end
end BPFixedPoints.SheafTools.BinaryCells

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory TopologicalSpace ExtResolutionTools SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (b : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (U : I → Fin 2 → X.Opens) (W : J → Fin 2 → X.Opens)
variable (f : sheafComplex U ⟶ sheafComplex W)
local instance geometricSourceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Original cell source pullback is linear for the same independently specified original geometric base action. -/
def schemeBaseCubicalSourceLinear (n : ℕ) :
    letI := schemeBaseCubicalAtModule b M W n
    letI := schemeBaseCubicalAtModule b M U n
    cubicalCohomologyAt W ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n →ₗ[R]
      cubicalCohomologyAt U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n :=
  (complexSourceMap f (sheafComplex_exact U) (sheafComplex_exact W)).cohomologyAtLinear
    (schemeBaseAbelianScalarHom b M) n

/-- The original geometric linear actual comparison is source-natural in every degree. -/
theorem schemeBaseFiniteCubicalAtActualLinearEquiv_source
    (hU : (⊤ : X.Opens) ≤ ⨆ i, chartOpen U i) (hW : (⊤ : X.Opens) ≤ ⨆ i, chartOpen W i)
    (hf : f.f 0 ≫ augmentation W=augmentation U)
    (aU : ComplexAcyclicAgainst (sheafComplex U) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (aW : ComplexAcyclicAgainst (sheafComplex W) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (n : ℕ) (x : cubicalCohomologyAt W ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :
    letI := schemeBaseCubicalAtModule b M W n
    letI := schemeBaseCubicalAtModule b M U n
    letI := schemeBaseCohomologyModule b M n
    schemeBaseFiniteCubicalAtActualLinearEquiv b M U hU aU n
      (schemeBaseCubicalSourceLinear b M U W f n x) =
        schemeBaseFiniteCubicalAtActualLinearEquiv b M W hW aW n x := by
  letI := schemeBaseCubicalAtModule b M W n
  letI := schemeBaseCubicalAtModule b M U n
  letI := schemeBaseCohomologyModule b M n
  exact finiteCubicalActualAtEquiv_source U W _ hU hW f hf aU aW n x

/-- Degree-zero geometric source naturality needs neither term acyclicity nor a Noetherian hypothesis. -/
theorem schemeBaseFiniteCubicalZeroActualLinearEquiv_source
    (hU : (⊤ : X.Opens) ≤ ⨆ i, chartOpen U i) (hW : (⊤ : X.Opens) ≤ ⨆ i, chartOpen W i)
    (hf : f.f 0 ≫ augmentation W=augmentation U)
    (x : cubicalCohomologyAt W ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 0) :
    letI := schemeBaseCubicalAtModule b M W 0
    letI := schemeBaseCubicalAtModule b M U 0
    letI := schemeBaseCohomologyModule b M 0
    schemeBaseFiniteCubicalZeroActualLinearEquiv b M U hU (schemeBaseCubicalSourceLinear b M U W f 0 x) =
      schemeBaseFiniteCubicalZeroActualLinearEquiv b M W hW x := by
  letI := schemeBaseCubicalAtModule b M W 0
  letI := schemeBaseCubicalAtModule b M U 0
  letI := schemeBaseCohomologyModule b M 0
  exact finiteCubicalActualZeroEquiv_source U W _ hU hW f hf x

end
end BPFixedPoints.SchemeTools
