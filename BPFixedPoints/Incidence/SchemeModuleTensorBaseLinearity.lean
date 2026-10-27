import BPFixedPoints.Incidence.SchemeModuleTensorSections
import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars

/-! # Original geometric base linearity of actual tensor sections

The source and target actions restrict the original structure-ring actions
along the original structural morphism. Pointwise structure-ring bilinearity
therefore gives base bilinearity before any chart or state comparison.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M N : X.Modules)

/-- The original pure section tensor preserves geometric base scalars in its first factor. -/
theorem moduleTensorPureSection_base_smul_left (U : X.Opens) (r : R) (x : Γ(M, U)) (y : Γ(N, U)) :
    letI := SchemeTools.schemeBaseOpenModuleSections f M U
    letI := SchemeTools.schemeBaseOpenModuleSections f N U
    letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
    moduleTensorPureSection X M N U (r • x) y = r • moduleTensorPureSection X M N U x y := by
  letI := SchemeTools.schemeBaseOpenModuleSections f M U
  letI := SchemeTools.schemeBaseOpenModuleSections f N U
  letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
  exact moduleTensorPureSection_smul_left X M N U (SchemeTools.schemeBaseCoefficientAt f U r) x y

/-- The original pure section tensor preserves geometric base scalars in its second factor. -/
theorem moduleTensorPureSection_base_smul_right (U : X.Opens) (r : R) (x : Γ(M, U)) (y : Γ(N, U)) :
    letI := SchemeTools.schemeBaseOpenModuleSections f M U
    letI := SchemeTools.schemeBaseOpenModuleSections f N U
    letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
    moduleTensorPureSection X M N U x (r • y) = r • moduleTensorPureSection X M N U x y := by
  letI := SchemeTools.schemeBaseOpenModuleSections f M U
  letI := SchemeTools.schemeBaseOpenModuleSections f N U
  letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
  exact moduleTensorPureSection_smul_right X M N U (SchemeTools.schemeBaseCoefficientAt f U r) x y

/-- Actual pure sections give a bilinear map for the independently induced geometric base actions. -/
noncomputable def moduleTensorBaseSectionBilinear (U : X.Opens) :
    letI := SchemeTools.schemeBaseOpenModuleSections f M U
    letI := SchemeTools.schemeBaseOpenModuleSections f N U
    letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
    Γ(M, U) →ₗ[R] Γ(N, U) →ₗ[R] Γ(moduleTensor X M N, U) := by
  letI := SchemeTools.schemeBaseOpenModuleSections f M U
  letI := SchemeTools.schemeBaseOpenModuleSections f N U
  letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
  refine
    { toFun := fun x =>
        { toFun := moduleTensorPureSection X M N U x
          map_add' := moduleTensorPureSection_add_right X M N U x
          map_smul' := fun r y => moduleTensorPureSection_base_smul_right f M N U r x y }
      map_add' := ?_
      map_smul' := ?_ }
  · intro x x'
    ext y
    exact moduleTensorPureSection_add_left X M N U x x' y
  · intro r x
    ext y
    exact moduleTensorPureSection_base_smul_left f M N U r x y

/-- The geometric base-bilinear map retains exactly the original actual pure tensor section. -/
theorem moduleTensorBaseSectionBilinear_apply (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    letI := SchemeTools.schemeBaseOpenModuleSections f M U
    letI := SchemeTools.schemeBaseOpenModuleSections f N U
    letI := SchemeTools.schemeBaseOpenModuleSections f (moduleTensor X M N) U
    moduleTensorBaseSectionBilinear f M N U x y = moduleTensorPureSection X M N U x y := rfl

end BPFixedPoints.SheafTools
