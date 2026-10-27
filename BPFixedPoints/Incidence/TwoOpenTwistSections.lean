import BPFixedPoints.Incidence.TwoOpenTwistSheaf
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual sections of the twisted gluing sheaf

Mathlib's evaluation functor preserves kernels. Hence sections on every open,
including the whole space, are the actual kernel of the original twisted
matching map evaluated there. This asserts no higher acyclicity or local
freeness hypothesis.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

local instance moduleEvaluation_preservesZero (W : X.Opens) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- Genuine section evaluation preserves the actual twisted gluing kernel. -/
noncomputable def twoOpenTwistSectionsIsoKer (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) :
    (SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).obj (twoOpenTwistModule X U V u) ≅
      ModuleCat.of (Γ(X, W))
        (LinearMap.ker ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).map
          (twoOpenTwistDifference X U V u)).hom) :=
  PreservesKernel.iso (SheafOfModules.evaluation.{u} X.ringCatSheaf (op W))
      (twoOpenTwistDifference X U V u) ≪≫
    ModuleCat.kernelIsoKer _

/-- The comparison is an actual linear isomorphism on the structure-module sections. -/
noncomputable def twoOpenTwistSectionsEquivKer (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) :
    Γ(twoOpenTwistModule X U V u, W) ≃ₗ[Γ(X, W)]
      LinearMap.ker ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).map
        (twoOpenTwistDifference X U V u)).hom :=
  (twoOpenTwistSectionsIsoKer X U V u W).toLinearEquiv

/-- The comparison preserves the original inclusion into the actual pair of chart modules. -/
@[reassoc] theorem twoOpenTwistSectionsIsoKer_hom_subtype (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) :
    (twoOpenTwistSectionsIsoKer X U V u W).hom ≫
      ModuleCat.ofHom (((SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).map
        (twoOpenTwistDifference X U V u)).hom.ker.subtype) =
      (SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).map
        (twoOpenTwistInclusion X U V u) := by
  let F : X.Modules ⥤ ModuleCat.{u} (Γ(X, W)) :=
    SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  dsimp only [twoOpenTwistSectionsIsoKer, Iso.trans_hom]
  rw [Category.assoc]
  erw [ModuleCat.kernelIsoKer_hom_ker_subtype]
  simpa only [PreservesKernel.iso_hom, twoOpenTwistInclusion] using
    kernelComparison_comp_ι (twoOpenTwistDifference X U V u)
      F

/-- Actual sections on any open, including the whole space, equal the actual matching kernel. -/
theorem twoOpenTwistSections_comparison (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) :
    Nonempty (Γ(twoOpenTwistModule X U V u, W) ≃ₗ[Γ(X, W)]
      LinearMap.ker ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op W)).map
        (twoOpenTwistDifference X U V u)).hom) :=
  ⟨twoOpenTwistSectionsEquivKer X U V u W⟩

end BPFixedPoints.SheafTools
