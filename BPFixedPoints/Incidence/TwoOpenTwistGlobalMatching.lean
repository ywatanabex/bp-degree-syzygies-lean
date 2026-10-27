import BPFixedPoints.Incidence.TwoOpenTwistSections
import BPFixedPoints.Incidence.TwoOpenTwistLocal
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Actual global matching equations for a genuine two-open twisted sheaf

Evaluation and biproduct preservation identify the original chart-module pair.
The maps are the genuine open-subscheme restrictions and overlap unit action.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

/-- Global sections of the pushed-forward open structure module have their genuine original scalar action. -/
noncomputable def openUnitGlobalSectionsEquiv (U : X.Opens) :
    Γ(openUnitModule X U, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(U.toScheme, ⊤) :=
  LinearEquiv.refl _ _

/-- The actual pushed-forward open restriction on global sections is the genuine open-subscheme pullback. -/
theorem openUnitRestriction_global {U V : X.Opens} (h : U ≤ V)
    (s : Γ(V.toScheme, ⊤)) :
    (openUnitRestriction X h).app ⊤ s = (X.homOfLE h).appTop s := by
  dsimp only [openUnitRestriction]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change U.toScheme.presheaf.map (𝟙 (op ⊤)) ((X.homOfLE h).appTop s) = _
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Actual global overlap multiplication is multiplication by the original overlap function. -/
theorem overlapMultiplication_global (U V : X.Opens)
    (r s : Γ((U ⊓ V).toScheme, ⊤)) :
    (overlapMultiplication X U V r).app ⊤ s = s * r := by
  change (unitGlobalMultiplication (U ⊓ V).toScheme r).val.app (op ⊤) s = _
  rw [unitGlobalMultiplication_app]
  change s * (U ⊓ V).toScheme.presheaf.map (𝟙 (op ⊤)) r = s * r
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- Actual global sections of the chart biproduct are the original pair of chart functions. -/
noncomputable def twoOpenChartPairSectionsEquiv (U V : X.Opens) :
    Γ(openUnitModule X U ⊞ openUnitModule X V, ⊤) ≃ₗ[Γ(X, ⊤)]
      (Γ(U.toScheme, ⊤) × Γ(V.toScheme, ⊤)) := by
  let F := SheafOfModules.evaluation.{u} X.ringCatSheaf (op ⊤)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact (F.mapBiprod (openUnitModule X U) (openUnitModule X V) ≪≫
      ModuleCat.biprodIsoProd _ _).toLinearEquiv

/-- The genuine pair comparison preserves the original left section projection. -/
theorem twoOpenChartPairSectionsEquiv_fst (U V : X.Opens)
    (s : Γ(openUnitModule X U ⊞ openUnitModule X V, ⊤)) :
    (twoOpenChartPairSectionsEquiv X U V s).1 =
      (biprod.fst : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X U).app ⊤ s := by
  let F := SheafOfModules.evaluation.{u} X.ringCatSheaf (op ⊤)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have h : (ModuleCat.biprodIsoProd (F.obj (openUnitModule X U))
      (F.obj (openUnitModule X V))).hom ≫
      ModuleCat.ofHom (LinearMap.fst (Γ(X, ⊤)) _ _) = biprod.fst := by
    apply (cancel_epi (ModuleCat.biprodIsoProd _ _).inv).mp
    simp only [Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  have hm := congrArg (fun k => (F.mapBiprod (openUnitModule X U) (openUnitModule X V)).hom ≫ k) h
  have hm' : (F.mapBiprod (openUnitModule X U) (openUnitModule X V) ≪≫
      ModuleCat.biprodIsoProd _ _).hom ≫
      ModuleCat.ofHom (LinearMap.fst (Γ(X, ⊤)) _ _) = F.map biprod.fst := by
    simpa only [Iso.trans_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.lift_fst] using hm
  exact ConcreteCategory.congr_hom hm' s

/-- The genuine pair comparison preserves the original right section projection. -/
theorem twoOpenChartPairSectionsEquiv_snd (U V : X.Opens)
    (s : Γ(openUnitModule X U ⊞ openUnitModule X V, ⊤)) :
    (twoOpenChartPairSectionsEquiv X U V s).2 =
      (biprod.snd : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X V).app ⊤ s := by
  let F := SheafOfModules.evaluation.{u} X.ringCatSheaf (op ⊤)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  letI := preservesBinaryBiproducts_of_preservesBinaryProducts F
  have h : (ModuleCat.biprodIsoProd (F.obj (openUnitModule X U))
      (F.obj (openUnitModule X V))).hom ≫
      ModuleCat.ofHom (LinearMap.snd (Γ(X, ⊤)) _ _) = biprod.snd := by
    apply (cancel_epi (ModuleCat.biprodIsoProd _ _).inv).mp
    simp only [Iso.inv_hom_id_assoc, ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl
  have hm := congrArg (fun k => (F.mapBiprod (openUnitModule X U) (openUnitModule X V)).hom ≫ k) h
  have hm' : (F.mapBiprod (openUnitModule X U) (openUnitModule X V) ≪≫
      ModuleCat.biprodIsoProd _ _).hom ≫
      ModuleCat.ofHom (LinearMap.snd (Γ(X, ⊤)) _ _) = F.map biprod.snd := by
    simpa only [Iso.trans_hom, Functor.mapBiprod_hom, Category.assoc,
      biprod.lift_snd] using hm
  exact ConcreteCategory.congr_hom hm' s

/-- Genuine restriction of open-subscheme functions, linear over the actual global structure ring. -/
noncomputable def openGlobalRestrictionLinear {U V : X.Opens} (h : U ≤ V) :
    Γ(V.toScheme, ⊤) →ₗ[Γ(X, ⊤)] Γ(U.toScheme, ⊤) :=
  (openUnitRestriction X h).val.app (op ⊤) |>.hom

/-- Genuine overlap multiplication, linear over the actual global structure ring. -/
noncomputable def overlapGlobalMultiplicationLinear (U V : X.Opens)
    (r : Γ((U ⊓ V).toScheme, ⊤)) :
    Γ((U ⊓ V).toScheme, ⊤) →ₗ[Γ(X, ⊤)] Γ((U ⊓ V).toScheme, ⊤) :=
  (overlapMultiplication X U V r).val.app (op ⊤) |>.hom

/-- The independently specified actual chart-function matching differential. -/
noncomputable def twoOpenGlobalDifference (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (Γ(U.toScheme, ⊤) × Γ(V.toScheme, ⊤)) →ₗ[Γ(X, ⊤)] Γ((U ⊓ V).toScheme, ⊤) :=
  (openGlobalRestrictionLinear X (show U ⊓ V ≤ U from inf_le_left)).comp (LinearMap.fst _ _ _) -
    ((overlapGlobalMultiplicationLinear X U V (u : Γ((U ⊓ V).toScheme, ⊤))).comp
      (openGlobalRestrictionLinear X (show U ⊓ V ≤ V from inf_le_right))).comp (LinearMap.snd _ _ _)

/-- Its formula is the original genuine restriction difference with the original transition unit. -/
theorem twoOpenGlobalDifference_apply (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (s : Γ(U.toScheme, ⊤) × Γ(V.toScheme, ⊤)) :
    twoOpenGlobalDifference X U V u s =
      (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).appTop s.1 -
        (X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop s.2 *
          (u : Γ((U ⊓ V).toScheme, ⊤)) := by
  dsimp only [twoOpenGlobalDifference, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, openGlobalRestrictionLinear,
    overlapGlobalMultiplicationLinear]
  change Sub.sub (α := Γ((U ⊓ V).toScheme, ⊤))
    ((openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left)).app ⊤ s.1)
    ((overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))).app ⊤
      ((openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right)).app ⊤ s.2)) = _
  rw [openUnitRestriction_global, overlapMultiplication_global, openUnitRestriction_global]
  rfl

/-- Evaluation of the original sheaf matching map has the genuine chart-function formula. -/
theorem twoOpenTwistDifference_global (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ)
    (s : Γ(openUnitModule X U ⊞ openUnitModule X V, ⊤)) :
    (twoOpenTwistDifference X U V u).app ⊤ s =
      (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)).appTop
        ((biprod.fst : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X U).app ⊤ s) -
      (X.homOfLE (show U ⊓ V ≤ V from inf_le_right)).appTop
        ((biprod.snd : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X V).app ⊤ s) *
          (u : Γ((U ⊓ V).toScheme, ⊤)) := by
  have he : twoOpenTwistDifference X U V u =
      biprod.fst ≫ openUnitRestriction X inf_le_left -
        (biprod.snd ≫ openUnitRestriction X inf_le_right) ≫
          overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤)) := by
    simp only [twoOpenTwistDifference, biprod.desc_eq, Preadditive.comp_neg,
      sub_eq_add_neg, Category.assoc]
  rw [he, Scheme.Modules.Hom.sub_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  change Sub.sub (α := Γ((U ⊓ V).toScheme, ⊤))
    ((openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left)).app ⊤
      ((biprod.fst : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X U).app ⊤ s))
    ((overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))).app ⊤
      ((openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right)).app ⊤
        ((biprod.snd : openUnitModule X U ⊞ openUnitModule X V ⟶ openUnitModule X V).app ⊤ s))) = _
  rw [openUnitRestriction_global, overlapMultiplication_global, openUnitRestriction_global]
  rfl

/-- The actual chart pair comparison intertwines the independently specified matching differentials. -/
theorem twoOpenChartPairSectionsEquiv_difference (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ)
    (s : Γ(openUnitModule X U ⊞ openUnitModule X V, ⊤)) :
    twoOpenGlobalDifference X U V u (twoOpenChartPairSectionsEquiv X U V s) =
      (twoOpenTwistDifference X U V u).app ⊤ s := by
  rw [twoOpenGlobalDifference_apply, twoOpenChartPairSectionsEquiv_fst,
    twoOpenChartPairSectionsEquiv_snd, twoOpenTwistDifference_global]


end BPFixedPoints.SheafTools
