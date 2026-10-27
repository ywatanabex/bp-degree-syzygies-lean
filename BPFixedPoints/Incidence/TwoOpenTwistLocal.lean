import BPFixedPoints.Incidence.TwoOpenTwistSheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Local rank-one trivializations of the actual twisted gluing sheaf

The local comparisons use Mathlib's restriction functor and its actual
structure-module counit. The gluing kernel is compared with a pullback,
whose projection is invertible when the other restriction is invertible.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u

/-- On an open inside its image, an open immersion induces an invertible unit-module map. -/
theorem unitToPushforward_isIso_app {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    [IsOpenImmersion f] (W : Z.Opens) (hW : W ≤ f.opensRange) :
    IsIso ((SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val.app (op W)) := by
  have : IsIso (f.app W) := f.isIso_app W hW
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (f.app W)
  exact ConcreteCategory.bijective_of_isIso (f.app W)

variable (X : Scheme.{u})

/-- Global multiplication sends the genuine unit frame to the original global section. -/
theorem unitGlobalMultiplication_top_one (r : Γ(X, ⊤)) :
    (unitGlobalMultiplication X r).val.app (op ⊤) (1 : Γ(X, ⊤)) = r := by
  rw [unitGlobalMultiplication_app]
  change 1 * X.presheaf.map (𝟙 (op ⊤)) r = r
  rw [CategoryTheory.Functor.map_id]
  change 1 * r = r
  exact one_mul r

/-- Restriction between pushed-forward open structure modules is invertible where the opens agree. -/
theorem openUnitRestriction_isIso_app {U V : X.Opens} (h : U ≤ V)
    (W : X.Opens) (hW : W ⊓ V ≤ U) :
    IsIso ((openUnitRestriction X h).app W) := by
  have hi : V.ι ⁻¹ᵁ W ≤ (X.homOfLE h).opensRange := by
    rw [X.opensRange_homOfLE]
    intro x hx
    exact hW ⟨hx, x.property⟩
  have ht := unitToPushforward_isIso_app (X.homOfLE h) (V.ι ⁻¹ᵁ W) hi
  have : IsIso (((Scheme.Modules.pushforward V.ι).map
      (SheafOfModules.unitToPushforwardObjUnit (X.homOfLE h).toRingCatSheafHom)).app W) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    exact ConcreteCategory.bijective_of_isIso
      ((SheafOfModules.unitToPushforwardObjUnit (X.homOfLE h).toRingCatSheafHom).val.app
        (op (V.ι ⁻¹ᵁ W)))
  dsimp only [openUnitRestriction]
  rw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app]
  infer_instance

/-- The actual open-module restriction becomes invertible after restricting inside any agreeing open. -/
theorem openUnitRestriction_restrict_isIso {U V : X.Opens} (h : U ≤ V)
    (S : X.Opens) (hS : S ⊓ V ≤ U) :
    IsIso ((Scheme.Modules.restrictFunctor S.ι).map (openUnitRestriction X h)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  change IsIso ((openUnitRestriction X h).app (S.ι ''ᵁ W))
  apply openUnitRestriction_isIso_app X h
  intro x hx
  apply hS
  exact ⟨by obtain ⟨y, hy, rfl⟩ := hx.1; exact y.property, hx.2⟩

/-- The actual twisted gluing kernel is the actual pullback of its two matching maps. -/
noncomputable def twoOpenTwistPullbackIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    twoOpenTwistModule X U V u ≅
      pullback (openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left))
        (openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right) ≫
          overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))) :=
  (kernelIsKernel (twoOpenTwistDifference X U V u)).conePointUniqueUpToIso
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _)

/-- The canonical pullback comparison preserves the actual inclusion into both charts. -/
@[reassoc] theorem twoOpenTwistPullbackIso_hom_pair (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistPullbackIso X U V u).hom ≫
      Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct _ _ =
        twoOpenTwistInclusion X U V u := by
  exact (kernelIsKernel (twoOpenTwistDifference X U V u)).conePointUniqueUpToIso_hom_comp
    (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct _ _) .zero

/-- The original inclusion projections form the genuine matching pullback square. -/
theorem twoOpenTwist_isPullback (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    IsPullback (twoOpenTwistInclusion X U V u ≫ biprod.fst)
      (twoOpenTwistInclusion X U V u ≫ biprod.snd)
      (openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left))
      (openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right) ≫
        overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))) := by
  refine IsPullback.of_iso_pullback
    (fst := twoOpenTwistInclusion X U V u ≫ biprod.fst)
    (snd := twoOpenTwistInclusion X U V u ≫ biprod.snd)
    ⟨twoOpenTwist_matching X U V u⟩ (twoOpenTwistPullbackIso X U V u) ?_ ?_
  · simpa only [Category.assoc, Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct,
      biprod.lift_fst] using congrArg (fun a => a ≫ biprod.fst)
        (twoOpenTwistPullbackIso_hom_pair X U V u)
  · simpa only [Category.assoc, Abelian.PullbackToBiproductIsKernel.pullbackToBiproduct,
      biprod.lift_snd] using congrArg (fun a => a ≫ biprod.snd)
        (twoOpenTwistPullbackIso_hom_pair X U V u)

/-- Twisting by an actual overlap unit is an actual module automorphism. -/
instance overlapMultiplication_isIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    IsIso (overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))) := by
  have : IsIso (unitGlobalMultiplication (U ⊓ V).toScheme
      (u : Γ((U ⊓ V).toScheme, ⊤))) :=
    inferInstanceAs (IsIso (unitGlobalMultiplicationIso (U ⊓ V).toScheme u).hom)
  dsimp only [overlapMultiplication]
  infer_instance

/-- The original left projection is invertible over every open contained in the left chart. -/
theorem twoOpenTwist_left_app_isIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) (hW : W ≤ U) :
    IsIso ((twoOpenTwistInclusion X U V u ≫ biprod.fst).app W) := by
  let F : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesFiniteLimits ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    ⟨fun J _ _ => by infer_instance⟩
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have := openUnitRestriction_isIso_app X
    (show U ⊓ V ≤ V from inf_le_right) W (inf_le_inf_right V hW)
  have h := (twoOpenTwist_isPullback X U V u).map F
  apply h.isIso_fst_of_isIso (by
    change IsIso ((openUnitRestriction X inf_le_right ≫
      overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))).app W)
    rw [Scheme.Modules.Hom.comp_app]
    infer_instance)

/-- The original right projection is invertible over every open contained in the right chart. -/
theorem twoOpenTwist_right_app_isIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (W : X.Opens) (hW : W ≤ V) :
    IsIso ((twoOpenTwistInclusion X U V u ≫ biprod.snd).app W) := by
  let F : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesFiniteLimits ((evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    ⟨fun J _ _ => by infer_instance⟩
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have := openUnitRestriction_isIso_app X
    (show U ⊓ V ≤ U from inf_le_left) W ((inf_le_inf_right U hW).trans_eq (inf_comm V U))
  have h := (twoOpenTwist_isPullback X U V u).map F
  exact h.isIso_snd_of_isIso (by
    change IsIso ((openUnitRestriction X inf_le_left).app W)
    infer_instance)

/-- The original left projection is invertible on every actual open inside the left chart. -/
theorem twoOpenTwist_left_restrict_isIso_of_le (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (S : X.Opens) (hS : S ≤ U) :
    IsIso ((Scheme.Modules.restrictFunctor S.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.fst)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  change IsIso ((twoOpenTwistInclusion X U V u ≫ biprod.fst).app (S.ι ''ᵁ W))
  apply twoOpenTwist_left_app_isIso X U V u
  rintro x ⟨y, hy, rfl⟩
  exact hS y.property

/-- The original right projection is invertible on every actual open inside the right chart. -/
theorem twoOpenTwist_right_restrict_isIso_of_le (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (S : X.Opens) (hS : S ≤ V) :
    IsIso ((Scheme.Modules.restrictFunctor S.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.snd)) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro W
  change IsIso ((twoOpenTwistInclusion X U V u ≫ biprod.snd).app (S.ι ''ᵁ W))
  apply twoOpenTwist_right_app_isIso X U V u
  rintro x ⟨y, hy, rfl⟩
  exact hS y.property

/-- The original left projection is invertible on the actual left open. -/
theorem twoOpenTwist_left_restrict_isIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.fst)) :=
  twoOpenTwist_left_restrict_isIso_of_le X U V u U le_rfl

/-- The original right projection is invertible on the actual right open. -/
theorem twoOpenTwist_right_restrict_isIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.snd)) :=
  twoOpenTwist_right_restrict_isIso_of_le X U V u V le_rfl

/-- A genuine rank-one trivialization on the original left open. -/
noncomputable def twoOpenTwistLeftIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistModule X U V u).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf := by
  have := twoOpenTwist_left_restrict_isIso X U V u
  exact asIso ((Scheme.Modules.restrictFunctor U.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.fst)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso U.ι).app (SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- A genuine rank-one trivialization on the original right open. -/
noncomputable def twoOpenTwistRightIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistModule X U V u).restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf := by
  have := twoOpenTwist_right_restrict_isIso X U V u
  exact asIso ((Scheme.Modules.restrictFunctor V.ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.snd)) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso V.ι).app (SheafOfModules.unit V.toScheme.ringCatSheaf)

/-- Both local rank-one trivializations exist on the original opens without acyclicity assumptions. -/
theorem twoOpenTwist_rankOne (U V : X.Opens) (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    Nonempty ((twoOpenTwistModule X U V u).restrict U.ι ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) ∧
    Nonempty ((twoOpenTwistModule X U V u).restrict V.ι ≅
      SheafOfModules.unit V.toScheme.ringCatSheaf) :=
  ⟨⟨twoOpenTwistLeftIso X U V u⟩, ⟨twoOpenTwistRightIso X U V u⟩⟩

end BPFixedPoints.SheafTools
