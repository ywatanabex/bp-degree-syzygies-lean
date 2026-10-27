import BPFixedPoints.Incidence.TwoOpenTwistLocal

/-! # Original transition unit between the genuine overlap trivializations

Both overlap frames come from the original chart projections and restrictions.
Naturality of Mathlib's actual restriction counit identifies their transition
with multiplication by the original overlap unit.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

/-- The left frame on the actual overlap comes from the original left chart projection. -/
noncomputable def twoOpenTwistOverlapLeftIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistModule X U V u).restrict (U ⊓ V).ι ≅
      SheafOfModules.unit (U ⊓ V).toScheme.ringCatSheaf := by
  have := twoOpenTwist_left_restrict_isIso_of_le X U V u (U ⊓ V) inf_le_left
  have := openUnitRestriction_restrict_isIso X
    (show U ⊓ V ≤ U from inf_le_left) (U ⊓ V) inf_le_left
  exact asIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.fst)) ≪≫
    asIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map
      (openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left))) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso (U ⊓ V).ι).app
      (SheafOfModules.unit (U ⊓ V).toScheme.ringCatSheaf)

/-- The right frame on the actual overlap comes from the original right chart projection. -/
noncomputable def twoOpenTwistOverlapRightIso (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistModule X U V u).restrict (U ⊓ V).ι ≅
      SheafOfModules.unit (U ⊓ V).toScheme.ringCatSheaf := by
  have := twoOpenTwist_right_restrict_isIso_of_le X U V u (U ⊓ V) inf_le_right
  have := openUnitRestriction_restrict_isIso X
    (show U ⊓ V ≤ V from inf_le_right) (U ⊓ V) inf_le_left
  exact asIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map
      (twoOpenTwistInclusion X U V u ≫ biprod.snd)) ≪≫
    asIso ((Scheme.Modules.restrictFunctor (U ⊓ V).ι).map
      (openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right))) ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso (U ⊓ V).ι).app
      (SheafOfModules.unit (U ⊓ V).toScheme.ringCatSheaf)

/-- The genuine overlap frames differ by exactly the original unit, as actual module morphisms. -/
theorem twoOpenTwist_overlap_transition (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    (twoOpenTwistOverlapLeftIso X U V u).hom =
      (twoOpenTwistOverlapRightIso X U V u).hom ≫
        unitGlobalMultiplication (U ⊓ V).toScheme (u : Γ((U ⊓ V).toScheme, ⊤)) := by
  let F := Scheme.Modules.restrictFunctor (U ⊓ V).ι
  let m := unitGlobalMultiplication (U ⊓ V).toScheme (u : Γ((U ⊓ V).toScheme, ⊤))
  have hc := (Scheme.Modules.restrictFunctorAdjCounitIso (U ⊓ V).ι).hom.naturality m
  let c := (Scheme.Modules.restrictFunctorAdjCounitIso (U ⊓ V).ι).hom.app
    (SheafOfModules.unit (U ⊓ V).toScheme.ringCatSheaf)
  have hm := congrArg (fun f => F.map f ≫ c) (twoOpenTwist_matching X U V u)
  dsimp only [twoOpenTwistOverlapLeftIso, twoOpenTwistOverlapRightIso,
    Iso.trans_hom, asIso_hom]
  simp only [Functor.map_comp, Category.assoc] at hm ⊢
  change F.map (twoOpenTwistInclusion X U V u) ≫ F.map biprod.fst ≫
      F.map (openUnitRestriction X inf_le_left) ≫ c = _
  rw [hm]
  simpa only [F, m, c, overlapMultiplication, Functor.comp_map, Functor.id_map,
    Category.assoc, Iso.app_hom] using congrArg (fun a =>
      F.map (twoOpenTwistInclusion X U V u) ≫ F.map biprod.snd ≫
        F.map (openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right)) ≫ a) hc

end BPFixedPoints.SheafTools
