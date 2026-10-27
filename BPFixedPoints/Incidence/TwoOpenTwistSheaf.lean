import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Actual twisted gluing sheaves on two open subschemes

The construction uses Mathlib's genuine sheaves of modules, pushforwards,
biproducts and kernels. A unit on the actual overlap twists the right
restriction map. The actual local rank-one trivializations and native local
freeness are proved in the subsequent local modules. Comparison with the
polynomial Cech coordinates remains a separate property.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme)

/-- The actual structure sheaf on an open, pushed forward as an `O_X`-module. -/
noncomputable def openUnitModule (U : X.Opens) : X.Modules :=
  (Scheme.Modules.pushforward U.ι).obj (SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- Genuine restriction between the pushed-forward structure modules of two opens. -/
noncomputable def openUnitRestriction {U V : X.Opens} (h : U ≤ V) :
    openUnitModule X V ⟶ openUnitModule X U :=
  (Scheme.Modules.pushforward V.ι).map
      (SheafOfModules.unitToPushforwardObjUnit (X.homOfLE h).toRingCatSheafHom) ≫
    (Scheme.Modules.pushforwardComp (X.homOfLE h) V.ι).hom.app
      (SheafOfModules.unit U.toScheme.ringCatSheaf) ≫
    (Scheme.Modules.pushforwardCongr (X.homOfLE_ι h)).hom.app
      (SheafOfModules.unit U.toScheme.ringCatSheaf)

/-- A global regular function gives its compatible family of actual restrictions. -/
noncomputable def unitGlobalSection (r : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun U => X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r)
    (by
      intro U V f
      change (X.presheaf.map f).hom
        ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom r) = _
      rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
      rfl)

/-- Multiplication by a global function as a genuine morphism of structure modules. -/
noncomputable def unitGlobalMultiplication (r : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (unitGlobalSection X r)

/-- Its actual component multiplies by the original restriction of the global function. -/
theorem unitGlobalMultiplication_app (r : Γ(X, ⊤)) (U : X.Opens) (s : Γ(X, U)) :
    (unitGlobalMultiplication X r).val.app (op U) s =
      s * X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r := by
  rfl

/-- Actual global multiplications compose by multiplying the original sections. -/
theorem unitGlobalMultiplication_mul (r s : Γ(X, ⊤)) :
    unitGlobalMultiplication X r ≫ unitGlobalMultiplication X s =
      unitGlobalMultiplication X (r*s) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(X, U.unop) at x
  change (x * X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) *
    X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s =
      x * X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (r*s)
  rw [map_mul, mul_assoc]

/-- Multiplication by the actual constant one is the identity sheaf morphism. -/
theorem unitGlobalMultiplication_one :
    unitGlobalMultiplication X 1 = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(X, U.unop) at x
  change x * X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op 1 = x
  simp

/-- A unit gives an actual automorphism of the structure module with the original inverse. -/
noncomputable def unitGlobalMultiplicationIso (u : Γ(X, ⊤)ˣ) :
    SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf where
  hom := unitGlobalMultiplication X (u : Γ(X, ⊤))
  inv := unitGlobalMultiplication X (↑(u⁻¹) : Γ(X, ⊤))
  hom_inv_id := by rw [unitGlobalMultiplication_mul, Units.mul_inv, unitGlobalMultiplication_one]
  inv_hom_id := by rw [unitGlobalMultiplication_mul, Units.inv_mul, unitGlobalMultiplication_one]

/-- The actual overlap structure module. -/
noncomputable def overlapUnitModule (U V : X.Opens) : X.Modules :=
  openUnitModule X (U ⊓ V)

/-- Push actual multiplication on the overlap into the ambient module category. -/
noncomputable def overlapMultiplication (U V : X.Opens)
    (r : Γ((U ⊓ V).toScheme, ⊤)) : overlapUnitModule X U V ⟶ overlapUnitModule X U V :=
  (Scheme.Modules.pushforward (U ⊓ V).ι).map (unitGlobalMultiplication (U ⊓ V).toScheme r)

/-- Difference of the genuine left restriction and the twisted genuine right restriction. -/
noncomputable def twoOpenTwistDifference (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    openUnitModule X U ⊞ openUnitModule X V ⟶ overlapUnitModule X U V :=
  biprod.desc (openUnitRestriction X (show U ⊓ V ≤ U from inf_le_left))
    (-(openUnitRestriction X (show U ⊓ V ≤ V from inf_le_right) ≫
      overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))))

/-- Actual sheaf of `O_X`-modules glued by the specified overlap unit. -/
noncomputable def twoOpenTwistModule (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) : X.Modules :=
  kernel (twoOpenTwistDifference X U V u)

/-- The actual twisted sheaf embeds in the direct sum of the two actual chart modules. -/
noncomputable def twoOpenTwistInclusion (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    twoOpenTwistModule X U V u ⟶ openUnitModule X U ⊞ openUnitModule X V :=
  kernel.ι (twoOpenTwistDifference X U V u)

/-- Sections of the constructed sheaf satisfy the actual twisted matching relation. -/
@[reassoc] theorem twoOpenTwistInclusion_difference (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    twoOpenTwistInclusion X U V u ≫ twoOpenTwistDifference X U V u = 0 :=
  kernel.condition _

/-- The kernel satisfies the original twisted matching equality as actual sheaf morphisms. -/
theorem twoOpenTwist_matching (U V : X.Opens) (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) :
    twoOpenTwistInclusion X U V u ≫ biprod.fst ≫ openUnitRestriction X inf_le_left =
      twoOpenTwistInclusion X U V u ≫ biprod.snd ≫ openUnitRestriction X inf_le_right ≫
        overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤)) := by
  have h := twoOpenTwistInclusion_difference X U V u
  simpa only [twoOpenTwistDifference, biprod.desc_eq, Preadditive.comp_add,
    Preadditive.comp_neg, Preadditive.neg_comp, Category.assoc, add_neg_eq_zero] using h

/-- Every pair of actual sheaf morphisms satisfying the overlap equation glues into the kernel. -/
noncomputable def twoOpenTwistLift (U V : X.Opens) (u : Γ((U ⊓ V).toScheme, ⊤)ˣ)
    (N : X.Modules) (f : N ⟶ openUnitModule X U) (g : N ⟶ openUnitModule X V)
    (h : f ≫ openUnitRestriction X inf_le_left =
      g ≫ openUnitRestriction X inf_le_right ≫ overlapMultiplication X U V (u : Γ((U ⊓ V).toScheme, ⊤))) :
    N ⟶ twoOpenTwistModule X U V u :=
  kernel.lift _ (biprod.lift f g) (by
    dsimp only [twoOpenTwistDifference]
    rw [biprod.lift_desc, Preadditive.comp_neg, add_neg_eq_zero]
    exact h)

@[reassoc] theorem twoOpenTwistLift_inclusion (U V : X.Opens) (u : Γ((U ⊓ V).toScheme, ⊤)ˣ)
    (N : X.Modules) (f : N ⟶ openUnitModule X U) (g : N ⟶ openUnitModule X V) (h) :
    twoOpenTwistLift X U V u N f g h ≫ twoOpenTwistInclusion X U V u = biprod.lift f g :=
  kernel.lift_ι _ _ _

end BPFixedPoints.SheafTools
