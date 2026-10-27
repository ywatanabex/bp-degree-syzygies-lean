import BPFixedPoints.Incidence.TwoOpenTwistLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Native local freeness of the actual twisted gluing sheaf

The explicit rank-one chart isomorphisms give Mathlib's local free-generator
data. The covering condition is used, rather than assumed implicitly.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false

universe u
variable (X : Scheme.{u})

/-- A geometric open restriction trivialization gives the corresponding native over-site trivialization. -/
noncomputable def moduleOverUnitIso (M : X.Modules) (S : X.Opens)
    (e : M.restrict S.ι ≅ SheafOfModules.unit S.toScheme.ringCatSheaf) :
    M.over S ≅ SheafOfModules.unit (X.ringCatSheaf.over S) :=
  (Scheme.Modules.overEquiv S).fullyFaithfulFunctor.preimageIso
    ((Scheme.Modules.overFunctorEquiv S).app M ≪≫ e ≪≫
      (S.sheafOfModulesEquivOverUnit X.ringCatSheaf).symm)

/-- An actual local unit trivialization supplies a single native free generator. -/
noncomputable def localUnitGeneratingSections (M : X.Modules) (S : X.Opens)
    (e : M.restrict S.ι ≅ SheafOfModules.unit S.toScheme.ringCatSheaf) :
    (M.over S).GeneratingSections :=
  (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over S) PUnit.{u+1}).ofEpi
    ((coproductUniqueIso (fun _ : PUnit.{u+1} =>
      SheafOfModules.unit (X.ringCatSheaf.over S))).hom ≫ (moduleOverUnitIso X M S e).inv)

/-- The actual one-generator presentation associated with a local trivialization is an isomorphism. -/
instance localUnitGeneratingSections_isIso (M : X.Modules) (S : X.Opens)
    (e : M.restrict S.ι ≅ SheafOfModules.unit S.toScheme.ringCatSheaf) :
    IsIso (localUnitGeneratingSections X M S e).π := by
  rw [localUnitGeneratingSections, SheafOfModules.GeneratingSections.ofEpi_π,
    SheafOfModules.free.generatingSections_π]
  infer_instance

/-- A genuine two-open cover is a cover of the terminal object of the native site. -/
theorem twoOpen_coversTop (U V : X.Opens) (hUV : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology X).CoversTop (fun b : Bool => if b then V else U) := by
  intro W x hx
  have hxUV : x ∈ U ⊔ V := by rw [hUV]; trivial
  rcases hxUV with hxU | hxV
  · refine ⟨W ⊓ U, homOfLE inf_le_left, ?_, hx, hxU⟩
    exact ⟨false, ⟨homOfLE inf_le_right⟩⟩
  · refine ⟨W ⊓ V, homOfLE inf_le_left, ?_, hx, hxV⟩
    exact ⟨true, ⟨homOfLE inf_le_right⟩⟩

/-- Native local free-generator data for the actual twisted gluing sheaf on a genuine cover. -/
noncomputable def twoOpenTwistLocalGenerators (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (hUV : U ⊔ V = ⊤) :
    (twoOpenTwistModule X U V u).LocalGeneratorsData where
  I := Bool
  X b := if b then V else U
  coversTop := twoOpen_coversTop X U V hUV
  generators b := by
    cases b
    · exact localUnitGeneratingSections X _ U (twoOpenTwistLeftIso X U V u)
    · exact localUnitGeneratingSections X _ V (twoOpenTwistRightIso X U V u)

/-- Both single-generator presentations of the original twisted sheaf are actual isomorphisms. -/
instance twoOpenTwistLocalGenerators_isLocallyFreeData (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (hUV : U ⊔ V = ⊤) :
    (twoOpenTwistLocalGenerators X U V u hUV).IsLocallyFreeData where
  isIso b := by cases b <;> exact localUnitGeneratingSections_isIso X _ _ _

/-- The actual twisted gluing sheaf is locally free in Mathlib's native sense on a genuine two-open cover. -/
theorem twoOpenTwist_isLocallyFree (U V : X.Opens)
    (u : Γ((U ⊓ V).toScheme, ⊤)ˣ) (hUV : U ⊔ V = ⊤) :
    (twoOpenTwistModule X U V u).IsLocallyFree :=
  (twoOpenTwistLocalGenerators X U V u hUV).isLocallyFree

end BPFixedPoints.SheafTools
