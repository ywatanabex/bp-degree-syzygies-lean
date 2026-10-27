import BPFixedPoints.Incidence.AffineInjectiveFlasque
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Module.LocalizedModule.Exact

/-! # Original tilde stalks and native module localizations

The actual abelian stalk is compared with the stalk of the original
constant-base module presheaf by the native filtered-colimit comparison.
The original module maps and germs are retained throughout.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u
variable (R : CommRingCat.{u})

/-- The original tilde construction followed by forgetting only the module action. -/
noncomputable def affineTildeAbelianFunctor :
    ModuleCat.{u} R ⥤ Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u} :=
  tilde.functor R ⋙ SheafOfModules.toSheaf (Spec R).ringCatSheaf

/-- The original constant-base module presheaf map of the actual tilde morphism. -/
noncomputable def affineTildeModulePresheafMap {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    structurePresheafInModuleCat R M ⟶ structurePresheafInModuleCat R N where
  app U := ModuleCat.ofHom (StructureSheaf.comapₗ f.hom U.unop U.unop .rfl)
  naturality _ _ _ := by ext s; rfl

/-- The actual abelian section map is the original pointwise localized module map. -/
theorem affineTildeAbelianFunctor_map_app {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (U : (Spec R).Opens) (s : (structurePresheafInModuleCat R M).obj (op U)) :
    ((affineTildeAbelianFunctor R).map f).hom.app (op U) s =
      (affineTildeModulePresheafMap R f).app (op U) s := rfl

/-- The actual structure-ring germ of an original coefficient is its original stalk coefficient. -/
theorem affineCoefficient_germ (U : (Spec R).Opens) (p : PrimeSpectrum.Top R) (hp : p ∈ U) (r : R) :
    (structurePresheafInCommRingCat R).germ U p hp
      (StructureSheaf.toOpenₗ R R U r) =
        StructureSheaf.toStalk R p r := by
  dsimp only [StructureSheaf.toStalk]
  rw [← (structurePresheafInCommRingCat R).germ_res (homOfLE (show U ≤ ⊤ from le_top)) p hp]
  rfl

/-- Actual tilde germs are linear for the original base-ring action. -/
noncomputable def affineTildeGermLinear (M : ModuleCat.{u} R) (U : (Spec R).Opens)
    (p : PrimeSpectrum.Top R) (hp : p ∈ U) :
    (structurePresheafInModuleCat R M).obj (op U) →ₗ[R]
      ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p) where
  __ := (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U p hp).hom
  map_smul' r s := by
    change _ = StructureSheaf.toStalk R p r •
      TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U p hp s
    rw [← affineCoefficient_germ R U p hp r]
    refine Eq.trans ?_ (PresheafOfModules.germ_smul (moduleStructurePresheaf R M) p U hp
      (StructureSheaf.toOpenₗ R R U r) s)
    congr 1
    let s₀ : (structureSheafInType R M).obj.obj (op U) := s
    have h : r • s₀ =
        (algebraMap R ((structureSheafInType R R).obj.obj (op U)) r) • s₀ :=
      (IsScalarTower.algebraMap_smul ((structureSheafInType R R).obj.obj (op U)) r s₀).symm
    exact h

/-- The original module-valued stalk cocone after the native forgetful functor. -/
noncomputable def affineTildeStalkForgetCocone (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R) :
    ColimitCocone (((OpenNhds.inclusion (X := PrimeSpectrum.Top R) p).op ⋙ structurePresheafInModuleCat R M) ⋙
      forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  ⟨(forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapCocone
    (colimit.cocone ((OpenNhds.inclusion (X := PrimeSpectrum.Top R) p).op ⋙ structurePresheafInModuleCat R M)),
    isColimitOfPreserves (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
      (colimit.isColimit ((OpenNhds.inclusion (X := PrimeSpectrum.Top R) p).op ⋙ structurePresheafInModuleCat R M))⟩

/-- Forgetting the original module action commutes with the actual stalk colimit. -/
noncomputable def affineTildeStalkForgetIso (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R) :
    TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p ≅
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj
        ((structurePresheafInModuleCat R M).stalk p) :=
  colimit.isoColimitCocone (affineTildeStalkForgetCocone R M p)

/-- The categorical comparison retains every original germ. -/
theorem affineTildeStalkForgetIso_germ (M : ModuleCat.{u} R) (U : (Spec R).Opens)
    (p : PrimeSpectrum.Top R) (hp : p ∈ U)
    (s : (structurePresheafInModuleCat R M).obj (op U)) :
    (affineTildeStalkForgetIso R M p).hom
        (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U p hp s) =
      (structurePresheafInModuleCat R M).germ U p hp s :=
  ConcreteCategory.congr_hom (colimit.isoColimitCocone_ι_hom
    (affineTildeStalkForgetCocone R M p) (op (⟨U, hp⟩ : OpenNhds (X := PrimeSpectrum.Top R) p))) s

/-- The native filtered-colimit comparison between the actual abelian and original module stalks. -/
noncomputable def affineTildeModuleStalkIso (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R) :
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p) ≃ₗ[R]
      (structurePresheafInModuleCat R M).stalk p where
  __ := (affineTildeStalkForgetIso R M p).addCommGroupIsoToAddEquiv
  map_smul' r x := by
    obtain ⟨U, hp, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
      (moduleStructurePresheaf R M).presheaf x
    let sR : (structurePresheafInModuleCat R M).obj (op U) := s
    have hg (t : (structurePresheafInModuleCat R M).obj (op U)) :
        (show (structurePresheafInModuleCat R M).stalk p from
          (affineTildeStalkForgetIso R M p).hom (affineTildeGermLinear R M U p hp t)) =
        (structurePresheafInModuleCat R M).germ U p hp t :=
      affineTildeStalkForgetIso_germ R M U p hp t
    change (show (structurePresheafInModuleCat R M).stalk p from
        (affineTildeStalkForgetIso R M p).hom (r • affineTildeGermLinear R M U p hp sR)) =
      r • (show (structurePresheafInModuleCat R M).stalk p from
        (affineTildeStalkForgetIso R M p).hom (affineTildeGermLinear R M U p hp sR))
    rw [← (affineTildeGermLinear R M U p hp).map_smul r sR, hg, hg]
    exact ((structurePresheafInModuleCat R M).germ U p hp).hom.map_smul r sR

/-- The linear stalk comparison preserves every original germ. -/
theorem affineTildeModuleStalkIso_germ (M : ModuleCat.{u} R) (U : (Spec R).Opens)
    (p : PrimeSpectrum.Top R) (hp : p ∈ U)
    (s : (structurePresheafInModuleCat R M).obj (op U)) :
    affineTildeModuleStalkIso R M p
        (TopCat.Presheaf.germ (moduleStructurePresheaf R M).presheaf U p hp s) =
      (structurePresheafInModuleCat R M).germ U p hp s :=
  affineTildeStalkForgetIso_germ R M U p hp s

/-- The original coefficient module mapped into its original module-valued stalk. -/
noncomputable def affineTildeModuleToStalk (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R) :
    M ⟶ (structurePresheafInModuleCat R M).stalk p :=
  ModuleCat.ofHom (StructureSheaf.toOpenₗ R M ⊤) ≫
    (structurePresheafInModuleCat R M).germ ⊤ p trivial

/-- This original module-valued stalk map is the native localization at the original prime. -/
instance affineTildeModuleToStalk_isLocalized (M : ModuleCat.{u} R) (p : PrimeSpectrum.Top R) :
    IsLocalizedModule p.asIdeal.primeCompl (affineTildeModuleToStalk R M p).hom := by
  have h : (affineTildeModuleStalkIso R M p).toLinearMap.comp (tilde.toStalk M p).hom =
      (affineTildeModuleToStalk R M p).hom := by
    ext x
    exact affineTildeModuleStalkIso_germ R M ⊤ p trivial (StructureSheaf.toOpenₗ R M ⊤ x)
  rw [← h]
  exact IsLocalizedModule.of_linearEquiv p.asIdeal.primeCompl (tilde.toStalk M p).hom
    (affineTildeModuleStalkIso R M p)

/-- The actual module-valued stalk map of the original tilde morphism. -/
noncomputable def affineTildeModuleStalkMap {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (p : PrimeSpectrum.Top R) :
    (structurePresheafInModuleCat R M).stalk p ⟶ (structurePresheafInModuleCat R N).stalk p :=
  (stalkFunctor (ModuleCat.{u} R) p).map (affineTildeModulePresheafMap R f)

/-- The original maps from coefficient modules to stalks commute with the original morphism. -/
@[reassoc] theorem affineTildeModuleToStalk_naturality {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (p : PrimeSpectrum.Top R) :
    affineTildeModuleToStalk R M p ≫ affineTildeModuleStalkMap R f p =
      f ≫ affineTildeModuleToStalk R N p := by
  ext x
  have ht := ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x
  simp only [ConcreteCategory.comp_apply] at ht
  dsimp only [affineTildeModuleToStalk, affineTildeModuleStalkMap]
  simp only [ConcreteCategory.comp_apply]
  erw [stalkFunctor_map_germ_apply]
  exact congrArg (fun s => (structurePresheafInModuleCat R N).germ ⊤ p trivial s) ht

/-- The original stalk morphism is the native map between the original localizations. -/
theorem affineTildeModuleStalkMap_eq_localized {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (p : PrimeSpectrum.Top R) :
    (affineTildeModuleStalkMap R f p).hom = IsLocalizedModule.map p.asIdeal.primeCompl
      (affineTildeModuleToStalk R M p).hom (affineTildeModuleToStalk R N p).hom f.hom := by
  apply IsLocalizedModule.linearMap_ext p.asIdeal.primeCompl
    (affineTildeModuleToStalk R M p).hom (affineTildeModuleToStalk R N p).hom
  ext x
  have hn := ConcreteCategory.congr_hom (affineTildeModuleToStalk_naturality R f p) x
  simp only [ConcreteCategory.comp_apply] at hn
  exact hn.trans (IsLocalizedModule.map_apply p.asIdeal.primeCompl
    (affineTildeModuleToStalk R M p).hom (affineTildeModuleToStalk R N p).hom f.hom x).symm

/-- The original abelian and module stalk comparisons preserve the actual stalk maps. -/
theorem affineTildeModuleStalkIso_naturality {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (p : PrimeSpectrum.Top R)
    (x : ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p)) :
    affineTildeModuleStalkIso R N p
        ((stalkFunctor AddCommGrpCat.{u} p).map ((affineTildeAbelianFunctor R).map f).hom x) =
      affineTildeModuleStalkMap R f p (affineTildeModuleStalkIso R M p x) := by
  obtain ⟨U, hp, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
    (moduleStructurePresheaf R M).presheaf x
  dsimp only [affineTildeModuleStalkMap]
  erw [stalkFunctor_map_germ_apply, affineTildeModuleStalkIso_germ,
    affineTildeModuleStalkIso_germ, stalkFunctor_map_germ_apply]
  rfl

end BPFixedPoints.SheafTools
