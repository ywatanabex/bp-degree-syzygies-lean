import BPFixedPoints.Incidence.SchemeModulePullbackFrames
import BPFixedPoints.Incidence.TwoOpenTwistSheaf

/-! # Pullback preserves the original geometric scalar frame transitions

The original scheme modules, structure-ring maps and native comparisons are used.
Comparison with the coefficient face atlas and derived cohomology is separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable {X Y : Scheme.{0}}

/-- The native structure-module pullback preserves multiplication by the original geometric global function. -/
theorem modulePullbackUnitIso_multiplication (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.pullback f).map (unitGlobalMultiplication Y r) ≫ (modulePullbackUnitIso f).hom =
      (modulePullbackUnitIso f).hom ≫ unitGlobalMultiplication X (f.appTop r) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    modulePullbackUnitIso_adjunction]
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Γ(Y, U.unop) at x
  change (f.app U.unop).hom
    (x * Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) =
      (f.app U.unop).hom x *
        X.presheaf.map (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op (f.appTop r)
  rw [map_mul]
  congr 1
  exact congrArg (fun k => k.hom r) (f.c.naturality (homOfLE (show U.unop ≤ ⊤ from le_top)).op)

/-- Pulling back the original local frame transition pulls back its original scalar function. -/
theorem modulePullbackLocalUnitIso_transition (f : X ⟶ Y) (U : Y.Opens)
    (M : Y.Modules) (e d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (g : X ⟶ U) (hg : g ≫ U.ι = f) (r : Γ(U.toScheme, ⊤))
    (h : e.hom = d.hom ≫ unitGlobalMultiplication U.toScheme r) :
    (modulePullbackLocalUnitIso f U M e g hg).hom =
      (modulePullbackLocalUnitIso f U M d g hg).hom ≫
        unitGlobalMultiplication X (g.appTop r) := by
  dsimp only [modulePullbackLocalUnitIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [h, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [modulePullbackUnitIso_multiplication]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end BPFixedPoints.SheafTools
