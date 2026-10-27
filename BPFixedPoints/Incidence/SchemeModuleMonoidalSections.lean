import BPFixedPoints.Incidence.SchemeModuleMonoidalComparison

/-! # Original pure sections and the native adjoint tensorator

The tensorator of the forgetful functor is the native right-adjoint lax
monoidal structure. Thus its section map is defined by the original
adjunction, independently of any chart frame or cohomology coordinates.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- The native adjunction equips the original forgetful functor with its tensorator. -/
noncomputable instance moduleForgetLaxMonoidal :
    (Scheme.Modules.toPresheafOfModules X).LaxMonoidal :=
  (moduleSheafificationAdjunction X).rightAdjointLaxMonoidal

/-- The original pure-section morphism maps to the native adjoint tensorator. -/
theorem moduleTensorIsoMonoidal_toSheaf (M N : X.Modules) :
    moduleTensorToSheaf X M N ≫ (moduleTensorIsoMonoidal X M N).hom.val =
      LaxMonoidal.μ (Scheme.Modules.toPresheafOfModules X) M N := rfl

/-- Native coherent pure tensor sections, defined by the adjoint tensorator. -/
noncomputable def moduleMonoidalPureSection (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) : Γ(M ⊗ N, U) :=
  (LaxMonoidal.μ (Scheme.Modules.toPresheafOfModules X) M N).app (op U)
    (x ⊗ₜ[Γ(X, U)] y)

/-- The original pure sections map to the native coherent tensor sections. -/
theorem moduleTensorIsoMonoidal_pure (M N : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) :
    (moduleTensorIsoMonoidal X M N).hom.app U (moduleTensorPureSection X M N U x y) =
      moduleMonoidalPureSection X M N U x y := rfl

/-- The native associator preserves the original order of the three pure factors. -/
theorem moduleMonoidalPureSection_assoc (M N P : X.Modules) (U : X.Opens)
    (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (α_ M N P).hom.app U
      (moduleMonoidalPureSection X (M ⊗ N) P U
        (moduleMonoidalPureSection X M N U x y) z) =
      moduleMonoidalPureSection X M (N ⊗ P) U x
        (moduleMonoidalPureSection X N P U y z) := by
  have h := LaxMonoidal.associativity (Scheme.Modules.toPresheafOfModules X) M N P
  have hv := congrArg (fun k => (k.app (op U)).hom
    ((x ⊗ₜ[Γ(X, U)] y) ⊗ₜ[Γ(X, U)] z)) h
  exact hv

/-- The native section tensor preserves the original factor morphisms. -/
theorem moduleMonoidalPureSection_map {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    (f ⊗ₘ g).app U (moduleMonoidalPureSection X M N U x y) =
      moduleMonoidalPureSection X M' N' U (f.app U x) (g.app U y) := by
  have h := LaxMonoidal.μ_natural (Scheme.Modules.toPresheafOfModules X) f g
  have hv := congrArg (fun k => (k.app (op U)).hom (x ⊗ₜ[Γ(X, U)] y)) h
  exact hv.symm

end BPFixedPoints.SheafTools
