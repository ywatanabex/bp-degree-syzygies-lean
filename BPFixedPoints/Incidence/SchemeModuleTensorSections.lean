import BPFixedPoints.Incidence.SchemeModuleTensor

/-! # Original pure sections of the actual sheaf tensor

The map is the unit of Mathlib's original module-sheafification adjunction.
It is applied to the original pointwise tensor, before any chart or state
comparison, and retains the original section restrictions.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0}) (M N : X.Modules)

/-- The original pointwise tensor maps to the actual tensor sheaf by the native adjunction unit. -/
noncomputable def moduleTensorToSheaf :
    moduleTensorPresheaf X M N ⟶ moduleCommPresheaf X (moduleTensor X M N) :=
  (moduleSheafificationAdjunction X).unit.app (moduleTensorPresheaf X M N)

/-- The native unit gives the original linear map on actual sections over every open. -/
noncomputable def moduleTensorSectionLinear (U : X.Opens) :
    TensorProduct Γ(X, U) Γ(M, U) Γ(N, U) →ₗ[Γ(X, U)] Γ(moduleTensor X M N, U) :=
  ((moduleTensorToSheaf X M N).app (op U)).hom

/-- The original pure tensor section, mapped into the actual tensor sheaf. -/
noncomputable def moduleTensorPureSection (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    Γ(moduleTensor X M N, U) :=
  moduleTensorSectionLinear X M N U (x ⊗ₜ[Γ(X, U)] y)

/-- The original section tensor is additive in its first input. -/
theorem moduleTensorPureSection_add_left (U : X.Opens) (x x' : Γ(M, U)) (y : Γ(N, U)) :
    moduleTensorPureSection X M N U (x+x') y =
      moduleTensorPureSection X M N U x y + moduleTensorPureSection X M N U x' y := by
  simp only [moduleTensorPureSection, TensorProduct.add_tmul, map_add]

/-- The original section tensor is additive in its second input. -/
theorem moduleTensorPureSection_add_right (U : X.Opens) (x : Γ(M, U)) (y y' : Γ(N, U)) :
    moduleTensorPureSection X M N U x (y+y') =
      moduleTensorPureSection X M N U x y + moduleTensorPureSection X M N U x y' := by
  simp only [moduleTensorPureSection, TensorProduct.tmul_add, map_add]

/-- The original section tensor is linear in its first input for the original structure-ring action. -/
theorem moduleTensorPureSection_smul_left (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    moduleTensorPureSection X M N U (r • x) y = r • moduleTensorPureSection X M N U x y := by
  change (moduleTensorSectionLinear X M N U) ((r • x) ⊗ₜ[Γ(X, U)] y) =
    r • (moduleTensorSectionLinear X M N U) (x ⊗ₜ[Γ(X, U)] y)
  exact (congrArg (moduleTensorSectionLinear X M N U) (TensorProduct.smul_tmul' r x y)).trans
    ((moduleTensorSectionLinear X M N U).map_smul r (x ⊗ₜ[Γ(X, U)] y))

/-- The original section tensor is linear in its second input for the original structure-ring action. -/
theorem moduleTensorPureSection_smul_right (U : X.Opens) (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) :
    moduleTensorPureSection X M N U x (r • y) = r • moduleTensorPureSection X M N U x y := by
  simp only [moduleTensorPureSection, TensorProduct.tmul_smul, map_smul]

/-- The original pure tensor sections form an actual bilinear map over each original structure ring. -/
noncomputable def moduleTensorSectionBilinear (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(moduleTensor X M N, U) :=
  (TensorProduct.mk Γ(X, U) Γ(M, U) Γ(N, U)).compr₂ (moduleTensorSectionLinear X M N U)

/-- The actual bilinear map retains precisely the original pure section construction. -/
theorem moduleTensorSectionBilinear_apply (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    moduleTensorSectionBilinear X M N U x y = moduleTensorPureSection X M N U x y := rfl

/-- Actual section restrictions retain the original pure tensor of the restricted factors. -/
theorem moduleTensorPureSection_restrict {U V : X.Opens} (i : U ⟶ V)
    (x : Γ(M, V)) (y : Γ(N, V)) :
    (moduleTensor X M N).presheaf.map i.op (moduleTensorPureSection X M N V x y) =
      moduleTensorPureSection X M N U (M.presheaf.map i.op x) (N.presheaf.map i.op y) := by
  have hn := PresheafOfModulesOfCommRing.naturality_apply (moduleTensorToSheaf X M N) i.op
    (x ⊗ₜ[Γ(X, V)] y)
  have ht := PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul
    (M₁ := moduleCommPresheaf X M) (M₂ := moduleCommPresheaf X N) i.op x y
  change (moduleTensorToSheaf X M N).app (op U)
      ((moduleTensorPresheaf X M N).map i.op (x ⊗ₜ[Γ(X, V)] y)) =
    (moduleTensor X M N).presheaf.map i.op (moduleTensorPureSection X M N V x y) at hn
  exact hn.symm.trans (congrArg (fun z => (moduleTensorToSheaf X M N).app (op U) z) ht)

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- Actual factor morphisms send original pure sections to the original pure sections of their images. -/
theorem moduleTensorPureSection_map {M M' N N' : X.Modules} (f : M ⟶ M') (g : N ⟶ N')
    (U : X.Opens) (x : Γ(M, U)) (y : Γ(N, U)) :
    (moduleTensorMap X f g).app U (moduleTensorPureSection X M N U x y) =
      moduleTensorPureSection X M' N' U (f.app U x) (g.app U y) := by
  let h : moduleTensorPresheaf X M N ⟶ moduleTensorPresheaf X M' N' :=
    (show moduleCommPresheaf X M ⟶ moduleCommPresheaf X M' from f.val) ⊗ₘ
      (show moduleCommPresheaf X N ⟶ moduleCommPresheaf X N' from g.val)
  have hn := (moduleSheafificationAdjunction X).unit.naturality h
  have hv := congrArg (fun k : moduleTensorPresheaf X M N ⟶
      moduleCommPresheaf X (moduleTensor X M' N') =>
        (k.app (op U)).hom (x ⊗ₜ[Γ(X, U)] y)) hn
  change moduleTensorPureSection X M' N' U (f.app U x) (g.app U y) =
    (moduleTensorMap X f g).app U (moduleTensorPureSection X M N U x y) at hv
  exact hv.symm

end BPFixedPoints.SheafTools
