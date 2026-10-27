import BPFixedPoints.Incidence.TwoOpenTwistLocallyFree

/-! # Original geometric functions and frame transitions on the native over-site

The original scheme modules, structure-ring maps and native comparisons are used.
Comparison with the coefficient face atlas and derived cohomology is separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0}) (U : X.Opens)

/-- The original geometric multiplication transported by the native fully faithful over-site equivalence. -/
noncomputable def moduleOverMultiplication (r : Γ(U.toScheme, ⊤)) :
    SheafOfModules.unit (X.ringCatSheaf.over U) ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  (Scheme.Modules.overEquiv U).fullyFaithfulFunctor.preimage
    ((U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ unitGlobalMultiplication U.toScheme r ≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).inv)

/-- The original local-frame transition induces the same actual over-site transition. -/
theorem moduleOverUnitIso_transition (M : X.Modules)
    (e d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (r : Γ(U.toScheme, ⊤)) (h : e.hom = d.hom ≫ unitGlobalMultiplication U.toScheme r) :
    (moduleOverUnitIso X M U e).hom =
      (moduleOverUnitIso X M U d).hom ≫ moduleOverMultiplication X U r := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [moduleOverUnitIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, CategoryTheory.Functor.map_comp,
    moduleOverMultiplication, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The native over-site retains multiplication of the original geometric scalar functions. -/
theorem moduleOverMultiplication_mul (r s : Γ(U.toScheme, ⊤)) :
    moduleOverMultiplication X U r ≫ moduleOverMultiplication X U s =
      moduleOverMultiplication X U (r*s) := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [moduleOverMultiplication, CategoryTheory.Functor.map_comp,
    Functor.FullyFaithful.map_preimage, ← unitGlobalMultiplication_mul,
    Category.assoc, Iso.inv_hom_id_assoc]

/-- The original constant one induces the identity over-site morphism. -/
theorem moduleOverMultiplication_one : moduleOverMultiplication X U 1 = 𝟙 _ := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  rw [CategoryTheory.Functor.map_id]
  rw [moduleOverMultiplication, Functor.FullyFaithful.map_preimage]
  change (𝟙 _ ≫ unitGlobalMultiplication U.toScheme 1 ≫ 𝟙 _) = 𝟙 _
  rw [Category.id_comp, Category.comp_id, unitGlobalMultiplication_one]

/-- The actual over-site coefficient of the original geometric multiplication on a subopen. -/
noncomputable def moduleOverMultiplicationCoefficient (r : Γ(U.toScheme, ⊤)) (S : Over U) :
    Γ(X, S.left) :=
  ((moduleOverMultiplication X U r).val.app (op S)).hom (1 : Γ(X, S.left))

/-- The original over-site structure-module endomorphism acts by its actual coefficient. -/
theorem moduleOverMultiplication_app (r : Γ(U.toScheme, ⊤)) (S : Over U) (x : Γ(X, S.left)) :
    (show Γ(X, S.left) from ((moduleOverMultiplication X U r).val.app (op S)).hom x) =
      x * moduleOverMultiplicationCoefficient X U r S := by
  have h := ((moduleOverMultiplication X U r).val.app (op S)).hom.map_smul x
    (1 : Γ(X, S.left))
  change (show Γ(X, S.left) from ((moduleOverMultiplication X U r).val.app (op S)).hom
    (x*1 : Γ(X, S.left))) =
    x * moduleOverMultiplicationCoefficient X U r S at h
  simpa only [mul_one] using h

/-- The actual coefficients preserve the original multiplication. -/
theorem moduleOverMultiplicationCoefficient_mul (r s : Γ(U.toScheme, ⊤)) (S : Over U) :
    moduleOverMultiplicationCoefficient X U (r*s) S =
      moduleOverMultiplicationCoefficient X U r S * moduleOverMultiplicationCoefficient X U s S := by
  have h := congrArg (fun f => (f.val.app (op S)).hom (1 : Γ(X, S.left)))
    (moduleOverMultiplication_mul X U r s)
  change ((moduleOverMultiplication X U s).val.app (op S)).hom
    (moduleOverMultiplicationCoefficient X U r S) = moduleOverMultiplicationCoefficient X U (r*s) S at h
  exact h.symm.trans (moduleOverMultiplication_app X U s S _)

/-- The original unit coefficient is one on every subopen. -/
theorem moduleOverMultiplicationCoefficient_one (S : Over U) :
    moduleOverMultiplicationCoefficient X U 1 S = 1 :=
  congrArg (fun f => (f.val.app (op S)).hom (1 : Γ(X, S.left))) (moduleOverMultiplication_one X U)

/-- All finite products of original functions retain their actual coefficients. -/
theorem moduleOverMultiplicationCoefficient_prod {I : Type*} (s : Finset I)
    (r : I → Γ(U.toScheme, ⊤)) (S : Over U) :
    moduleOverMultiplicationCoefficient X U (∏ i ∈ s, r i) S =
      ∏ i ∈ s, moduleOverMultiplicationCoefficient X U (r i) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using moduleOverMultiplicationCoefficient_one X U S
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, moduleOverMultiplicationCoefficient_mul, ih]

/-- The original geometric frame transition retains its coefficients on every native subopen. -/
theorem moduleOverUnitIso_transition_coefficients (M : X.Modules)
    (e d : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (r : Γ(U.toScheme, ⊤)) (h : e.hom = d.hom ≫ unitGlobalMultiplication U.toScheme r)
    (S : Over U) (x : (M.over U).val.obj (op S)) :
    (show Γ(X, S.left) from ((moduleOverUnitIso X M U e).hom.val.app (op S)).hom x) =
      (show Γ(X, S.left) from ((moduleOverUnitIso X M U d).hom.val.app (op S)).hom x) *
        moduleOverMultiplicationCoefficient X U r S := by
  have hh := congrArg (fun f => (f.val.app (op S)).hom x)
    (moduleOverUnitIso_transition X U M e d r h)
  exact hh.trans (moduleOverMultiplication_app X U r S _)

/-- The over-site multiplication returns the original geometric multiplication. -/
theorem moduleOverMultiplication_map (r : Γ(U.toScheme, ⊤)) :
    (Scheme.Modules.overEquiv U).functor.map (moduleOverMultiplication X U r) ≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
        (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫ unitGlobalMultiplication U.toScheme r := by
  rw [moduleOverMultiplication, Functor.FullyFaithful.map_preimage]
  change (𝟙 _ ≫ unitGlobalMultiplication U.toScheme r ≫ 𝟙 _) ≫ 𝟙 _ =
    𝟙 _ ≫ unitGlobalMultiplication U.toScheme r
  simp only [Category.id_comp, Category.comp_id]

end BPFixedPoints.SheafTools
