import BPFixedPoints.Incidence.SchemeModuleTensorLocalFrames
import BPFixedPoints.Incidence.SchemeModuleFrameScalars

/-! # Actual tensor section equivalences and original finite frame transitions

The original scheme modules, structure-ring maps and native comparisons are used.
Comparison with the coefficient face atlas and derived cohomology is separate.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- On a common rank-one chart the original pointwise tensor maps isomorphically to the actual tensor sections. -/
noncomputable def moduleTensorSectionEquivOfFrames (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (S : Over U) :
    TensorProduct Γ(X, S.left) Γ(M, S.left) Γ(N, S.left) ≃ₗ[Γ(X, S.left)]
      Γ(moduleTensor X M N, S.left) :=
  CategoryTheory.Iso.toLinearEquiv ((PresheafOfModules.evaluation _ (Opposite.op S)).mapIso
    ((SheafOfModules.forget _).mapIso
      (moduleSheafificationOverIso X (moduleTensorPresheaf X M N) U
        (moduleTensorPresheafOver_isSheaf X M N U eM eN)).symm))

/-- This local equivalence is the original sheafification-unit section map. -/
theorem moduleTensorSectionEquivOfFrames_eq (M N : X.Modules) (U : X.Opens)
    (eM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) (S : Over U)
    (z : TensorProduct Γ(X, S.left) Γ(M, S.left) Γ(N, S.left)) :
    moduleTensorSectionEquivOfFrames X M N U eM eN S z =
      moduleTensorSectionLinear X M N S.left z := by
  have h := moduleSheafificationOverIso_unit X (moduleTensorPresheaf X M N) U
    (moduleTensorPresheafOver_isSheaf X M N U eM eN)
  have hv := congrArg (fun k => (k.app (Opposite.op S)).hom z) h
  let e := CategoryTheory.Iso.toLinearEquiv ((PresheafOfModules.evaluation _ (Opposite.op S)).mapIso
    ((SheafOfModules.forget _).mapIso
      (moduleSheafificationOverIso X (moduleTensorPresheaf X M N) U
        (moduleTensorPresheafOver_isSheaf X M N U eM eN))))
  change e.symm z = moduleTensorSectionLinear X M N S.left z
  apply e.injective
  change e (moduleTensorSectionLinear X M N S.left z) = z at hv
  exact (e.apply_symm_apply z).trans hv.symm

/-- On arbitrary actual tensor sections the two factor transitions multiply. -/
theorem moduleTensorOverUnitIso_change (M N : X.Modules) (U : X.Opens)
    (eM fM : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (eN fN : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (S : Over U) (r s : Γ(X, S.left))
    (hM : ∀ x, (show Γ(X, S.left) from (eM.hom.val.app (Opposite.op S)).hom x) =
      (show Γ(X, S.left) from (fM.hom.val.app (Opposite.op S)).hom x) * r)
    (hN : ∀ y, (show Γ(X, S.left) from (eN.hom.val.app (Opposite.op S)).hom y) =
      (show Γ(X, S.left) from (fN.hom.val.app (Opposite.op S)).hom y) * s)
    (z : Γ(moduleTensor X M N, S.left)) :
    (show Γ(X, S.left) from
      ((moduleTensorOverUnitIso X M N U eM eN).hom.val.app (Opposite.op S)).hom z) =
      (show Γ(X, S.left) from
        ((moduleTensorOverUnitIso X M N U fM fN).hom.val.app (Opposite.op S)).hom z) * (r*s) := by
  obtain ⟨t, rfl⟩ := (moduleTensorSectionEquivOfFrames X M N U eM eN S).surjective z
  rw [moduleTensorSectionEquivOfFrames_eq]
  induction t using TensorProduct.inductionOn with
  | tmul x y =>
      change ((moduleTensorOverUnitIso X M N U eM eN).hom.val.app (Opposite.op S)).hom
        (moduleTensorPureSection X M N S.left x y) =
          (show Γ(X, S.left) from
            ((moduleTensorOverUnitIso X M N U fM fN).hom.val.app (Opposite.op S)).hom
              (moduleTensorPureSection X M N S.left x y)) * (r*s)
      rw [moduleTensorOverUnitIso_pure, moduleTensorOverUnitIso_pure, hM, hN]
      ac_rfl
  | add x y hx hy =>
      simpa only [map_add, add_mul] using congrArg₂ (fun a b : Γ(X, S.left) => a+b) hx hy

/-- The transition on arbitrary finite actual tensor sections is the product of all original factor coefficients. -/
theorem moduleTensorFamilyOverUnitIso_change (U : X.Opens) (n : ℕ) :
    ∀ (M : Fin n → X.Modules)
    (e f : ∀ i, (M i).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (S : Over U) (t : Fin n → Γ(X, S.left))
    (_ : ∀ i x, (show Γ(X, S.left) from ((e i).hom.val.app (Opposite.op S)).hom x) =
      (show Γ(X, S.left) from ((f i).hom.val.app (Opposite.op S)).hom x) * t i)
    (z : Γ(moduleTensorFamily X n M, S.left)),
    (show Γ(X, S.left) from
      ((moduleTensorFamilyOverUnitIso X U n M e).hom.val.app (Opposite.op S)).hom z) =
      (show Γ(X, S.left) from
        ((moduleTensorFamilyOverUnitIso X U n M f).hom.val.app (Opposite.op S)).hom z) * ∏ i, t i := by
  induction n with
  | zero => intro M e f S t h z; simp; rfl
  | succ n ih =>
      intro M e f S t h z
      have ht := moduleTensorOverUnitIso_change X _ _ U (e 0) (f 0)
        (moduleTensorFamilyOverUnitIso X U n (fun i => M i.succ) (fun i => e i.succ))
        (moduleTensorFamilyOverUnitIso X U n (fun i => M i.succ) (fun i => f i.succ))
        S (t 0) (∏ i : Fin n, t i.succ) (h 0)
        (ih (fun i => M i.succ) (fun i => e i.succ) (fun i => f i.succ) S (fun i => t i.succ)
          (fun i => h i.succ)) z
      rw [Fin.prod_univ_succ]
      exact ht

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (X : Scheme.{0}) (U : X.Opens)

/-- Original geometric factor transitions induce the product transition on the actual over-site finite tensor. -/
theorem moduleTensorFamilyOverUnitIso_transition (n : ℕ) (M : Fin n → X.Modules)
    (e f : ∀ i, (M i).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (r : Fin n → Γ(U.toScheme, ⊤))
    (h : ∀ i, (e i).hom = (f i).hom ≫ unitGlobalMultiplication U.toScheme (r i)) :
    (moduleTensorFamilyOverUnitIso X U n M (fun i => moduleOverUnitIso X (M i) U (e i))).hom =
      (moduleTensorFamilyOverUnitIso X U n M (fun i => moduleOverUnitIso X (M i) U (f i))).hom ≫
        moduleOverMultiplication X U (∏ i, r i) := by
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have ht := moduleTensorFamilyOverUnitIso_change X U n M
    (fun i => moduleOverUnitIso X (M i) U (e i)) (fun i => moduleOverUnitIso X (M i) U (f i))
    S.unop (fun i => moduleOverMultiplicationCoefficient X U (r i) S.unop)
    (fun i => moduleOverUnitIso_transition_coefficients X U (M i) (e i) (f i) (r i) (h i) S.unop) z
  have hp := congrArg (fun t : Γ(X, S.unop.left) =>
    (show Γ(X, S.unop.left) from
      ((moduleTensorFamilyOverUnitIso X U n M
        (fun i => moduleOverUnitIso X (M i) U (f i))).hom.val.app S).hom z) * t)
    (moduleOverMultiplicationCoefficient_prod X U Finset.univ r S.unop)
  exact ht.trans (hp.symm.trans (moduleOverMultiplication_app X U (∏ i, r i) S.unop _).symm)

/-- The actual geometric finite tensor frames differ by multiplication by the product of the original functions. -/
theorem moduleTensorFamilyLocalUnitIso_transition (n : ℕ) (M : Fin n → X.Modules)
    (e f : ∀ i, (M i).restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    (r : Fin n → Γ(U.toScheme, ⊤))
    (h : ∀ i, (e i).hom = (f i).hom ≫ unitGlobalMultiplication U.toScheme (r i)) :
    (moduleTensorFamilyLocalUnitIso X U n M e).hom =
      (moduleTensorFamilyLocalUnitIso X U n M f).hom ≫ unitGlobalMultiplication U.toScheme (∏ i, r i) := by
  dsimp only [moduleTensorFamilyLocalUnitIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [moduleTensorFamilyOverUnitIso_transition X U n M e f r h,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [moduleOverMultiplication_map]

end BPFixedPoints.SheafTools
