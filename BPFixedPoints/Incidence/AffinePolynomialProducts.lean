import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Original affine polynomial charts over a common coefficient scheme

The fiber-product comparison uses Mathlib's Spec tensor-product theorem and
its polynomial tensor-product equivalence. The projection formulas retain
the original coefficient and variable maps.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R] (σ τ : Type)

local instance algSpecPreservesSmallLimits :
    PreservesLimitsOfSize.{0,0} (AlgebraicGeometry.algSpec (CommRingCat.of R)) :=
  AlgebraicGeometry.preservesLimitsOfSize_algSpec

/-- The original polynomial affine scheme over its actual coefficient scheme. -/
noncomputable def polynomialOverBase : Over (Spec (CommRingCat.of R)) :=
  (AlgebraicGeometry.algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R (MvPolynomial σ R)))

/-- Mathlib's algebra-Spec functor preserves the original polynomial product. -/
noncomputable def polynomialSumOverIso :
    polynomialOverBase R (σ ⊕ τ) ≅ polynomialOverBase R σ ⨯ polynomialOverBase R τ := by
  letI : PreservesLimitsOfSize.{0,0} (AlgebraicGeometry.algSpec (CommRingCat.of R)) :=
    AlgebraicGeometry.preservesLimitsOfSize_algSpec
  exact (AlgebraicGeometry.algSpec (CommRingCat.of R)).mapIso
      (CommAlgCat.isoMk (MvPolynomial.tensorEquivSum R σ τ R)).op ≪≫
    CartesianMonoidalCategory.prodComparisonIso (AlgebraicGeometry.algSpec (CommRingCat.of R))
      (op (CommAlgCat.of R (MvPolynomial σ R))) (op (CommAlgCat.of R (MvPolynomial τ R))) ≪≫
    (CartesianMonoidalCategory.tensorLeftIsoProd (polynomialOverBase R σ)).app
      (polynomialOverBase R τ)

/-- The actual fiber product of polynomial affine charts is the polynomial
scheme on the disjoint union of their original variable sets. -/
noncomputable def polynomialFiberProductIso :
    pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial σ R))))
        (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial τ R)))) ≅
      Spec (CommRingCat.of (MvPolynomial (σ ⊕ τ) R)) :=
  pullbackSpecIso R (MvPolynomial σ R) (MvPolynomial τ R) ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.tensorEquivSum R σ τ R).toRingEquiv.toCommRingCatIso.symm.op

/-- The first actual projection is the original inclusion of the left variables. -/
@[reassoc] theorem polynomialFiberProductIso_inv_fst :
    (polynomialFiberProductIso R σ τ).inv ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (rename (R := R) (Sum.inl : σ → σ ⊕ τ)).toRingHom) := by
  dsimp only [polynomialFiberProductIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [Category.assoc, pullbackSpecIso_inv_fst, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- The second actual projection is the original inclusion of the right variables. -/
@[reassoc] theorem polynomialFiberProductIso_inv_snd :
    (polynomialFiberProductIso R σ τ).inv ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (rename (R := R) (Sum.inr : τ → σ ⊕ τ)).toRingHom) := by
  dsimp only [polynomialFiberProductIso, Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [Category.assoc, pullbackSpecIso_inv_snd, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- The product comparison over the base preserves the original left variable map. -/
@[reassoc] theorem polynomialSumOverIso_hom_fst :
    ((polynomialSumOverIso R σ τ).hom ≫ prod.fst).left =
      Spec.map (CommRingCat.ofHom (rename (R := R) (Sum.inl : σ → σ ⊕ τ)).toRingHom) := by
  have ht : ((CartesianMonoidalCategory.tensorLeftIsoProd
      (polynomialOverBase R σ)).app (polynomialOverBase R τ)).hom ≫ prod.fst =
      CartesianMonoidalCategory.fst (polynomialOverBase R σ) (polynomialOverBase R τ) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _) (limit.isLimit _) ⟨WalkingPair.left⟩
  dsimp only [polynomialOverBase] at ht
  simp only [polynomialSumOverIso, polynomialOverBase, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ht, CartesianMonoidalCategory.prodComparisonIso_hom, Over.comp_left,
    AlgebraicGeometry.prodComparison_algSpec_left]
  change (polynomialFiberProductIso R σ τ).inv ≫ pullback.fst _ _ = _
  exact polynomialFiberProductIso_inv_fst R σ τ

/-- The product comparison over the base preserves the original right variable map. -/
@[reassoc] theorem polynomialSumOverIso_hom_snd :
    ((polynomialSumOverIso R σ τ).hom ≫ prod.snd).left =
      Spec.map (CommRingCat.ofHom (rename (R := R) (Sum.inr : τ → σ ⊕ τ)).toRingHom) := by
  have ht : ((CartesianMonoidalCategory.tensorLeftIsoProd
      (polynomialOverBase R σ)).app (polynomialOverBase R τ)).hom ≫ prod.snd =
      CartesianMonoidalCategory.snd (polynomialOverBase R σ) (polynomialOverBase R τ) :=
    IsLimit.conePointUniqueUpToIso_hom_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _) (limit.isLimit _) ⟨WalkingPair.right⟩
  dsimp only [polynomialOverBase] at ht
  simp only [polynomialSumOverIso, polynomialOverBase, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, ht, CartesianMonoidalCategory.prodComparisonIso_hom, Over.comp_left,
    AlgebraicGeometry.prodComparison_algSpec_left]
  change (polynomialFiberProductIso R σ τ).inv ≫ pullback.snd _ _ = _
  exact polynomialFiberProductIso_inv_snd R σ τ

end BPFixedPoints.SchemeTools
