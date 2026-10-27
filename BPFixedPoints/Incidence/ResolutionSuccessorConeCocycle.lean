import BPFixedPoints.Incidence.ResolutionFirstConeLift

/-! # Original successive syzygy coefficients in Mathlib's native cone

Mathlib's existing `liftCocycle` constructs the degree-n cone cocycle.
Its two components are the original degree-n term and the next syzygy
projection, with the sign forced by the native Hom differential.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
attribute [local instance] Abelian.hasFiniteBiproducts
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ) (S : ShortComplex C) (n : ℤ)
variable (u : K.X (-(n+1)) ⟶ S.X₁) (hu : K.d (-(n+2)) (-(n+1)) ≫ u=0)
variable (v : K.X (-n) ⟶ S.X₂) (huv : K.d (-(n+1)) (-n) ≫ v=u ≫ S.f)

/-- The original next syzygy cocycle, with the coefficient required by the native cone equation. -/
def successorConeFirst : Cocycle K ((CochainComplex.singleFunctor C 0).obj S.X₁) (n+1) :=
  n.negOnePow • Cocycle.toSingleMk u (by omega : -(n+1)+(n+1)=0) (-(n+2)) (by omega) hu

/-- The original degree-n term, as a native Hom cochain. -/
def successorConeSecond : Cochain K ((CochainComplex.singleFunctor C 0).obj S.X₂) n :=
  Cochain.toSingleMk v (by omega : -n+n=0)

include huv in
/-- The actual factorization of the original differential satisfies Mathlib's cone equation in every degree. -/
theorem successorCone_equation :
    δ n (n+1) (successorConeSecond K S n v) + (successorConeFirst K S n u hu).val.comp
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.f)) (add_zero (n+1))=0 := by
  change δ n (n+1) (Cochain.toSingleMk v (by omega : -n+n=0)) +
    (n.negOnePow • Cochain.toSingleMk u (by omega : -(n+1)+(n+1)=0)).comp
      (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.f)) (add_zero (n+1))=0
  rw [Cochain.δ_toSingleMk v (by omega : -n+n=0) (n+1) (-(n+1)) (by omega),
    Cochain.units_smul_comp,← Cochain.toSingleMk_postcomp,huv,Int.negOnePow_succ,
    Units.neg_smul]
  exact neg_add_cancel _

/-- The specified native degree-n cone cocycle uses the original two coefficients. -/
def successorConeCocycle :
    Cocycle K (CochainComplex.mappingCone ((CochainComplex.singleFunctor C 0).map S.f)) n :=
  CochainComplex.mappingCone.liftCocycle _ (successorConeFirst K S n u hu)
    (successorConeSecond K S n v) rfl (successorCone_equation K S n u hu v huv)

/-- The native cone augmentation is precisely the original quotient coefficient, in every degree. -/
theorem successorConeCocycle_augmentation :
    (successorConeCocycle K S n u hu v huv).val.comp
      (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex
        (S.map (CochainComplex.singleFunctor C 0)))) (add_zero n) =
      Cochain.toSingleMk (v ≫ S.g) (by omega : -n+n=0) := by
  change (CochainComplex.mappingCone.liftCochain _
    (successorConeFirst K S n u hu).val (successorConeSecond K S n v) rfl).comp _ _ = _
  rw [CochainComplex.mappingCone.descShortComplex,CochainComplex.mappingCone.ofHom_desc]
  change (CochainComplex.mappingCone.liftCochain ((CochainComplex.singleFunctor C 0).map S.f)
    (successorConeFirst K S n u hu).val (successorConeSecond K S n v) rfl).comp
      (CochainComplex.mappingCone.descCochain ((CochainComplex.singleFunctor C 0).map S.f)
        0 (Cochain.ofHom ((CochainComplex.singleFunctor C 0).map S.g)) (neg_add_cancel 1)) (add_zero n) = _
  rw [CochainComplex.mappingCone.liftCochain_descCochain]
  simp only [Cochain.comp_zero,zero_add]
  exact (Cochain.toSingleMk_postcomp v (by omega : -n+n=0) S.g).symm

/-- The negative cone projection has exactly the successor sign on the original next syzygy coefficient. -/
theorem successorConeCocycle_negativeProjection :
    (successorConeCocycle K S n u hu v huv).val.comp
      (-(CochainComplex.mappingCone.fst ((CochainComplex.singleFunctor C 0).map S.f)).val) rfl =
      (n+1).negOnePow • Cochain.toSingleMk u (by omega : -(n+1)+(n+1)=0) := by
  change (CochainComplex.mappingCone.liftCochain _
    (successorConeFirst K S n u hu).val (successorConeSecond K S n v) rfl).comp _ _ = _
  rw [Cochain.comp_neg,CochainComplex.mappingCone.liftCochain_fst]
  simp only [successorConeFirst,
    Int.negOnePow_succ,Units.neg_smul]
  rfl

end
end BPFixedPoints.ExtResolutionTools
