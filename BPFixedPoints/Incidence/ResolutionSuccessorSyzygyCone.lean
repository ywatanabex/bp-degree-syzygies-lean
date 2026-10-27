import BPFixedPoints.Incidence.ResolutionSuccessorConeCocycle

/-! # The original differential cokernel tower supplies every successor cone lift

The coefficients below are the native extension isomorphisms followed by
the original syzygy projections. No cohomology coordinates are used.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ) (hP : ∀ n, P.ExactAt (n+1)) (n : ℕ)

/-- The original next differential cokernel projection in the native negative source degree. -/
def syzygyConeFirstCoefficient : (negativeComplex P).X (-((n : ℤ)+1)) ⟶ complexSyzygy P (n+1) :=
  (P.extendXIso ComplexShape.embeddingDownNat
    (by simp : ComplexShape.embeddingDownNat.f (n+1) = -((n : ℤ)+1))).hom ≫
      cokernel.π (P.d (n+2) (n+1))

/-- The original degree-n term in the native negative source degree. -/
def syzygyConeSecondCoefficient : (negativeComplex P).X (-(n : ℤ)) ⟶ P.X n :=
  (P.extendXIso ComplexShape.embeddingDownNat
    (by rfl : ComplexShape.embeddingDownNat.f n = -(n : ℤ))).hom

/-- The original incoming differential kills the original next syzygy coefficient. -/
theorem syzygyConeFirstCoefficient_closed :
    (negativeComplex P).d (-((n : ℤ)+2)) (-((n : ℤ)+1)) ≫ syzygyConeFirstCoefficient P n=0 := by
  rw [show (negativeComplex P).d (-((n : ℤ)+2)) (-((n : ℤ)+1)) =
    (P.extendXIso ComplexShape.embeddingDownNat (by simp :
      ComplexShape.embeddingDownNat.f (n+2) = -((n : ℤ)+2))).hom ≫ P.d (n+2) (n+1) ≫
        (P.extendXIso ComplexShape.embeddingDownNat (by simp :
          ComplexShape.embeddingDownNat.f (n+1) = -((n : ℤ)+1))).inv from
    extend_d_eq P ComplexShape.embeddingDownNat (by simp) (by simp)]
  simp [syzygyConeFirstCoefficient,Category.assoc]

/-- The native cone equation uses precisely the original differential factorization in every degree. -/
theorem syzygyConeCoefficient_factor :
    (negativeComplex P).d (-((n : ℤ)+1)) (-(n : ℤ)) ≫ syzygyConeSecondCoefficient P n =
      syzygyConeFirstCoefficient P n ≫ ((complexTower P hP).sequence n).f := by
  change _ = syzygyConeFirstCoefficient P n ≫ complexSyzygyInclusion P n
  rw [show (negativeComplex P).d (-((n : ℤ)+1)) (-(n : ℤ)) =
    (P.extendXIso ComplexShape.embeddingDownNat (by simp :
      ComplexShape.embeddingDownNat.f (n+1) = -((n : ℤ)+1))).hom ≫ P.d (n+1) n ≫
        (P.extendXIso ComplexShape.embeddingDownNat (by rfl :
          ComplexShape.embeddingDownNat.f n = -(n : ℤ))).inv from
    extend_d_eq P ComplexShape.embeddingDownNat (by simp) rfl]
  simp only [syzygyConeSecondCoefficient,syzygyConeFirstCoefficient,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  exact (congrArg (fun f => (P.extendXIso ComplexShape.embeddingDownNat
    (by simp : ComplexShape.embeddingDownNat.f (n+1) = -((n : ℤ)+1))).hom ≫ f)
      (complexSyzygy_factor P n)).symm

/-- The original degree-n term and next syzygy projection give Mathlib's specified native cone cocycle. -/
def syzygySuccessorConeCocycle :
    Cocycle (negativeComplex P) (CochainComplex.mappingCone
      ((CochainComplex.singleFunctor C 0).map ((complexTower P hP).sequence n).f)) (n : ℤ) :=
  successorConeCocycle (negativeComplex P) ((complexTower P hP).sequence n) n
    (syzygyConeFirstCoefficient P n) (syzygyConeFirstCoefficient_closed P n)
    (syzygyConeSecondCoefficient P n) (syzygyConeCoefficient_factor P hP n)

/-- The actual cone augmentation retains the original degree-n differential cokernel projection. -/
theorem syzygySuccessorConeCocycle_augmentation :
    (syzygySuccessorConeCocycle P hP n).val.comp
      (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex
        (((complexTower P hP).sequence n).map (CochainComplex.singleFunctor C 0)))) (add_zero (n : ℤ)) =
      Cochain.toSingleMk (syzygyConeSecondCoefficient P n ≫ cokernel.π (P.d (n+1) n))
        (by omega : -(n : ℤ)+(n : ℤ)=0) :=
  successorConeCocycle_augmentation _ _ _ _ _ _ _

/-- The actual negative cone projection keeps the original next syzygy coefficient and its successor sign. -/
theorem syzygySuccessorConeCocycle_negativeProjection :
    (syzygySuccessorConeCocycle P hP n).val.comp
      (-(CochainComplex.mappingCone.fst
        ((CochainComplex.singleFunctor C 0).map ((complexTower P hP).sequence n).f)).val) rfl =
      ((n : ℤ)+1).negOnePow • Cochain.toSingleMk (syzygyConeFirstCoefficient P n)
        (by omega : -((n : ℤ)+1)+((n : ℤ)+1)=0) :=
  successorConeCocycle_negativeProjection _ _ _ _ _ _ _

end
end BPFixedPoints.ExtResolutionTools
