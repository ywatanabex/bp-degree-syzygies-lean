import BPFixedPoints.Incidence.ResolutionSuccessorDerived
import BPFixedPoints.Incidence.ResolutionNativeExtTarget

/-! # Original syzygy projections compose with the actual native SES class -/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
universe w w' v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ) (hP : ∀ n, P.ExactAt (n+1))

/-- The original degree-n projection is the actual augmentation cocycle of the original successor cone. -/
def syzygyProjectionCocycle (n : ℕ) :
    Cocycle (negativeComplex P) ((CochainComplex.singleFunctor C 0).obj (complexSyzygy P n)) (n : ℤ) :=
  Cocycle.postcomp (syzygySuccessorConeCocycle P hP n)
    (CochainComplex.mappingCone.descShortComplex
      (((complexTower P hP).sequence n).map (CochainComplex.singleFunctor C 0)))

/-- The original projection cocycle retains its independently specified native single-map representative. -/
theorem syzygyProjectionCocycle_native (n : ℕ) :
    Cocycle.equivHomShift.symm (syzygyProjectionCocycle P hP n) =
      negativeCocycleMap P n (cokernel.π (P.d (n+1) n)) (cokernel.condition _) ≫
        ((CochainComplex.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app (complexSyzygy P n) := by
  apply nativeHomShift_single_of_coefficient
  change (syzygySuccessorConeCocycle P hP n).val.comp
    (Cochain.ofHom (CochainComplex.mappingCone.descShortComplex
      (((complexTower P hP).sequence n).map (CochainComplex.singleFunctor C 0)))) (add_zero (n : ℤ)) = _
  rw [syzygySuccessorConeCocycle_augmentation,negativeCocycleMap_component]
  simp [syzygyConeSecondCoefficient,complexSyzygy,Category.assoc]

variable [HasDerivedCategory.{w} C]

/-- The original native single-degree representative retains its native derived single shift. -/
theorem syzygyProjectionCocycle_derived (n : ℕ) :
    ShiftedHom.map (Cocycle.equivHomShift.symm (syzygyProjectionCocycle P hP n)) DerivedCategory.Q =
      DerivedCategory.Q.map (negativeCocycleMap P n (cokernel.π (P.d (n+1) n)) (cokernel.condition _)) ≫
        ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app (complexSyzygy P n) := by
  rw [syzygyProjectionCocycle_native]
  simp [ShiftedHom.map,Functor.map_comp,DerivedCategory.singleFunctors,SingleFunctors.postcomp,Category.assoc]

omit [HasDerivedCategory C] in
/-- The next original coefficient in the successor cone gives the next original projection cocycle itself. -/
theorem syzygyNextCocycle_native (n : ℕ) :
    Cocycle.equivHomShift.symm (Cocycle.toSingleMk (syzygyConeFirstCoefficient P n)
      (by omega : -((n : ℤ)+1)+((n : ℤ)+1)=0) (-((n : ℤ)+2)) (by omega)
        (syzygyConeFirstCoefficient_closed P n)) =
      negativeCocycleMap P (n+1) (cokernel.π (P.d (n+2) (n+1))) (cokernel.condition _) ≫
        ((CochainComplex.singleFunctors C).shiftIso ((n : ℤ)+1) (-((n : ℤ)+1)) 0 (by omega)).inv.app
          (complexSyzygy P (n+1)) := by
  apply nativeHomShift_single_of_coefficient
  have hc := negativeCocycleMap_component P (n+1) (cokernel.π (P.d (n+2) (n+1))) (cokernel.condition _)
  erw [hc]
  simp [syzygyConeFirstCoefficient,complexSyzygy,Category.assoc]

/-- The actual native derived successor composition has exactly the original next syzygy coefficient and its sign. -/
theorem nativeSyzygyProjection_step (n : ℕ) :
    ShiftedHom.comp
      (DerivedCategory.Q.map (negativeCocycleMap P n (cokernel.π (P.d (n+1) n)) (cokernel.condition _)) ≫
        ((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app (complexSyzygy P n))
      (complexSyzygy_shortExact P n (hP n)).singleδ (by omega : 1+(n : ℤ)=((n+1 : ℕ) : ℤ)) =
    ((n : ℤ)+1).negOnePow •
      (DerivedCategory.Q.map (negativeCocycleMap P (n+1) (cokernel.π (P.d (n+1+1) (n+1))) (cokernel.condition _)) ≫
        ((DerivedCategory.singleFunctors C).shiftIso ((n+1 : ℕ) : ℤ) (-((n+1 : ℕ) : ℤ)) 0 (by omega)).inv.app
          (complexSyzygy P (n+1))) := by
  have h := successorCone_derivedConnecting (negativeComplex P) ((complexTower P hP).sequence n)
    n (syzygyConeFirstCoefficient P n) (syzygyConeFirstCoefficient_closed P n)
    (syzygyConeSecondCoefficient P n) (syzygyConeCoefficient_factor P hP n)
    (complexSyzygy_shortExact P n (hP n))
  change ShiftedHom.comp
    (ShiftedHom.map (Cocycle.equivHomShift.symm (syzygyProjectionCocycle P hP n)) DerivedCategory.Q) _ _ = _ at h
  rw [syzygyProjectionCocycle_derived] at h
  simp only [Units.smul_def] at h
  rw [Cocycle.equivHomShift_symm_smul] at h
  erw [syzygyNextCocycle_native P n] at h
  simpa [ShiftedHom.map,Units.smul_def,Functor.map_zsmul,Preadditive.zsmul_comp,
    DerivedCategory.singleFunctors,SingleFunctors.postcomp,Functor.map_comp,Category.assoc,
    ExactTower.sequence,complexTower,Int.natCast_succ,Int.natCast_add,
    Int.natCast_zero,zero_add,Nat.add_assoc] using h

end
end BPFixedPoints.ExtResolutionTools
