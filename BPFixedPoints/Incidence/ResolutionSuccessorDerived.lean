import BPFixedPoints.Incidence.NativeHomShiftComposition

/-! # The original successor cone formula as actual derived shifted composition -/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open CochainComplex CochainComplex.HomComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (K : CochainComplex C ℤ) (S : ShortComplex C) (n : ℤ)
variable (u : K.X (-(n+1)) ⟶ S.X₁) (hu : K.d (-(n+2)) (-(n+1)) ≫ u=0)
variable (v : K.X (-n) ⟶ S.X₂) (huv : K.d (-(n+1)) (-n) ≫ v=u ≫ S.f)

/-- The original successor cone projects by native shifted composition with exactly its specified next-coefficient sign. -/
theorem successorCone_nativeProjection :
    ShiftedHom.comp (Cocycle.equivHomShift.symm (successorConeCocycle K S n u hu v huv))
      (CochainComplex.mappingCone.triangle ((CochainComplex.singleFunctor C 0).map S.f)).mor₃
        (by omega : 1+n=n+1) =
      Cocycle.equivHomShift.symm ((n+1).negOnePow •
        Cocycle.toSingleMk u (by omega : -(n+1)+(n+1)=0) (-(n+2)) (by omega) hu) := by
  exact nativeHomShift_comp _ _ _ _ (successorConeCocycle_negativeProjection K S n u hu v huv)

variable [HasDerivedCategory.{w} C]

/-- The native SES connecting morphism composes the original successor cone augmentation into its specified next cocycle. -/
theorem successorCone_derivedConnecting (hS : S.ShortExact) :
    ShiftedHom.comp
      (ShiftedHom.map (Cocycle.equivHomShift.symm (Cocycle.postcomp
        (successorConeCocycle K S n u hu v huv)
        (CochainComplex.mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0)))))
          DerivedCategory.Q)
      hS.singleδ (by omega : 1+n=n+1) =
    ShiftedHom.map (Cocycle.equivHomShift.symm ((n+1).negOnePow •
      Cocycle.toSingleMk u (by omega : -(n+1)+(n+1)=0) (-(n+2)) (by omega) hu)) DerivedCategory.Q := by
  let L := Cocycle.equivHomShift.symm (successorConeCocycle K S n u hu v huv)
  let q := CochainComplex.mappingCone.descShortComplex (S.map (CochainComplex.singleFunctor C 0))
  rw [Cocycle.equivHomShift_symm_postcomp]
  have hq : DerivedCategory.Q.map q ≫ hS.singleδ =
      ShiftedHom.map
        (CochainComplex.mappingCone.triangle ((CochainComplex.singleFunctor C 0).map S.f)).mor₃
        DerivedCategory.Q := by
    exact DerivedCategory.descShortComplex_triangleOfSESδ
      (hS.map_of_exact (CochainComplex.singleFunctor C 0))
  have h := congrArg (fun f => ShiftedHom.map f DerivedCategory.Q)
    (successorCone_nativeProjection K S n u hu v huv)
  rw [ShiftedHom.map_comp] at h
  change ShiftedHom.comp (ShiftedHom.map (L ≫ q⟦n⟧') DerivedCategory.Q) hS.singleδ _ = _
  calc
    _ = ShiftedHom.comp (ShiftedHom.map L DerivedCategory.Q) (DerivedCategory.Q.map q ≫ hS.singleδ) _ := by
      simp only [ShiftedHom.comp,ShiftedHom.map,Functor.map_comp,Category.assoc,
        ← Functor.commShiftIso_hom_naturality_assoc]
    _ = _ := by rw [hq]; exact h

end
end BPFixedPoints.ExtResolutionTools
