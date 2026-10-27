import BPFixedPoints.Incidence.SchemeModuleSectionKernel

/-! # Native positive cohomology as a restriction kernel when the previous overlap group vanishes -/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance mvKernelHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

/-- The original cohomology pair of restrictions, retaining the geometric base action. -/
noncomputable def schemeBaseSquareCohomologyPair (n : ℕ) :
    schemeBaseLocalCohomologyObject f M S.X₄ n →ₗ[R]
      schemeBaseLocalCohomologyObject f M S.X₂ n × schemeBaseLocalCohomologyObject f M S.X₃ n := by
  letI := schemeBaseLocalCohomologyModule f M S.X₄ n
  letI := schemeBaseLocalCohomologyModule f M S.X₂ n
  letI := schemeBaseLocalCohomologyModule f M S.X₃ n
  exact (schemeBaseLocalRestrictionLinear f M S.f₂₄ n).prod (schemeBaseLocalRestrictionLinear f M S.f₃₄ n)

/-- The original restriction difference on cohomology, retaining the geometric base action. -/
noncomputable def schemeBaseSquareCohomologyDifference (n : ℕ) :
    (schemeBaseLocalCohomologyObject f M S.X₂ n × schemeBaseLocalCohomologyObject f M S.X₃ n) →ₗ[R]
      schemeBaseLocalCohomologyObject f M S.X₁ n := by
  letI := schemeBaseLocalCohomologyModule f M S.X₂ n
  letI := schemeBaseLocalCohomologyModule f M S.X₃ n
  letI := schemeBaseLocalCohomologyModule f M S.X₁ n
  exact (schemeBaseLocalRestrictionLinear f M S.f₁₂ n).comp (LinearMap.fst R _ _) -
    (schemeBaseLocalRestrictionLinear f M S.f₁₃ n).comp (LinearMap.snd R _ _)

/-- The native cohomology pair has exactly the original restriction-difference kernel as its image. -/
theorem schemeBaseSquareCohomologyPair_range (n : ℕ) :
    LinearMap.range (schemeBaseSquareCohomologyPair f M S (n+1)) =
      LinearMap.ker (schemeBaseSquareCohomologyDifference f M S (n+1)) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  have he := ((S.sequence_exact F n (n+1) rfl).exact 3).ab_range_eq_ker
  change (S.toBiprod F (n+1)).hom.range = (S.fromBiprod F (n+1)).hom.ker at he
  ext z
  have hz : (S.fromBiprod F (n+1)) ((AddCommGrpCat.biprodIsoProd _ _).inv z) =
      schemeBaseSquareCohomologyDifference f M S (n+1) z :=
    S.fromBiprod_biprodIsoProd_inv_apply F z.1 z.2
  constructor
  · rintro ⟨x,rfl⟩
    change schemeBaseSquareCohomologyDifference f M S (n+1) _ = 0
    rw [← hz]
    have hx : (AddCommGrpCat.biprodIsoProd _ _).inv
        (schemeBaseSquareCohomologyPair f M S (n+1) x) ∈ (S.toBiprod F (n+1)).hom.range :=
      ⟨x,S.toBiprod_apply F x⟩
    rw [he] at hx
    exact hx
  · intro h
    change schemeBaseSquareCohomologyDifference f M S (n+1) z = 0 at h
    have hx : (AddCommGrpCat.biprodIsoProd _ _).inv z ∈ (S.toBiprod F (n+1)).hom.range := by
      rw [he]
      exact hz.trans h
    obtain ⟨x,hx⟩ := hx
    refine ⟨x,?_⟩
    rw [S.toBiprod_apply] at hx
    exact (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.injective hx

variable (n : ℕ)
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n S.X₁)]

/-- Vanishing of the previous overlap group makes the original cohomology pair injective. -/
theorem schemeBaseSquareCohomologyPair_injective :
    Function.Injective (schemeBaseSquareCohomologyPair f M S (n+1)) := by
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  have he := ((S.sequence_exact F n (n+1) rfl).exact 2).ab_range_eq_ker
  change (S.δ F n (n+1) rfl).hom.range = (S.toBiprod F (n+1)).hom.ker at he
  intro x y h
  have ht : S.toBiprod F (n+1) (x-y) = 0 := by
    rw [map_sub,S.toBiprod_apply,S.toBiprod_apply]
    change (AddCommGrpCat.biprodIsoProd _ _).inv (schemeBaseSquareCohomologyPair f M S (n+1) x) -
      (AddCommGrpCat.biprodIsoProd _ _).inv (schemeBaseSquareCohomologyPair f M S (n+1) y) = 0
    rw [h,sub_self]
  have hx : x-y ∈ (S.δ F n (n+1) rfl).hom.range := by rw [he]; exact ht
  obtain ⟨z,hz⟩ := hx
  have hz0 : z = 0 := Subsingleton.elim _ _
  rw [hz0,map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- Actual next cohomology is the original matching kernel when the previous overlap group vanishes. -/
noncomputable def schemeBaseSquareCohomologyKernelEquiv :
    schemeBaseLocalCohomologyObject f M S.X₄ (n+1) ≃ₗ[R]
      LinearMap.ker (schemeBaseSquareCohomologyDifference f M S (n+1)) :=
  (LinearEquiv.ofInjective (schemeBaseSquareCohomologyPair f M S (n+1))
    (schemeBaseSquareCohomologyPair_injective f M S n)).trans
      (LinearEquiv.ofEq _ _ (schemeBaseSquareCohomologyPair_range f M S n))

/-- Every actual class retains the two original restrictions in the specified kernel comparison. -/
theorem schemeBaseSquareCohomologyKernelEquiv_val
    (x : schemeBaseLocalCohomologyObject f M S.X₄ (n+1)) :
    (schemeBaseSquareCohomologyKernelEquiv f M S n x).val =
      schemeBaseSquareCohomologyPair f M S (n+1) x := rfl

end BPFixedPoints.SchemeTools
