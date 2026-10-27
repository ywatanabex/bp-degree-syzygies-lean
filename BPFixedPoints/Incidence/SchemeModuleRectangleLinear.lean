import BPFixedPoints.Incidence.SheafRectangleTopQuotient
import BPFixedPoints.Incidence.SchemeModuleMayerVietorisLinear
import BPFixedPoints.Incidence.SchemeModuleOpenRestrictions

/-! # The native rectangular H2 quotient over the original geometric base ring -/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance schemeRectangleHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Package native local Ext with the independently defined geometric scalar action. -/
noncomputable def schemeBaseLocalCohomologyObject (U : X.Opens) (n : ℕ) : ModuleCat.{1} R := by
  letI := schemeBaseLocalCohomologyModule f M U n
  exact ModuleCat.of R (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n U)

/-- The original whole-open Ext comparison is linear for the original geometric actions. -/
noncomputable def schemeBaseCoverCohomologyLinearEquiv (U : X.Opens) (hU : U = ⊤) (n : ℕ) :
    letI := schemeBaseCohomologyModule f M n
    schemeBaseLocalCohomologyObject f M U n ≃ₗ[R]
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H n := by
  subst U
  exact schemeBaseLocalTopLinearEquiv f M n

/-- The linear cover comparison is exactly the original native cover comparison on elements. -/
theorem schemeBaseCoverCohomologyLinearEquiv_apply (U : X.Opens) (hU : U = ⊤) (n : ℕ)
    (x : schemeBaseLocalCohomologyObject f M U n) :
    schemeBaseCoverCohomologyLinearEquiv f M U hU n x =
      SheafTools.localSheafCoverEquiv ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n U hU x := by
  subst U
  rfl

/-- Every native Mayer--Vietoris square has an original-base-linear connecting map. -/
noncomputable def schemeBaseSquareConnectingLinear
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (n : ℕ) :
    schemeBaseLocalCohomologyObject f M S.X₁ n →ₗ[R]
      schemeBaseLocalCohomologyObject f M S.X₄ (n+1) := by
  letI := schemeBaseLocalCohomologyModule f M S.X₁ n
  letI := schemeBaseLocalCohomologyModule f M S.X₄ (n+1)
  change (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n S.X₁) →ₗ[R]
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) S.X₄)
  refine { (S.δ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n+1) rfl).hom with
    map_smul' := ?_ }
  intro r x
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (show 1+n = n+1 by omega)).symm

/-- The native section connecting map is linear for the original geometric actions. -/
noncomputable def schemeBaseSectionConnectingLinear
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) :
    schemeBaseOpenSectionModule f M S.X₁ →ₗ[R] schemeBaseLocalCohomologyObject f M S.X₄ 1 := by
  letI := schemeBaseLocalCohomologyModule f M S.X₁ 0
  letI := schemeBaseOpenModuleSections f M S.X₁
  exact (schemeBaseSquareConnectingLinear f M S 0).comp
    (schemeBaseLocalH0LinearEquiv f M S.X₁).symm.toLinearMap

variable (C D : X.Opens) (hCD : C ⊔ D = ⊤) (A B : X.Opens)

/-- The specified native two-step connecting map with the original base action. -/
noncomputable def schemeRectangleTopConnectingLinear :
    schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ (C ⊓ D)) →ₗ[R]
      schemeBaseLocalCohomologyObject f M (A ⊔ B) 2 :=
  (schemeBaseSquareConnectingLinear f M (Opens.mayerVietorisSquare A B) 1).comp
    (schemeBaseSectionConnectingLinear f M (SheafTools.rectangleRowSquare C D hCD (A ⊓ B)))

/-- Original native section modules on the four one-overlap faces. -/
abbrev SchemeRectangleBoundarySections :=
  (schemeBaseOpenSectionModule f M (A ⊓ (C ⊓ D)) × schemeBaseOpenSectionModule f M (B ⊓ (C ⊓ D))) ×
    (schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ C) × schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ D))

/-- The original four signed native restrictions are linear over the original base. -/
noncomputable def schemeRectangleBoundaryLinear :
    SchemeRectangleBoundarySections f M C D A B →ₗ[R]
      schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ (C ⊓ D)) :=
  { toFun := fun x =>
      (schemeBaseOpenRestrictionLinear f M (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_left)) x.1.1 -
        schemeBaseOpenRestrictionLinear f M (homOfLE (inf_le_inf_right (C ⊓ D) inf_le_right)) x.1.2) -
      (schemeBaseOpenRestrictionLinear f M (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_left)) x.2.1 -
        schemeBaseOpenRestrictionLinear f M (homOfLE (inf_le_inf_left (A ⊓ B) inf_le_right)) x.2.2)
    map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
    map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_sub, RingHom.id_apply] }

/-- The specified linear map is the original two-step connecting class on every representative. -/
theorem schemeRectangleTopConnectingLinear_apply
    (x : schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ (C ⊓ D))) :
    schemeRectangleTopConnectingLinear f M C D hCD A B x =
      SheafTools.rectangleTopConnecting ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) C D hCD A B x := rfl

variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 (A ⊓ C))]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 (A ⊓ D))]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 (B ⊓ C))]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 (B ⊓ D))]

/-- The native boundary image is the kernel with the independent geometric base action. -/
theorem schemeRectangleBoundaryLinear_range :
    LinearMap.range (schemeRectangleBoundaryLinear f M C D A B) =
      LinearMap.ker (schemeRectangleTopConnectingLinear f M C D hCD A B) := by
  ext x
  exact (SheafTools.rectangleTopConnecting_eq_zero_iff
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) C D hCD A B x).symm

variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 2 A)]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 2 B)]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 ((A ⊓ B) ⊓ C))]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' 1 ((A ⊓ B) ⊓ D))]

/-- The native rectangular section quotient computes actual H2 linearly over the original base ring. -/
noncomputable def schemeRectangleSectionH2LinearEquiv :
    (schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ (C ⊓ D)) ⧸
      LinearMap.range (schemeRectangleBoundaryLinear f M C D A B)) ≃ₗ[R]
        schemeBaseLocalCohomologyObject f M (A ⊔ B) 2 :=
  (Submodule.quotEquivOfEq _ _ (schemeRectangleBoundaryLinear_range f M C D hCD A B)).trans
    ((schemeRectangleTopConnectingLinear f M C D hCD A B).quotKerEquivOfSurjective
      (SheafTools.rectangleTopConnecting_surjective
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) C D hCD A B))

/-- Every native quotient representative maps to the original iterated connecting class, linearly. -/
theorem schemeRectangleSectionH2LinearEquiv_mk
    (x : schemeBaseOpenSectionModule f M ((A ⊓ B) ⊓ (C ⊓ D))) :
    schemeRectangleSectionH2LinearEquiv f M C D hCD A B (Submodule.Quotient.mk x) =
      schemeRectangleTopConnectingLinear f M C D hCD A B x := rfl

end BPFixedPoints.SchemeTools
