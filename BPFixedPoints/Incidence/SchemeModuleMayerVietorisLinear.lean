import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity
import BPFixedPoints.Incidence.SheafMayerVietorisQuotient

/-! # The original local Mayer--Vietoris maps over the geometric base ring

All actions are induced by the original structural morphism and scalar sheaf
endomorphisms. The restriction difference and connecting map are the native maps.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance schemeMVLinearHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Original cohomology restrictions preserve the independently defined geometric base action. -/
theorem schemeBaseLocalRestriction_smul {U V : X.Opens} (i : U ⟶ V) (n : ℕ)
    (r : R) (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n V) :
    letI := schemeBaseLocalCohomologyModule f M V n
    letI := schemeBaseLocalCohomologyModule f M U n
    (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n).map i.op (r • x) =
      r • (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n).map i.op x := by
  letI := schemeBaseLocalCohomologyModule f M V n
  letI := schemeBaseLocalCohomologyModule f M U n
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- The native local connecting map is linear over the original geometric coefficients. -/
theorem schemeBaseLocalConnecting_smul (U V : X.Opens) (n : ℕ) (r : R)
    (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V)) :
    letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
    letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
    (Opens.mayerVietorisSquare U V).δ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
      n (n+1) rfl (r • x) =
      r • (show ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) (U ⊔ V) from
        (Opens.mayerVietorisSquare U V).δ ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)
          n (n+1) rfl x) := by
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (show 1+n = n+1 by omega)).symm

/-- The original cohomology restriction, with its original geometric scalar action. -/
noncomputable def schemeBaseLocalRestrictionLinear {U V : X.Opens} (i : U ⟶ V) (n : ℕ) :
    letI := schemeBaseLocalCohomologyModule f M V n
    letI := schemeBaseLocalCohomologyModule f M U n
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n V →ₗ[R]
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n U := by
  letI := schemeBaseLocalCohomologyModule f M V n
  letI := schemeBaseLocalCohomologyModule f M U n
  exact { (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n).map i.op |>.hom with
    map_smul' := schemeBaseLocalRestriction_smul f M i n }

/-- The original local connecting homomorphism, with its original geometric scalar action. -/
noncomputable def schemeBaseLocalConnectingLinear (U V : X.Opens) (n : ℕ) :
    letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
    letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V) →ₗ[R]
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) (U ⊔ V) := by
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
  exact { ((Opens.mayerVietorisSquare U V).δ
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n (n+1) rfl).hom with
      map_smul' := schemeBaseLocalConnecting_smul f M U V n }

/-- The image of the original restriction difference is a submodule for the original base action. -/
noncomputable def schemeBaseMayerVietorisImage (U V : X.Opens) (n : ℕ) :
    letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
    Submodule R (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V)) := by
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
  let F := (SheafOfModules.toSheaf X.ringCatSheaf).obj M
  let S := Opens.mayerVietorisSquare U V
  refine { (S.fromBiprod F n).hom.range.toAddSubmonoid with smul_mem' := ?_ }
  intro r x hx
  have he := ((S.sequence_exact F n (n+1) rfl).exact 1).ab_range_eq_ker
  change (S.fromBiprod F n).hom.range = (S.δ F n (n+1) rfl).hom.ker at he
  change x ∈ (S.fromBiprod F n).hom.range at hx
  change r • x ∈ (S.fromBiprod F n).hom.range
  rw [he] at hx ⊢
  change S.δ F n (n+1) rfl (r • x) = 0
  change S.δ F n (n+1) rfl x = 0 at hx
  rw [schemeBaseLocalConnecting_smul f M U V n, hx, smul_zero]

/-- The original restriction cokernel inherits the quotient of the geometric Ext action. -/
@[instance_reducible] noncomputable def schemeBaseMayerVietorisCokernelModule
    (U V : X.Opens) (n : ℕ) :
    Module R (SheafTools.mayerVietorisCokernel
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U V n) := by
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  exact inferInstanceAs (Module R
    ((((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V)) ⧸
      schemeBaseMayerVietorisImage f M U V n))

variable (U V : X.Opens) (n : ℕ)
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) U)]
variable [Subsingleton (((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) V)]

/-- The existing Mayer--Vietoris quotient comparison is linear for the original geometric actions. -/
noncomputable def schemeBaseMayerVietorisCokernelLinearEquiv :
    letI := schemeBaseMayerVietorisCokernelModule f M U V n
    letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
    SheafTools.mayerVietorisCokernel ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U V n ≃ₗ[R]
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (n+1) (U ⊔ V) := by
  letI := schemeBaseMayerVietorisCokernelModule f M U V n
  letI := schemeBaseLocalCohomologyModule f M (U ⊔ V) (n+1)
  refine { SheafTools.mayerVietorisCokernelEquiv
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U V n with map_smul' := ?_ }
  intro r x
  refine Quotient.inductionOn' x (fun y => ?_)
  letI := schemeBaseLocalCohomologyModule f M (U ⊓ V) n
  let z : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' n (U ⊓ V) := y
  change SheafTools.mayerVietorisCokernelEquiv _ U V n (QuotientAddGroup.mk (r • z)) =
    r • SheafTools.mayerVietorisCokernelEquiv _ U V n (QuotientAddGroup.mk z)
  rw [SheafTools.mayerVietorisCokernelEquiv_mk, SheafTools.mayerVietorisCokernelEquiv_mk]
  exact schemeBaseLocalConnecting_smul f M U V n r z

end BPFixedPoints.SchemeTools
