import BPFixedPoints.Incidence.AcyclicResolutionComplex
import BPFixedPoints.Incidence.AcyclicResolutionScalars
import BPFixedPoints.Incidence.SchemeModuleCohomologyScalars

/-! # Geometric base-linear Ext comparison for actual sheaf resolutions

The target is the original underlying abelian sheaf. Source scalars are defined
on original cohomology representatives by the original geometric sheaf action,
before any cohomology isomorphism. No field hypothesis or transported action is used.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
universe v
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
noncomputable local instance resolutionCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The original geometric scalar endomorphisms, packaged as their original endomorphism ring map. -/
noncomputable def schemeBaseAbelianScalarHom : R →+* End ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) where
  toFun r := End.of (schemeBaseAbelianScalar f M r)
  map_one' := End.ext (schemeBaseAbelianScalar_one f M)
  map_zero' := End.ext (schemeBaseAbelianScalar_zero f M)
  map_add' r s := End.ext (schemeBaseAbelianScalar_add f M r s)
  map_mul' r s := End.ext (schemeBaseAbelianScalar_mul f M r s)

/-- The original geometric base action on original resolution cohomology, defined by original sheaf postcomposition. -/
@[instance_reducible] noncomputable def schemeBaseResolutionCohomologyModule
    (T : ExactTower (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})) (n : ℕ) :
    Module R (T.cohomology ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) := T.cohomologyModule (schemeBaseAbelianScalarHom f M) n

/-- Every scalar retains the original geometric endomorphism on every original cocycle representative. -/
theorem schemeBaseResolutionCohomology_smul
    (T : ExactTower (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))
    (n : ℕ) (r : R) (x : T.cycles ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1)) :
    letI := schemeBaseResolutionCohomologyModule f M T n
    r • (QuotientAddGroup.mk x : T.cohomology ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) =
      QuotientAddGroup.mk (T.mapCycles (schemeBaseAbelianScalar f M r) (n+1) x) := rfl

/-- The original resolution cohomology computes actual Ext linearly for the already defined original geometric actions. -/
noncomputable def schemeBaseResolutionCohomologyLinearEquiv
    (T : ExactTower (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}))
    (h : T.AcyclicAgainst ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    letI := schemeBaseResolutionCohomologyModule f M T n
    letI := schemeBaseExtModule f M (T.K 0) (n+1)
    T.cohomology ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R] Ext.{1} (T.K 0) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) := by
  letI := schemeBaseExtModule f M (T.K 0) (n+1)
  exact T.cohomologyLinearEquiv (schemeBaseAbelianScalarHom f M) n h (fun _ _ => rfl)

/-- The original constant integer sheaf used by Mathlib's actual global sheaf cohomology. -/
noncomputable abbrev schemeCohomologyUnit (X : Scheme.{0}) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}).obj
    (AddCommGrpCat.of (ULift ℤ))

/-- An original exact augmentation computes actual Ext linearly over the original geometric base. -/
noncomputable def schemeBaseAugmentedExtLinearEquiv
    (P : ChainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) ℕ)
    (h : ∀ n, P.ExactAt (n+1))
    {A : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}} (π : P.X 0 ⟶ A)
    (hz : P.d 1 0 ≫ π = 0) (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    (ha : ComplexAcyclicAgainst P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    letI := schemeBaseResolutionCohomologyModule f M (complexTower P h) n
    letI := schemeBaseExtModule f M A (n+1)
    (complexTower P h).cohomology ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Ext.{1} A ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) := by
  letI := schemeBaseResolutionCohomologyModule f M (complexTower P h) n
  letI := schemeBaseExtModule f M A (n+1)
  refine { augmentedComplexExtEquiv P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) h π hz he ha n with map_smul' := ?_ }
  intro r x
  change augmentedComplexExtEquiv P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) h π hz he ha n
    ((complexTower P h).mapCohomology (schemeBaseAbelianScalar f M r) n x) =
      r • augmentedComplexExtEquiv P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) h π hz he ha n x
  rw [augmentedComplexExtEquiv_postcomp]
  rfl

/-- An original exact augmentation and actual term acyclicity compute genuine global sheaf cohomology over the geometric base. -/
noncomputable def schemeBaseAugmentedResolutionCohomologyLinearEquiv
    (P : ChainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) ℕ)
    (h : ∀ n, P.ExactAt (n+1)) (π : P.X 0 ⟶ schemeCohomologyUnit X)
    (hz : P.d 1 0 ≫ π = 0) (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    (ha : ComplexAcyclicAgainst P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    letI := schemeBaseResolutionCohomologyModule f M (complexTower P h) n
    letI := schemeBaseCohomologyModule f M (n+1)
    (complexTower P h).cohomology ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) :=
  schemeBaseAugmentedExtLinearEquiv f M P h π hz he ha n

/-- Every original cocycle uses the specified native extension classes and original augmentation in the global linear comparison. -/
theorem schemeBaseAugmentedResolutionCohomologyLinearEquiv_mk
    (P : ChainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) ℕ)
    (h : ∀ n, P.ExactAt (n+1)) (π : P.X 0 ⟶ schemeCohomologyUnit X)
    (hz : P.d 1 0 ≫ π = 0) (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    (ha : ComplexAcyclicAgainst P ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) (x : (complexTower P h).cycles ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1)) :
    schemeBaseAugmentedResolutionCohomologyLinearEquiv f M P h π hz he ha n (QuotientAddGroup.mk x) =
      (((extFunctor (n+1)).mapIso (complexAugmentationIso P π hz he).symm.op).app ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)).hom
        ((complexTower P h).cocycleComparison ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) x) := rfl

end BPFixedPoints.SchemeTools
