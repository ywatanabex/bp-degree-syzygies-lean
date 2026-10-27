import BPFixedPoints.Incidence.BinaryCoverCellCohomologyCup
import BPFixedPoints.Incidence.AcyclicResolutionDegreeScalars

/-! # The original cubical classes compute actual sheaf cohomology in every degree

Degree zero uses the original exact augmentation and closed cochains.
Positive degrees retain the existing original quotient and Yoneda
comparison. All representatives and the independent geometric base
actions are retained; no product on actual Ext is defined here.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance degreeCubicalHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- Degree zero computes the actual original global cohomology without term acyclicity. -/
def finiteCubicalActualZeroEquiv
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) :
    cubicalCohomologyAt U F 0 ≃+ F.H 0 := by
  letI := augmentation_epi U hcover
  exact (((cubicalTower U).cycleEquiv F 0).trans Ext.addEquiv₀.symm).trans
    (((((extFunctor 0).mapIso (complexAugmentationIso _ (augmentation U)
      (augmentation_zero U) (augmentation_exact U)).symm.op).app F).addCommGroupIsoToAddEquiv).trans
        (localSheafTopEquiv F 0))

/-- The same original cubical resolution computes actual sheaf cohomology in every degree. -/
def finiteCubicalActualAtEquiv
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    cubicalCohomologyAt U F n ≃+ F.H n := by
  letI := augmentation_epi U hcover
  exact ((cubicalTower U).cohomologyAtExtEquiv F (complexTower_acyclic _ _ _ ha) n).trans
    (((((extFunctor n).mapIso (complexAugmentationIso _ (augmentation U)
      (augmentation_zero U) (augmentation_exact U)).symm.op).app F).addCommGroupIsoToAddEquiv).trans
        (localSheafTopEquiv F n))

/-- Every positive comparison is the original comparison itself. -/
theorem finiteCubicalActualAtEquiv_succ
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    finiteCubicalActualAtEquiv U F hcover ha (n+1) = finiteCubicalActualEquiv U F hcover ha n := rfl

/-- The zero comparison retains the same original augmentation-only comparison. -/
theorem finiteCubicalActualAtEquiv_zero
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) :
    finiteCubicalActualAtEquiv U F hcover ha 0 = finiteCubicalActualZeroEquiv U F hcover := rfl

/-- Every original class retains its original factorization, augmentation, and iterated Yoneda representative. -/
theorem finiteCubicalActualAtEquiv_class
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) (x : (cubicalTower U).cycles F n) :
    letI := augmentation_epi U hcover
    finiteCubicalActualAtEquiv U F hcover ha n ((cubicalTower U).classAt F n x) =
      localSheafTopEquiv F n
        ((Ext.mk₀ (complexAugmentationIso _ (augmentation U) (augmentation_zero U)
          (augmentation_exact U)).inv).comp ((cubicalTower U).cocycleComparison F n x) (zero_add n)) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv F n
    ((((extFunctor n).mapIso (complexAugmentationIso _ (augmentation U) (augmentation_zero U)
      (augmentation_exact U)).symm.op).app F).hom
        ((cubicalTower U).cohomologyAtExtEquiv F _ n ((cubicalTower U).classAt F n x))) = _
  rw [ExactTower.cohomologyAtExtEquiv_class]
  rfl

private theorem cubicalExtIso_postcomp
    {A B F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
    (e : A ≅ B) (f : F ⟶ G) (n : ℕ) (x : Ext.{1} B F n) :
    (((extFunctor n).mapIso e.op).app G).hom (x.comp (Ext.mk₀ f) (add_zero n)) =
      ((((extFunctor n).mapIso e.op).app F).hom x).comp (Ext.mk₀ f) (add_zero n) := by
  change (Ext.mk₀ e.hom).comp (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ e.hom).comp x (zero_add n)).comp (Ext.mk₀ f) (add_zero n)
  exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.hom) x (Ext.mk₀ f) (zero_add n)).symm

/-- The augmentation-only degree-zero comparison is target-natural without term acyclicity. -/
theorem finiteCubicalActualZeroEquiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (g : F ⟶ G)
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b) (x : cubicalCohomologyAt U F 0) :
    finiteCubicalActualZeroEquiv U G hcover ((cubicalTower U).mapAt g 0 x) =
      Sheaf.H.map g 0 (finiteCubicalActualZeroEquiv U F hcover x) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv G 0
    ((((extFunctor 0).mapIso (complexAugmentationIso _ (augmentation U) (augmentation_zero U)
      (augmentation_exact U)).symm.op).app G).hom
        (Ext.mk₀ ((cubicalTower U).cycleEquiv G 0 ((cubicalTower U).mapCycles g 0 x)))) = _
  rw [ExactTower.cycleEquiv_postcomp,← Ext.mk₀_comp_mk₀,cubicalExtIso_postcomp]
  exact localSheafTopEquiv_naturality g 0 _

/-- The same original comparison retains every original target morphism in every actual degree. -/
theorem finiteCubicalActualAtEquiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (g : F ⟶ G)
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (n : ℕ) (x : cubicalCohomologyAt U F n) :
    finiteCubicalActualAtEquiv U G hcover haG n ((cubicalTower U).mapAt g n x) =
      Sheaf.H.map g n (finiteCubicalActualAtEquiv U F hcover haF n x) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv G n
    ((((extFunctor n).mapIso (complexAugmentationIso _ (augmentation U) (augmentation_zero U)
      (augmentation_exact U)).symm.op).app G).hom
        ((cubicalTower U).cohomologyAtExtEquiv G _ n ((cubicalTower U).mapAt g n x))) = _
  rw [ExactTower.cohomologyAtExtEquiv_postcomp,cubicalExtIso_postcomp]
  exact localSheafTopEquiv_naturality g n _

end
end BPFixedPoints.SheafTools.BinaryCells

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open SheafTools.BinaryCells ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → X.Opens)
local instance degreeGeometricHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original geometric target action acts on original cubical classes in every actual degree. -/
@[instance_reducible] def schemeBaseCubicalAtModule (n : ℕ) :
    Module R (cubicalCohomologyAt U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :=
  (cubicalTower U).cohomologyAtModule (schemeBaseAbelianScalarHom f M) n

/-- Actual degree zero is compared over the original geometric base without term acyclicity. -/
def schemeBaseFiniteCubicalZeroActualLinearEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ b, chartOpen U b) :
    letI := schemeBaseCubicalAtModule f M U 0
    letI := schemeBaseCohomologyModule f M 0
    cubicalCohomologyAt U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 0 ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) 0 := by
  letI := schemeBaseCubicalAtModule f M U 0
  letI := schemeBaseCohomologyModule f M 0
  refine { finiteCubicalActualZeroEquiv U _ hcover with map_smul' := ?_ }
  intro r x
  change finiteCubicalActualZeroEquiv U _ hcover
    ((cubicalTower U).mapAt (schemeBaseAbelianScalar f M r) 0 x) = _
  rw [finiteCubicalActualZeroEquiv_postcomp]
  rfl

/-- Actual cohomology is compared linearly with the original classes and independent geometric actions in every degree. -/
def schemeBaseFiniteCubicalAtActualLinearEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)) (n : ℕ) :
    letI := schemeBaseCubicalAtModule f M U n
    letI := schemeBaseCohomologyModule f M n
    cubicalCohomologyAt U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n := by
  letI := schemeBaseCubicalAtModule f M U n
  letI := schemeBaseCohomologyModule f M n
  refine { finiteCubicalActualAtEquiv U _ hcover ha n with map_smul' := ?_ }
  intro r x
  change finiteCubicalActualAtEquiv U _ hcover ha n
    ((cubicalTower U).mapAt (schemeBaseAbelianScalar f M r) n x) = _
  rw [finiteCubicalActualAtEquiv_postcomp]
  rfl

end
end BPFixedPoints.SchemeTools
