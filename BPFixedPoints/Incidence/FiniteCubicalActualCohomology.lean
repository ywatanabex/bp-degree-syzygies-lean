import BPFixedPoints.Incidence.BinaryCoverCellAcyclic
import BPFixedPoints.Incidence.BinaryCoverCellCoverAugmentation
import BPFixedPoints.Incidence.SchemeModuleCellSections
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity

/-! # Actual cohomology from the original finite cubical cell resolution

The original cell complex, original augmentation and actual term Ext
vanishing compute actual sheaf cohomology in every positive degree.
The comparison retains the original Yoneda connecting classes and original
geometric scalar action. The original state complex comparison is separate.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
noncomputable local instance actualCubicalHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- Canonical original syzygies of the original positively exact cubical cell sheaf complex. -/
noncomputable abbrev cubicalTower := complexTower (sheafComplex U) (sheafComplex_exact U)

/-- Original cubical Hom cohomology in degree `n+1`, modulo its original boundary image. -/
noncomputable abbrev cubicalCohomology
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :=
  (cubicalTower U).cohomology F n

/-- The original cubical Hom cohomology computes actual sheaf cohomology in every positive degree. -/
noncomputable def finiteCubicalActualEquiv
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    cubicalCohomology U F n ≃+ F.H (n+1) := by
  letI := augmentation_epi U hcover
  exact (augmentedComplexExtEquiv _ F (sheafComplex_exact U)
    (augmentation U) (augmentation_zero U) (augmentation_exact U) ha n).trans
      (localSheafTopEquiv F (n+1))

/-- Every original class maps by its specified original iterated connecting class and original augmentation. -/
theorem finiteCubicalActualEquiv_mk
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ)
    (x : (cubicalTower U).cycles F (n+1)) :
    letI := augmentation_epi U hcover
    finiteCubicalActualEquiv U F hcover ha n (QuotientAddGroup.mk x) =
      localSheafTopEquiv F (n+1)
        ((Ext.mk₀ (complexAugmentationIso _ (augmentation U) (augmentation_zero U)
          (augmentation_exact U)).inv).comp
            ((cubicalTower U).cocycleComparison F (n+1) x) (zero_add (n+1))) := by
  letI := augmentation_epi U hcover
  rfl

/-- The original comparison preserves all original morphisms of coefficient sheaves. -/
theorem finiteCubicalActualEquiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (g : F ⟶ G)
    (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (haF : ComplexAcyclicAgainst (sheafComplex U) F)
    (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (n : ℕ) (x : cubicalCohomology U F n) :
    finiteCubicalActualEquiv U G hcover haG n ((cubicalTower U).mapCohomology g n x) =
      Sheaf.H.map g (n+1) (finiteCubicalActualEquiv U F hcover haF n x) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv G (n+1)
    (augmentedComplexExtEquiv _ G _ _ _ _ _ n ((cubicalTower U).mapCohomology g n x)) = _
  rw [augmentedComplexExtEquiv_postcomp]
  exact localSheafTopEquiv_naturality g (n+1) _

end BPFixedPoints.SheafTools.BinaryCells

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open SheafTools.BinaryCells ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1400000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → X.Opens)
noncomputable local instance geometricCubicalHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- Original geometric postcomposition defines the original cubical cohomology action before comparison. -/
@[instance_reducible] noncomputable def schemeBaseCubicalModule (n : ℕ) :
    Module R (cubicalCohomology U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :=
  schemeBaseResolutionCohomologyModule f M (cubicalTower U) n

/-- The specified original cubical comparison is linear for the original geometric actions. -/
noncomputable def schemeBaseFiniteCubicalActualLinearEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (n : ℕ) :
    letI := schemeBaseCubicalModule f M U n
    letI := schemeBaseCohomologyModule f M (n+1)
    cubicalCohomology U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) := by
  letI := augmentation_epi U hcover
  exact (schemeBaseAugmentedExtLinearEquiv f M _ (sheafComplex_exact U)
    (augmentation U) (augmentation_zero U) (augmentation_exact U) ha n).trans
      (schemeBaseLocalTopLinearEquiv f M (n+1))

/-- Linearization retains the specified original additive comparison and its specified original representatives. -/
theorem schemeBaseFiniteCubicalActualLinearEquiv_toAddEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ b, chartOpen U b)
    (ha : ComplexAcyclicAgainst (sheafComplex U) ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (n : ℕ) :
    letI := schemeBaseCubicalModule f M U n
    letI := schemeBaseCohomologyModule f M (n+1)
    (schemeBaseFiniteCubicalActualLinearEquiv f M U hcover ha n).toAddEquiv =
      finiteCubicalActualEquiv U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hcover ha n := rfl

end BPFixedPoints.SchemeTools
