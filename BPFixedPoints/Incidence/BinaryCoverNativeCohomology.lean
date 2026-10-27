import BPFixedPoints.Incidence.ResolutionNativeAllYoneda
import BPFixedPoints.Incidence.ResolutionNativeYonedaSignFormula
import BPFixedPoints.Incidence.BinaryCoverNativeCupRoofs
import BPFixedPoints.Incidence.FiniteCubicalCohomologyDegree

/-! # All original cubical Hom quotients retain their native Ext roofs

The map is independently specified by the original native augmentation
roof and the original comparison at the terminal open. Its sign and
bijectivity follow from the original iterated Yoneda comparison.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
local instance nativeCubicalAllHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance nativeCubicalAllDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _
variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
variable (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)

/-- The independently specified original native roof on the original cubical Hom quotient in every degree. -/
def nativeCubicalComparison (n : ℕ) : cubicalCohomologyAt U F n →+ F.H n := by
  letI := augmentation_epi U hcover
  exact (localSheafTopEquiv F n).toAddMonoidHom.comp
    (nativeCohomologyAtComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F n)

/-- Degree zero retains the original augmentation-only comparison without any relative acyclicity hypothesis. -/
theorem nativeCubicalComparison_zero (x : cubicalCohomologyAt U F 0) :
    nativeCubicalComparison U F hcover 0 x = finiteCubicalActualZeroEquiv U F hcover x := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv F 0
    (nativeCycleComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F 0 x) = _
  rw [nativeCycleComparison_zero_yoneda]
  rfl

/-- Every original cubical class has its original actual Yoneda image multiplied by the accumulated native cone sign. -/
theorem nativeCubicalComparison_yoneda (ha : ComplexAcyclicAgainst (sheafComplex U) F)
    (n : ℕ) (x : cubicalCohomologyAt U F n) :
    nativeCubicalComparison U F hcover n x =
      nativeYonedaSign n • finiteCubicalActualAtEquiv U F hcover ha n x := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv F n
    (nativeCohomologyAtComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F n x) = _
  have h := nativeCohomologyAtComparison_yoneda (sheafComplex U) (sheafComplex_exact U)
    (augmentation U) (augmentation_zero U) (augmentation_exact U) F ha n x
  refine (congrArg (localSheafTopEquiv F n) h).trans ?_
  change localSheafTopEquiv F n (nativeYonedaSign n • _) =
    nativeYonedaSign n • localSheafTopEquiv F n _
  exact map_zsmul (localSheafTopEquiv F n) (nativeYonedaSign n : ℤ) _

/-- Original relative term acyclicity makes the specified native quotient comparison bijective in every degree. -/
theorem nativeCubicalComparison_bijective (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    Function.Bijective (nativeCubicalComparison U F hcover n) := by
  letI := augmentation_epi U hcover
  exact (localSheafTopEquiv F n).bijective.comp
    (nativeCohomologyAtComparison_bijective (sheafComplex U) (sheafComplex_exact U)
      (augmentation U) (augmentation_zero U) (augmentation_exact U) F ha n)

/-- The original native augmentation roof is an additive equivalence on the original Hom quotient itself. -/
def nativeCubicalEquiv (ha : ComplexAcyclicAgainst (sheafComplex U) F) (n : ℕ) :
    cubicalCohomologyAt U F n ≃+ F.H n :=
  AddEquiv.ofBijective (nativeCubicalComparison U F hcover n)
    (nativeCubicalComparison_bijective U F hcover ha n)

/-- Every original representative retains exactly its actual derived augmentation denominator, cocycle and native single shift. -/
theorem nativeCubicalComparison_representative (n : ℕ) (x : (cubicalTower U).cycles F n) :
    nativeCubicalComparison U F hcover n ((cubicalTower U).classAt F n x) =
      localSheafTopEquiv F n (Ext.homEquiv.symm
        (actualCellNativeRoof U hcover n x.val (by
          have h : (cubicalTower U).differential n ≫ x.val=0 := x.property
          simpa only [complexTower_differential] using h) ≫
            ((DerivedCategory.singleFunctors _).shiftIso (n : ℤ) (-(n : ℤ)) 0 (by omega)).inv.app F)) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv F n
    (nativeCohomologyAtComparison (sheafComplex U) (augmentation U) (augmentation_zero U)
      (augmentation_exact U) (sheafComplex_exact U) F n ((cubicalTower U).classAt F n x)) = _
  rw [nativeCohomologyAtComparison_class]
  rfl

/-- The actual accumulated sign on every original quotient class is the sign of its triangular cochain degree. -/
theorem nativeCubicalComparison_triangular (ha : ComplexAcyclicAgainst (sheafComplex U) F)
    (n : ℕ) (x : cubicalCohomologyAt U F n) :
    nativeCubicalComparison U F hcover n x =
      ((n*(n+1)/2 : ℕ) : ℤ).negOnePow • finiteCubicalActualAtEquiv U F hcover ha n x := by
  rw [nativeCubicalComparison_yoneda,nativeYonedaSign_eq]

end
end BPFixedPoints.SheafTools.BinaryCells
