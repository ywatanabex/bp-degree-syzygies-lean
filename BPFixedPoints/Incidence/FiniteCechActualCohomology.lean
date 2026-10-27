import BPFixedPoints.Incidence.FreeAbelianCechAcyclic
import BPFixedPoints.Incidence.FreeAbelianCechAugmentation
import BPFixedPoints.Incidence.SchemeModuleResolutionCohomology
import BPFixedPoints.Incidence.SchemeModuleCohomologyLinearity

/-! # All positive actual cohomology from the original finite tuple Čech resolution

The cover supplies augmented degree-zero exactness by genuine sheaf gluing.
Actual local Ext vanishing supplies relative term acyclicity by native finite
biproducts. All comparisons retain the original differential, augmentation,
extension classes and geometric base action.
-/

namespace BPFixedPoints.SheafTools.FreeCech
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T] {ι : Type} [Fintype ι] (U : ι → Opens T)
noncomputable local instance actualFiniteCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The canonical syzygies of the original finite-cover tuple complex. -/
noncomputable abbrev cechTower :=
  complexTower (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U))
    (freeSheafComplex_exact _ _)

/-- Original finite-cover Hom-complex cohomology in degree `n+1`, with its original boundary image. -/
noncomputable abbrev cechCohomology
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ) :=
  (cechTower U).cohomology F n

/-- Every original finite tuple cocycle computes actual global Ext cohomology in every positive degree. -/
noncomputable def finiteCechActualEquiv
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ i, U i)
    (ha : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ) (x : F.H' (k+1) (intersection U t)), x = 0)
    (n : ℕ) : cechCohomology U F n ≃+ F.H (n+1) := by
  letI := augmentation_epi U hcover
  exact (augmentedComplexExtEquiv _ F (freeSheafComplex_exact _ _)
    (augmentationAt U 0) (augmentation_zero U) (augmentation_exact U hcover)
    (freeSheafComplex_acyclic U F ha) n).trans (localSheafTopEquiv F (n+1))

/-- Each original class is the specified iterated Yoneda connecting class through the specified augmentation. -/
theorem finiteCechActualEquiv_mk
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (hcover : (⊤ : Opens T) ≤ ⨆ i, U i)
    (ha : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ) (x : F.H' (k+1) (intersection U t)), x = 0)
    (n : ℕ) (x : (cechTower U).cycles F (n+1)) :
    letI := augmentation_epi U hcover
    finiteCechActualEquiv U F hcover ha n (QuotientAddGroup.mk x) =
      localSheafTopEquiv F (n+1)
        ((Ext.mk₀ (complexAugmentationIso _ (augmentationAt U 0) (augmentation_zero U)
          (augmentation_exact U hcover)).inv).comp
            ((cechTower U).cocycleComparison F (n+1) x) (zero_add (n+1))) := by
  letI := augmentation_epi U hcover
  rfl

/-- The all-degree comparison is natural for every original morphism of coefficient sheaves. -/
theorem finiteCechActualEquiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (g : F ⟶ G)
    (hcover : (⊤ : Opens T) ≤ ⨆ i, U i)
    (haF : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ) (x : F.H' (k+1) (intersection U t)), x = 0)
    (haG : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ) (x : G.H' (k+1) (intersection U t)), x = 0)
    (n : ℕ) (x : cechCohomology U F n) :
    finiteCechActualEquiv U G hcover haG n ((cechTower U).mapCohomology g n x) =
      Sheaf.H.map g (n+1) (finiteCechActualEquiv U F hcover haF n x) := by
  letI := augmentation_epi U hcover
  change localSheafTopEquiv G (n+1)
    (augmentedComplexExtEquiv _ G _ _ _ _ _ n ((cechTower U).mapCohomology g n x)) = _
  rw [augmentedComplexExtEquiv_postcomp]
  exact localSheafTopEquiv_naturality g (n+1) _

end BPFixedPoints.SheafTools.FreeCech

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open SheafTools.FreeCech ExtResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {X : Scheme.{0}} {R : Type} [CommRing R]
variable (f : X ⟶ Spec (CommRingCat.of R)) (M : X.Modules)
variable {ι : Type} [Fintype ι] (U : ι → X.Opens)
noncomputable local instance geometricFiniteCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- The independently specified original geometric action on finite Čech cohomology. -/
@[instance_reducible] noncomputable def schemeBaseFiniteCechModule (n : ℕ) :
    Module R (cechCohomology U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n) :=
  schemeBaseResolutionCohomologyModule f M (cechTower U) n

/-- Original tuple cohomology computes genuine sheaf cohomology linearly for the original geometric actions. -/
noncomputable def schemeBaseFiniteCechActualLinearEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (ha : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ)
      (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (k+1) (intersection U t)), x = 0)
    (n : ℕ) :
    letI := schemeBaseFiniteCechModule f M U n
    letI := schemeBaseCohomologyModule f M (n+1)
    cechCohomology U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) n ≃ₗ[R]
      Sheaf.H.{1} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (n+1) := by
  letI := augmentation_epi U hcover
  exact (schemeBaseAugmentedExtLinearEquiv f M _ (freeSheafComplex_exact _ _)
    (augmentationAt U 0) (augmentation_zero U) (augmentation_exact U hcover)
    (freeSheafComplex_acyclic U _ ha) n).trans (schemeBaseLocalTopLinearEquiv f M (n+1))

/-- The geometric linear comparison retains the already specified original connecting comparison. -/
theorem schemeBaseFiniteCechActualLinearEquiv_toAddEquiv
    (hcover : (⊤ : X.Opens) ≤ ⨆ i, U i)
    (ha : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ)
      (x : ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).H' (k+1) (intersection U t)), x = 0)
    (n : ℕ) :
    letI := schemeBaseFiniteCechModule f M U n
    letI := schemeBaseCohomologyModule f M (n+1)
    (schemeBaseFiniteCechActualLinearEquiv f M U hcover ha n).toAddEquiv =
      finiteCechActualEquiv U ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) hcover ha n := rfl

/-- At every original tuple section the source scalar is the original geometric coefficient. -/
theorem schemeBaseFiniteCechSection_scalar (q : ℕ) (r : R) (g : freeTerm U q ⟶
    (SheafOfModules.toSheaf X.ringCatSheaf).obj M) (t : Fin (q+1) → ι) :
    let s : Γ(M, intersection U t) := sectionsEquiv U _ q g t
    let sr : Γ(M, intersection U t) := sectionsEquiv U _ q (g ≫ schemeBaseAbelianScalar f M r) t
    sr = schemeBaseCoefficientAt f (intersection U t) r • s := rfl

end BPFixedPoints.SchemeTools
