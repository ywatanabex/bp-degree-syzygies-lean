import BPFixedPoints.Incidence.BinaryCoverStandardCup

/-! # Naturality of the cup in the pairing

Two original section pairings b : F × G → H and b₁ : F₁ × G₁ → H₁ that are
compatible on sections with sheaf morphisms f : F → F₁, g : G → G₁ and
k : H → H₁ have compatible actual sheaf pairings. The original cell cup,
the original quotient cup, the native comparison and the standard product
on actual cohomology are then natural for (f, g, k). This is used to
compute products on finite biproducts summand by summand.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.MonoidalCategory HomologicalComplex
open TopologicalSpace Opposite ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
noncomputable section
variable {T : Type} [TopologicalSpace T]
variable {F G H F₁ G₁ H₁ : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}}
variable (b : SectionPairing F G H) (b₁ : SectionPairing F₁ G₁ H₁)
variable (f : F ⟶ F₁) (g : G ⟶ G₁) (k : H ⟶ H₁)

/-- Compatibility of two section pairings with three sheaf morphisms. -/
def SectionPairing.Compatible : Prop :=
  ∀ (W : Opens T) (x : F.obj.obj (op W)) (y : G.obj.obj (op W)),
    b₁.pairing W (f.hom.app (op W) x) (g.hom.app (op W) y) = k.hom.app (op W) (b.pairing W x y)

variable {b b₁ f g k}

/-- Compatible section pairings have compatible actual sheaf pairings. -/
theorem SectionPairing.Compatible.sheafMap (h : SectionPairing.Compatible b b₁ f g k) :
    (f ⊗ₘ g) ≫ b₁.sheafMap = b.sheafMap ≫ k := by
  apply sheafTensor_hom_ext
  intro W x y
  change b₁.sheafMap.hom.app (op W) ((f ⊗ₘ g).hom.app (op W) (sheafPureSection F G W x y)) =
    k.hom.app (op W) (b.sheafMap.hom.app (op W) (sheafPureSection F G W x y))
  rw [sheafPureSection_map,SectionPairing.sheafMap_pure,SectionPairing.sheafMap_pure]
  exact h W x y

variable {V : Type} [Fintype V] [DecidableEq V] (U : V → Fin 2 → Opens T)

/-- The original cell cup is natural for compatible pairings. -/
theorem actualCellCupAt_natural (h : SectionPairing.Compatible b b₁ f g k) (n i j : ℕ)
    (x : (sheafComplex U).X i ⟶ F) (y : (sheafComplex U).X j ⟶ G) :
    actualCellCupAt U b₁ n i j (x ≫ f) (y ≫ g) = actualCellCupAt U b n i j x y ≫ k := by
  simp only [actualCellCupAt,actualTensorCochain,Category.assoc]
  rw [← tensorHom_comp_tensorHom_assoc,h.sheafMap]

/-- The original quotient cup is natural for compatible pairings. -/
theorem cubicalCohomologyCupAt_natural (h : SectionPairing.Compatible b b₁ f g k) (n i j : ℕ)
    (x : cubicalCohomologyAt U F i) (y : cubicalCohomologyAt U G j) :
    cubicalCohomologyCupAt U b₁ n i j ((cubicalTower U).mapAt f i x) ((cubicalTower U).mapAt g j y) =
      (cubicalTower U).mapAt k n (cubicalCohomologyCupAt U b n i j x y) := by
  obtain ⟨x,rfl⟩ := (cubicalTower U).classAt_surjective F i x
  obtain ⟨y,rfl⟩ := (cubicalTower U).classAt_surjective G j y
  rw [ExactTower.mapAt_class,ExactTower.mapAt_class,cubicalCohomologyCupAt_class,
    cubicalCohomologyCupAt_class,ExactTower.mapAt_class]
  congr 1
  apply Subtype.ext
  exact actualCellCupAt_natural U h n i j x.val y.val

local instance standardCupNaturalHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance standardCupNaturalDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasDerivedCategory.standard _

/-- The native comparison is natural in the target sheaf, with no acyclicity hypothesis. -/
theorem nativeCubicalComparison_postcomp (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
    {K L : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (m : K ⟶ L) (n : ℕ)
    (z : cubicalCohomologyAt U K n) :
    nativeCubicalComparison U L hcover n ((cubicalTower U).mapAt m n z) =
      Sheaf.H.map m n (nativeCubicalComparison U K hcover n z) := by
  have := augmentation_epi U hcover
  obtain ⟨z,rfl⟩ := (cubicalTower U).classAt_surjective K n z
  rw [ExactTower.mapAt_class]
  change localSheafTopEquiv L n (nativeCohomologyAtComparison (sheafComplex U) (augmentation U)
      (augmentation_zero U) (augmentation_exact U) (sheafComplex_exact U) L n
        ((cubicalTower U).classAt L n ((cubicalTower U).mapCycles m n z))) =
    Sheaf.H.map m n (localSheafTopEquiv K n (nativeCohomologyAtComparison (sheafComplex U) (augmentation U)
      (augmentation_zero U) (augmentation_exact U) (sheafComplex_exact U) K n
        ((cubicalTower U).classAt K n z)))
  rw [nativeCohomologyAtComparison_class,nativeCohomologyAtComparison_class]
  rw [show (cubicalTower U).mapCycles m n z =
    (complexTower (sheafComplex U) (sheafComplex_exact U)).mapCycles m n z from rfl,
    nativeCycleComparison_postcomp]
  exact localSheafTopEquiv_naturality m n _

/-- The standard product on actual cohomology is natural for compatible pairings. -/
theorem actualStandardClassCup_natural (hcover : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
    (h : SectionPairing.Compatible b b₁ f g k)
    (haF : ComplexAcyclicAgainst (sheafComplex U) F) (haG : ComplexAcyclicAgainst (sheafComplex U) G)
    (haF₁ : ComplexAcyclicAgainst (sheafComplex U) F₁) (haG₁ : ComplexAcyclicAgainst (sheafComplex U) G₁)
    (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hcover b₁ haF₁ haG₁ i j (Sheaf.H.map f i a) (Sheaf.H.map g j c) =
      Sheaf.H.map k (i+j) (actualStandardClassCup U hcover b haF haG i j a c) := by
  obtain ⟨x,rfl⟩ := (nativeCubicalComparison_bijective U F hcover haF i).surjective a
  obtain ⟨y,rfl⟩ := (nativeCubicalComparison_bijective U G hcover haG j).surjective c
  rw [← nativeCubicalComparison_postcomp,← nativeCubicalComparison_postcomp,
    actualStandardClassCup_apply,actualStandardClassCup_apply,actualStandardClassProduct_native,
    actualStandardClassProduct_native,actualNativeClassCup_quotient,actualNativeClassCup_quotient,
    cubicalCohomologyCupAt_natural U h,nativeCubicalComparison_postcomp,Units.smul_def,Units.smul_def,
    map_zsmul]

end
end BPFixedPoints.SheafTools.BinaryCells
