import BPFixedPoints.Incidence.AcyclicResolutionExtCocycles
import BPFixedPoints.Incidence.AcyclicResolutionExtNaturality
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-! # Actual Ext from an augmented exact complex with relatively acyclic terms

The syzygies are the native cokernels of the original differentials. Every
original differential and the original augmentation are retained explicitly.
-/

namespace BPFixedPoints.ExtResolutionTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (P : ChainComplex C ℕ)

/-- The native cokernel of the original incoming differential. -/
noncomputable def complexSyzygy (n : ℕ) : C := cokernel (P.d (n+1) n)

/-- The original outgoing differential descends through its original incoming-differential cokernel. -/
noncomputable def complexSyzygyInclusion (n : ℕ) : complexSyzygy P (n+1) ⟶ P.X n :=
  cokernel.desc (P.d (n+2) (n+1)) (P.d (n+1) n) (P.d_comp_d _ _ _)

/-- The original differential is precisely the specified syzygy projection followed by inclusion. -/
theorem complexSyzygy_factor (n : ℕ) :
    cokernel.π (P.d (n+2) (n+1)) ≫ complexSyzygyInclusion P n = P.d (n+1) n :=
  cokernel.π_desc _ _ _

/-- The specified syzygy inclusion is killed by the original native cokernel projection. -/
theorem complexSyzygy_zero (n : ℕ) :
    complexSyzygyInclusion P n ≫ cokernel.π (P.d (n+1) n) = 0 := by
  apply (cancel_epi (cokernel.π (P.d (n+2) (n+1)))).mp
  rw [← Category.assoc,complexSyzygy_factor,cokernel.condition,comp_zero]

/-- Original positive-degree exactness makes the specified syzygy inclusion mono. -/
theorem complexSyzygyInclusion_mono (n : ℕ) (h : P.ExactAt (n+1)) :
    Mono (complexSyzygyInclusion P n) := by
  have hs := (HomologicalComplex.exactAt_iff' (K := P) (i := n+2) (j := n+1) (k := n)
    (by simp) (by simp)).mp h
  exact hs.mono_cokernelDesc

/-- The original cokernel presentations are short exact, using only original complex exactness. -/
theorem complexSyzygy_shortExact (n : ℕ) (h : P.ExactAt (n+1)) :
    (ShortComplex.mk (complexSyzygyInclusion P n) (cokernel.π (P.d (n+1) n))
      (complexSyzygy_zero P n)).ShortExact := by
  let S := ShortComplex.mk (complexSyzygyInclusion P n) (cokernel.π (P.d (n+1) n))
    (complexSyzygy_zero P n)
  let A := ShortComplex.mk (P.d (n+1) n) (cokernel.π (P.d (n+1) n)) (cokernel.condition _)
  let φ : A ⟶ S :=
    { τ₁ := cokernel.π (P.d (n+2) (n+1))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simpa only [Category.comp_id] using complexSyzygy_factor P n
      comm₂₃ := by simp [S,A] }
  letI : Mono S.f := complexSyzygyInclusion_mono P n h
  letI : Epi S.g := inferInstanceAs (Epi (cokernel.π (P.d (n+1) n)))
  letI : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π (P.d (n+2) (n+1))))
  letI : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 (P.X n)))
  letI : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 (cokernel (P.d (n+1) n))))
  have heA : A.Exact := ShortComplex.exact_of_g_is_cokernel A (cokernelIsCokernel _)
  exact { exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp heA }

/-- The canonical exact tower of the original positively exact complex. -/
noncomputable def complexTower (h : ∀ n, P.ExactAt (n+1)) : ExactTower C where
  K n := complexSyzygy P n
  P n := P.X n
  inclusion n := complexSyzygyInclusion P n
  projection n := cokernel.π (P.d (n+1) n)
  zero n := complexSyzygy_zero P n
  shortExact n := complexSyzygy_shortExact P n (h n)

/-- The canonical tower has exactly the original complex differential, in every degree. -/
theorem complexTower_differential (h : ∀ n, P.ExactAt (n+1)) (n : ℕ) :
    (complexTower P h).differential n = P.d (n+1) n := complexSyzygy_factor P n

/-- The original exact augmentation identifies its target with the original degree-zero cokernel. -/
noncomputable def complexAugmentationIso {A : C} (π : P.X 0 ⟶ A)
    (hz : P.d 1 0 ≫ π = 0) (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π] :
    complexSyzygy P 0 ≅ A := by
  letI : Mono (cokernel.desc (P.d 1 0) π hz) := he.mono_cokernelDesc
  letI : Epi (cokernel.desc (P.d 1 0) π hz) := epi_of_epi_fac (cokernel.π_desc _ _ _)
  letI : IsIso (cokernel.desc (P.d 1 0) π hz) := isIso_of_mono_of_epi _
  exact asIso (cokernel.desc (P.d 1 0) π hz)

/-- The canonical augmentation identification retains the originally specified augmentation itself. -/
theorem complexAugmentationIso_projection {A : C} (π : P.X 0 ⟶ A)
    (hz : P.d 1 0 ≫ π = 0) (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π] :
    cokernel.π (P.d 1 0) ≫ (complexAugmentationIso P π hz he).hom = π := cokernel.π_desc _ _ _

variable [HasExt.{w} C] (Y : C)

/-- Relative term acyclicity is imposed on the original terms of the original complex. -/
def ComplexAcyclicAgainst : Prop := ∀ n k (x : Ext.{w} (P.X n) Y (k+1)), x = 0

/-- The canonical tower uses exactly the supplied actual term Ext vanishings. -/
theorem complexTower_acyclic (h : ∀ n, P.ExactAt (n+1)) (ha : ComplexAcyclicAgainst P Y) :
    (complexTower P h).AcyclicAgainst Y := ha

/-- The original Hom-complex cohomology computes actual Ext of the original augmentation target in every positive degree. -/
noncomputable def augmentedComplexExtEquiv (h : ∀ n, P.ExactAt (n+1))
    {A : C} (π : P.X 0 ⟶ A) (hz : P.d 1 0 ≫ π = 0)
    (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    (ha : ComplexAcyclicAgainst P Y) (n : ℕ) :
    (complexTower P h).cohomology Y n ≃+ Ext.{w} A Y (n+1) :=
  ((complexTower P h).cohomologyEquiv Y n (complexTower_acyclic P Y h ha)).trans
    ((((extFunctor (n+1)).mapIso (complexAugmentationIso P π hz he).symm.op).app Y).addCommGroupIsoToAddEquiv)

/-- Every original cocycle representative uses the original iterated connecting classes and the original augmentation identification. -/
theorem augmentedComplexExtEquiv_mk (h : ∀ n, P.ExactAt (n+1))
    {A : C} (π : P.X 0 ⟶ A) (hz : P.d 1 0 ≫ π = 0)
    (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    (ha : ComplexAcyclicAgainst P Y) (n : ℕ) (x : (complexTower P h).cycles Y (n+1)) :
    augmentedComplexExtEquiv P Y h π hz he ha n (QuotientAddGroup.mk x) =
      (((extFunctor (n+1)).mapIso (complexAugmentationIso P π hz he).symm.op).app Y).hom
        ((complexTower P h).cocycleComparison Y (n+1) x) := rfl

/-- The augmented comparison preserves every original target morphism on all cohomology classes. -/
private theorem extIso_postcomp {A B Y Z : C} (e : A ≅ B) (f : Y ⟶ Z) (n : ℕ)
    (x : Ext.{w} B Y n) :
    (((extFunctor n).mapIso e.op).app Z).hom (x.comp (Ext.mk₀ f) (add_zero n)) =
      ((((extFunctor n).mapIso e.op).app Y).hom x).comp (Ext.mk₀ f) (add_zero n) := by
  change (Ext.mk₀ e.hom).comp (x.comp (Ext.mk₀ f) (add_zero n)) (zero_add n) =
    ((Ext.mk₀ e.hom).comp x (zero_add n)).comp (Ext.mk₀ f) (add_zero n)
  exact (Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ e.hom) x (Ext.mk₀ f) (zero_add n)).symm

/-- The augmented comparison preserves every original target morphism on all cohomology classes. -/
theorem augmentedComplexExtEquiv_postcomp (h : ∀ n, P.ExactAt (n+1))
    {A : C} (π : P.X 0 ⟶ A) (hz : P.d 1 0 ≫ π = 0)
    (he : (ShortComplex.mk (P.d 1 0) π hz).Exact) [Epi π]
    {Z : C} (f : Y ⟶ Z) (haY : ComplexAcyclicAgainst P Y) (haZ : ComplexAcyclicAgainst P Z)
    (n : ℕ) (x : (complexTower P h).cohomology Y n) :
    augmentedComplexExtEquiv P Z h π hz he haZ n ((complexTower P h).mapCohomology f n x) =
      (augmentedComplexExtEquiv P Y h π hz he haY n x).comp (Ext.mk₀ f) (add_zero (n+1)) := by
  change (((extFunctor (n+1)).mapIso (complexAugmentationIso P π hz he).symm.op).app Z).hom
    ((complexTower P h).cohomologyEquiv Z n _ ((complexTower P h).mapCohomology f n x)) = _
  rw [ExactTower.cohomologyEquiv_postcomp]
  exact extIso_postcomp (complexAugmentationIso P π hz he).symm f (n+1) _

end BPFixedPoints.ExtResolutionTools
