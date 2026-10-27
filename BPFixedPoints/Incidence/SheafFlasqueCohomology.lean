import BPFixedPoints.Incidence.SheafInjectiveFlasque
import BPFixedPoints.Incidence.SheafTerminalCohomology
import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences

/-! # Flasque sheaves have no positive Ext-defined cohomology

The proof uses Mathlib's native injective presentations, exact Ext sequence,
and its two flasque short-exact-sequence lemmas. The local groups are the
original Ext groups corepresented by free open sheaves, in every degree.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {T : Type} [TopologicalSpace T]
noncomputable local instance flasqueCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- Local degree-zero Ext evaluation is natural in the actual abelian sheaf. -/
theorem localSheafH0Equiv_postcomp
    {F G : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (f : F ⟶ G)
    (U : Opens T) (x : F.H' 0 U) :
    localSheafH0Equiv G U (x.comp (Ext.mk₀ f) (add_zero 0)) =
      f.hom.app (op U) (localSheafH0Equiv F U x) := by
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
  rw [Ext.mk₀_comp_mk₀]
  have h₁ : Ext.addEquiv₀ (Ext.mk₀ (g ≫ f)) = g ≫ f := Ext.addEquiv₀.apply_symm_apply _
  have h₂ : Ext.addEquiv₀ (Ext.mk₀ g) = g := Ext.addEquiv₀.apply_symm_apply _
  change freeSheafSectionsEquiv G U (Ext.addEquiv₀ (Ext.mk₀ (g ≫ f))) =
    f.hom.app (op U) (freeSheafSectionsEquiv F U (Ext.addEquiv₀ (Ext.mk₀ g)))
  erw [h₁, h₂]
  rfl

/-- The native injective presentation followed by its genuine cokernel. -/
noncomputable def sheafInjectiveShortComplex
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :
    ShortComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F)) (cokernel.condition _)

/-- The native injective presentation and cokernel form a short exact sequence. -/
theorem sheafInjectiveShortComplex_shortExact
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :
    (sheafInjectiveShortComplex F).ShortExact := by
  dsimp only [sheafInjectiveShortComplex]
  exact { exact := ShortComplex.exact_cokernel (Injective.ι F) }

/-- Every positive local Ext group of a flasque sheaf vanishes on every original open. -/
theorem flasque_local_cohomology_eq_zero (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
      [TopCat.Sheaf.IsFlasque (X := TopCat.of T) F] (U : Opens T)
      (x : F.H' (n+1) U), x = 0 := by
  induction n with
  | zero =>
      intro F hF U x
      let S := sheafInjectiveShortComplex F
      have hS := sheafInjectiveShortComplex_shortExact F
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
      have : TopCat.Sheaf.IsFlasque (X := TopCat.of T) S.X₁ := hF
      have hx : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 :=
        Ext.eq_zero_of_injective _
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
        ((freeOpenAbelianSheaf (T := T)).obj U) hS x hx rfl
      have hepi : Epi (S.g.hom.app (op U)) :=
        TopCat.Sheaf.IsFlasque.epi_of_shortExact (X := TopCat.of T) hS
      obtain ⟨s, hs⟩ := (AddCommGrpCat.epi_iff_surjective _).mp hepi
        (localSheafH0Equiv S.X₃ U y)
      let z := (localSheafH0Equiv S.X₂ U).symm s
      have he : z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
        apply (localSheafH0Equiv S.X₃ U).injective
        rw [localSheafH0Equiv_postcomp]
        simpa only [z, AddEquiv.apply_symm_apply] using hs
      have hy0 : y.comp hS.extClass rfl = 0 := by
        rw [← he]
        simp only [Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      exact hy.symm.trans hy0
  | succ n ih =>
      intro F hF U x
      let S := sheafInjectiveShortComplex F
      have hS := sheafInjectiveShortComplex_shortExact F
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
      have : TopCat.Sheaf.IsFlasque (X := TopCat.of T) S.X₁ := hF
      have : TopCat.Sheaf.IsFlasque (X := TopCat.of T) S.X₂ :=
        injectiveSheaf_isFlasque (Injective.under F)
      have : TopCat.Sheaf.IsFlasque (X := TopCat.of T) S.X₃ :=
        TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ (X := TopCat.of T) hS
      have hx : x.comp (Ext.mk₀ S.f) (add_zero (n+1+1)) = 0 :=
        Ext.eq_zero_of_injective _
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
        ((freeOpenAbelianSheaf (T := T)).obj U) hS x hx rfl
      have hy0 : y = 0 := ih S.X₃ U y
      rw [hy0, Ext.zero_comp] at hy
      exact hy.symm

/-- All positive local Ext groups of a flasque sheaf are subsingletons. -/
theorem flasque_local_cohomology_subsingleton
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    [TopCat.Sheaf.IsFlasque (X := TopCat.of T) F] (U : Opens T) (n : ℕ) :
    Subsingleton (F.H' (n+1) U) :=
  subsingleton_of_forall_eq 0 (flasque_local_cohomology_eq_zero n F U)

/-- Every positive global Ext-defined cohomology class of a flasque sheaf is zero. -/
theorem flasque_global_cohomology_eq_zero
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    [TopCat.Sheaf.IsFlasque (X := TopCat.of T) F] (n : ℕ) (x : F.H (n+1)) : x = 0 := by
  apply (localSheafTopEquiv F (n+1)).symm.injective
  rw [map_zero]
  exact flasque_local_cohomology_eq_zero n F ⊤ _

/-- All positive global Ext-defined cohomology groups of a flasque sheaf are subsingletons. -/
theorem flasque_global_cohomology_subsingleton
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    [TopCat.Sheaf.IsFlasque (X := TopCat.of T) F] (n : ℕ) :
    Subsingleton (F.H (n+1)) :=
  subsingleton_of_forall_eq 0 (flasque_global_cohomology_eq_zero F n)

end BPFixedPoints.SheafTools
