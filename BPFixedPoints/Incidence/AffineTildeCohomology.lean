import BPFixedPoints.Incidence.AffineTildeExact
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Positive cohomology vanishing for the original affine tilde sheaves

The original module embeds into a native injective module. Exactness of the
actual abelian tilde functor and flasqueness of injective tilde sheaves give
vanishing by the native long exact cohomology sequence. The degree-zero step
uses the original global section comparison, retaining its naturality.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u
variable (R : CommRingCat.{u})

/-- A surjection of original modules is surjective on actual affine global sections. -/
theorem affineTildeAbelian_map_top_surjective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Surjective f) :
    Function.Surjective (((affineTildeAbelianFunctor R).map f).hom.app (op ⊤)) := by
  intro s
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective s
  obtain ⟨x, hx⟩ := hf y
  refine ⟨(tilde.toOpen M ⊤) x, ?_⟩
  have hn := ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x
  simp only [ConcreteCategory.comp_apply] at hn
  exact hn.trans (by rw [hx, hy])

/-- The native injective embedding followed by its actual module cokernel. -/
noncomputable def affineModuleInjectiveShortComplex (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (Injective.ι M) (cokernel.π (Injective.ι M)) (cokernel.condition _)

/-- The original module embedding and its cokernel form a native short exact sequence. -/
theorem affineModuleInjectiveShortComplex_shortExact (M : ModuleCat.{u} R) :
    (affineModuleInjectiveShortComplex R M).ShortExact where
  exact := ShortComplex.exact_cokernel (Injective.ι M)
  mono_f := by change Mono (Injective.ι M); infer_instance
  epi_g := by change Epi (cokernel.π (Injective.ι M)); infer_instance

/-- The middle module is injective in the native module-theoretic sense. -/
theorem affineModuleInjectiveShortComplex_injective (M : ModuleCat.{u} R) :
    Module.Injective R (affineModuleInjectiveShortComplex R M).X₂ := by
  have : Injective (ModuleCat.of R (affineModuleInjectiveShortComplex R M).X₂) := by
    change Injective (Injective.under M)
    infer_instance
  exact Module.injective_module_of_injective_object R _

end BPFixedPoints.SheafTools

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (R : CommRingCat.{0})
noncomputable local instance affineTildeCohomologyHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{0}) := HasExt.standard _

/-- The actual degree-zero cohomology map retains surjectivity of the original module map. -/
theorem affineTildeAbelian_map_H0_surjective {M N : ModuleCat.{0} R} (f : M ⟶ N)
    (hf : Function.Surjective f) :
    Function.Surjective (Sheaf.H.map ((affineTildeAbelianFunctor R).map f) 0) := by
  intro y
  let eM := Sheaf.H.equiv₀ ((affineTildeAbelianFunctor R).obj M) isTerminalTop
  let eN := Sheaf.H.equiv₀ ((affineTildeAbelianFunctor R).obj N) isTerminalTop
  obtain ⟨s, hs⟩ := affineTildeAbelian_map_top_surjective R f hf (eN y)
  refine ⟨eM.symm s, ?_⟩
  apply eN.injective
  rw [← Sheaf.H.equiv₀_naturality isTerminalTop]
  simpa only [eM, AddEquiv.apply_symm_apply] using hs

variable [IsNoetherianRing R]

/-- Every positive actual affine cohomology class of an arbitrary original module is zero. -/
theorem affineTilde_global_cohomology_eq_zero (n : ℕ) :
    ∀ (M : ModuleCat.{0} R) (x : (affineTildeAbelianSheaf R M).H (n+1)), x = 0 := by
  induction n with
  | zero =>
      intro M x
      let S := affineModuleInjectiveShortComplex R M
      have hS := affineModuleInjectiveShortComplex_shortExact R M
      let T := S.map (affineTildeAbelianFunctor R)
      have hT := affineTildeAbelian_map_shortExact R hS
      have : Module.Injective R S.X₂ := affineModuleInjectiveShortComplex_injective R M
      have hx : Sheaf.H.map T.f 1 x = 0 :=
        affineInjective_global_cohomology_eq_zero R S.X₂ 0 _
      obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hT x hx rfl
      obtain ⟨z, hz⟩ := affineTildeAbelian_map_H0_surjective R S.g hS.moduleCat_surjective_g y
      have hy0 : Sheaf.H.δ hT 0 1 rfl y = 0 := by
        rw [← hz]
        change (z.comp (Ext.mk₀ T.g) (add_zero 0)).comp hT.extClass rfl = 0
        simp only [Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      exact hy.symm.trans hy0
  | succ n ih =>
      intro M x
      let S := affineModuleInjectiveShortComplex R M
      have hS := affineModuleInjectiveShortComplex_shortExact R M
      let T := S.map (affineTildeAbelianFunctor R)
      have hT := affineTildeAbelian_map_shortExact R hS
      have : Module.Injective R S.X₂ := affineModuleInjectiveShortComplex_injective R M
      have hx : Sheaf.H.map T.f (n+1+1) x = 0 :=
        affineInjective_global_cohomology_eq_zero R S.X₂ (n+1) _
      obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hT x hx rfl
      have hy0 : y = 0 := ih S.X₃ y
      rw [hy0, map_zero] at hy
      exact hy.symm

/-- All positive actual cohomology groups of an original affine tilde module are subsingletons. -/
theorem affineTilde_global_cohomology_subsingleton (M : ModuleCat.{0} R) (n : ℕ) :
    Subsingleton ((affineTildeAbelianSheaf R M).H (n+1)) :=
  subsingleton_of_forall_eq 0 (affineTilde_global_cohomology_eq_zero R n M)

/-- The same vanishing holds for local Ext at the whole original affine scheme. -/
theorem affineTilde_top_local_cohomology_eq_zero (M : ModuleCat.{0} R) (n : ℕ)
    (x : (affineTildeAbelianSheaf R M).H' (n+1) ⊤) : x = 0 := by
  apply (localSheafTopEquiv (affineTildeAbelianSheaf R M) (n+1)).injective
  rw [map_zero]
  exact affineTilde_global_cohomology_eq_zero R n M _

/-- Every positive actual cohomology class of a native quasi-coherent affine module is zero. -/
theorem affineQuasicoherent_global_cohomology_eq_zero
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H (n+1)) : x = 0 := by
  have := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let e := (SheafOfModules.toSheaf (Spec R).ringCatSheaf).mapIso (asIso M.fromTildeΓ)
  let h := (Sheaf.functorH (Opens.grothendieckTopology (Spec R)) (n+1)).mapIso e
  have hx := affineTilde_global_cohomology_eq_zero R n _ (h.inv x)
  have he := ConcreteCategory.congr_hom h.inv_hom_id x
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at he
  rw [hx, map_zero] at he
  exact he.symm

/-- Native quasi-coherent affine modules have subsingleton positive cohomology groups. -/
theorem affineQuasicoherent_global_cohomology_subsingleton
    (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ) :
    Subsingleton (((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M).H (n+1)) :=
  subsingleton_of_forall_eq 0 (affineQuasicoherent_global_cohomology_eq_zero R M n)

end BPFixedPoints.SheafTools
