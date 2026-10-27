import BPFixedPoints.Incidence.AffineTildeStalkComparison
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.Stalks

/-! # Exactness of the original abelian tilde functor

The actual stalk maps are the original localized maps. Mathlib's native
localization exactness and stalk criterion therefore preserve short exact
sequences of original coefficient modules as actual abelian sheaf sequences.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat.Presheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

universe u
variable (R : CommRingCat.{u})

instance affineTildeAbelianFunctor_additive : (affineTildeAbelianFunctor R).Additive := by
  constructor
  intro M N f g
  have h := tilde.map_add f g
  ext U s
  exact congrArg (fun k => (k.val.app U).hom s) h

/-- The original abelian stalk map is injective when the original coefficient map is injective. -/
theorem affineTildeAbelian_stalk_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (p : PrimeSpectrum.Top R) :
    Function.Injective ((stalkFunctor AddCommGrpCat.{u} p).map
      ((affineTildeAbelianFunctor R).map f).hom) := by
  have hi := IsLocalizedModule.map_injective p.asIdeal.primeCompl
    (affineTildeModuleToStalk R M p).hom (affineTildeModuleToStalk R N p).hom f.hom hf
  rw [← affineTildeModuleStalkMap_eq_localized R f p] at hi
  intro x y hxy
  apply (affineTildeModuleStalkIso R M p).injective
  apply hi
  rw [← affineTildeModuleStalkIso_naturality, ← affineTildeModuleStalkIso_naturality, hxy]

/-- The original abelian stalk map is surjective when the original coefficient map is surjective. -/
theorem affineTildeAbelian_stalk_surjective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Surjective f) (p : PrimeSpectrum.Top R) :
    Function.Surjective ((stalkFunctor AddCommGrpCat.{u} p).map
      ((affineTildeAbelianFunctor R).map f).hom) := by
  have hs := IsLocalizedModule.map_surjective p.asIdeal.primeCompl
    (affineTildeModuleToStalk R M p).hom (affineTildeModuleToStalk R N p).hom f.hom hf
  rw [← affineTildeModuleStalkMap_eq_localized R f p] at hs
  intro y
  obtain ⟨x, hx⟩ := hs (affineTildeModuleStalkIso R N p y)
  refine ⟨(affineTildeModuleStalkIso R M p).symm x, ?_⟩
  apply (affineTildeModuleStalkIso R N p).injective
  rw [affineTildeModuleStalkIso_naturality, LinearEquiv.apply_symm_apply]
  exact hx

/-- The original abelian tilde functor preserves native monomorphisms. -/
theorem affineTildeAbelian_map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] :
    Mono ((affineTildeAbelianFunctor R).map f) := by
  apply (TopCat.Presheaf.mono_iff_stalk_mono _).mpr
  intro p
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (affineTildeAbelian_stalk_injective R f ((ModuleCat.mono_iff_injective f).mp inferInstance) p)

/-- The original abelian tilde functor preserves native epimorphisms. -/
theorem affineTildeAbelian_map_epi {M N : ModuleCat.{u} R} (f : M ⟶ N) [Epi f] :
    Epi ((affineTildeAbelianFunctor R).map f) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (locally_surjective_iff_surjective_on_stalks _).mpr
  intro p
  exact affineTildeAbelian_stalk_surjective R f
    ((ModuleCat.epi_iff_surjective f).mp inferInstance) p

/-- The original sheaf stalk sequence is exact whenever the original module sequence is exact. -/
theorem affineTildeAbelian_stalk_exact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.Exact) (p : PrimeSpectrum.Top R) :
    Function.Exact
      ((stalkFunctor AddCommGrpCat.{u} p).map ((affineTildeAbelianFunctor R).map S.f).hom)
      ((stalkFunctor AddCommGrpCat.{u} p).map ((affineTildeAbelianFunctor R).map S.g).hom) := by
  have h := IsLocalizedModule.map_exact p.asIdeal.primeCompl
    (affineTildeModuleToStalk R S.X₁ p).hom (affineTildeModuleToStalk R S.X₂ p).hom
    (affineTildeModuleToStalk R S.X₃ p).hom S.f.hom S.g.hom
    (LinearMap.exact_iff.mpr hS.moduleCat_range_eq_ker.symm)
  rw [← affineTildeModuleStalkMap_eq_localized R S.f p,
    ← affineTildeModuleStalkMap_eq_localized R S.g p] at h
  apply Function.Exact.of_ladder_addEquiv_of_exact'
    (e₁ := (affineTildeModuleStalkIso R S.X₁ p).toAddEquiv)
    (e₂ := (affineTildeModuleStalkIso R S.X₂ p).toAddEquiv)
    (e₃ := (affineTildeModuleStalkIso R S.X₃ p).toAddEquiv)
    (g₁₂ := (affineTildeModuleStalkMap R S.f p).hom.toAddMonoidHom)
    (g₂₃ := (affineTildeModuleStalkMap R S.g p).hom.toAddMonoidHom) (H := h)
  · ext x
    exact (affineTildeModuleStalkIso_naturality R S.f p x).symm
  · ext x
    exact (affineTildeModuleStalkIso_naturality R S.g p x).symm

/-- The original abelian tilde functor preserves exactness of the actual short complex. -/
theorem affineTildeAbelian_map_exact (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact) :
    (S.map (affineTildeAbelianFunctor R)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro p
  rw [ShortComplex.ab_exact_iff_function_exact]
  exact affineTildeAbelian_stalk_exact R S hS p

/-- The original module short exact sequence becomes the actual abelian tilde short exact sequence. -/
theorem affineTildeAbelian_map_shortExact {S : ShortComplex (ModuleCat.{u} R)}
    (hS : S.ShortExact) : (S.map (affineTildeAbelianFunctor R)).ShortExact where
  exact := affineTildeAbelian_map_exact R S hS.exact
  mono_f := by
    have := hS.mono_f
    exact affineTildeAbelian_map_mono R S.f
  epi_g := by
    have := hS.epi_g
    exact affineTildeAbelian_map_epi R S.g

end BPFixedPoints.SheafTools
