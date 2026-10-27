import BPFixedPoints.Incidence.PrimaryTorsionInjective

/-! # Extending supported-localization sections through an injective module

An injective restriction kernel splits off. The resulting linear section of
the image lets the native injective extension property lift a denominator
ideal. Ideal-power clearing and absence of supported target torsion then
give actual surjectivity of the original map.
-/

namespace BPFixedPoints.SheafTools
open Submodule
set_option backward.isDefEq.respectTransparency false

universe u v w
variable {R : Type u} [CommRing R] {I : Type v} [Small.{v} R]
    [AddCommGroup I] [Module R I] {N : Type w} [AddCommGroup N] [Module R N]

/-- A map with injective kernel has a linear section on its original image. -/
theorem exists_range_section_of_injective_kernel (l : I →ₗ[R] N)
    [Module.Injective R l.ker] :
    ∃ s : l.range →ₗ[R] I, ∀ y : l.range, l (s y) = y := by
  obtain ⟨ρ, hρ⟩ := Module.Injective.extension_property R l.ker l.ker I
    l.ker.subtype l.ker.subtype_injective LinearMap.id
  let q : I →ₗ[R] I := LinearMap.id - l.ker.subtype.comp ρ
  have hq : l.ker ≤ q.ker := by
    intro x hx
    have he := LinearMap.congr_fun hρ (⟨x, hx⟩ : l.ker)
    change ρ x = ⟨x, hx⟩ at he
    change x - (ρ x : I) = 0
    rw [he, sub_self]
  let s : l.range →ₗ[R] I := (l.ker.liftQ q hq).comp l.quotKerEquivRange.symm.toLinearMap
  refine ⟨s, ?_⟩
  rintro ⟨y, x, rfl⟩
  dsimp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change l (x - (ρ x : I)) = l x
  rw [map_sub, (ρ x).property, sub_zero]

/-- Coefficients whose multiple of the target section lifts through the original map. -/
def supportedDenominatorIdeal (l : I →ₗ[R] N) (y : N) : Ideal R :=
  l.range.comap (LinearMap.toSpanSingleton R N y)

/-- Ideal-power clearing lifts an actual section when the original kernel is injective
and the target has no torsion supported in the specified closed complement. -/
theorem supported_localization_surjective (J : Ideal R) (l : I →ₗ[R] N)
    [Module.Injective R I] [Module.Injective R l.ker]
    (hclear : ∀ y : N, ∃ n : ℕ, J ^ n ≤ supportedDenominatorIdeal l y)
    (hzero : ∀ (y : N) (n : ℕ), (∀ r : R, r ∈ J ^ n → r • y = 0) → y = 0) :
    Function.Surjective l := by
  obtain ⟨s, hs⟩ := exists_range_section_of_injective_kernel l
  intro y
  let A := supportedDenominatorIdeal l y
  let g₀ : A →ₗ[R] l.range :=
    ((LinearMap.toSpanSingleton R N y).comp A.subtype).codRestrict l.range (fun a => a.property)
  let g : A →ₗ[R] I := s.comp g₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R I A R A.subtype A.subtype_injective g
  have he (a : A) : (a : R) • l (h 1) = (a : R) • y := by
    have ht := LinearMap.congr_fun hh a
    have hlin : h (a : R) = (a : R) • h 1 := by
      simpa only [smul_eq_mul, mul_one] using h.map_smul (a : R) (1 : R)
    calc
      (a : R) • l (h 1) = l (h (a : R)) := by rw [hlin, map_smul]
      _ = l (s (g₀ a)) := congrArg l ht
      _ = (a : R) • y := hs (g₀ a)
  obtain ⟨n, hn⟩ := hclear y
  have hz : l (h 1) - y = 0 := hzero _ n (fun r hr => by
    rw [smul_sub, he ⟨r, hn hr⟩, sub_self])
  exact ⟨h 1, sub_eq_zero.mp hz⟩

end BPFixedPoints.SheafTools
