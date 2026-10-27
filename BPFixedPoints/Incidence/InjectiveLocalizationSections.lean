import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.RingTheory.Noetherian.Defs

/-! # Principal-localization sections of injective modules

Over a Noetherian ring, every section of a principal localization of an
injective module comes from the original module. The proof uses the native
stabilization theorem for kernels and the injective extension property.
-/

namespace BPFixedPoints.SheafTools
open Filter

universe u v w

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
    {I : Type v} {N : Type w} [Small.{v} R] [AddCommGroup I] [Module R I] [Module.Injective R I]
    [AddCommGroup N] [Module R N]

/-- The original map to any principal localization of an injective module is surjective. -/
theorem injective_localizationAway_surjective (r : R) (l : I →ₗ[R] N)
    [IsLocalizedModule.Away r l] : Function.Surjective l := by
  intro y
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj l r y
  let f : Module.End R R := LinearMap.mulLeft R r
  obtain ⟨k, hk, hnk⟩ := ((f.eventually_disjoint_ker_pow_range_pow).and
    (eventually_ge_atTop n)).exists
  let P := LinearMap.range (f ^ k)
  let a : P →ₗ[R] R := (f ^ n).domRestrict P
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro z hz
    change z = 0
    apply Subtype.ext
    change (z : R) = 0
    have hz' : (f ^ n) (z : R) = 0 := hz
    have hm : (z : R) ∈ LinearMap.ker (f ^ k) :=
      Module.End.pow_map_zero_of_le hnk hz'
    exact hk.le_bot ⟨hm, z.property⟩
  let g : P →ₗ[R] I := LinearMap.smulRight P.subtype x
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R I P R a ha g
  have hlin (q : R) : h q = q • h 1 := by
    simpa only [smul_eq_mul, mul_one] using h.map_smul q (1 : R)
  let z : P := ⟨(f ^ k) 1, ⟨1, rfl⟩⟩
  have he := congrArg l (LinearMap.congr_fun hh z)
  change l (h ((f ^ n) ((f ^ k) 1))) = l (((f ^ k) 1) • x) at he
  simp only [f, LinearMap.pow_mulLeft, LinearMap.mulLeft_apply, mul_one] at he
  rw [hlin] at he
  simp only [map_smul] at he
  refine ⟨h 1, ?_⟩
  apply IsLocalizedModule.smul_injective l (⟨r ^ (k+n), k+n, rfl⟩ : Submonoid.powers r)
  change r ^ (k+n) • l (h 1) = r ^ (k+n) • y
  calc
    r ^ (k+n) • l (h 1) = r ^ k • l x := by
      simpa only [pow_add, mul_smul, smul_comm (r ^ n) (r ^ k)] using he
    _ = r ^ (k+n) • y := by rw [← hx, ← mul_smul, ← pow_add]

end BPFixedPoints.SheafTools
