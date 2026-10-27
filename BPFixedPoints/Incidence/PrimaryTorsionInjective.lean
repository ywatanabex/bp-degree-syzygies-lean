import Mathlib.Algebra.Module.Injective
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.RingTheory.Filtration
import Mathlib.LinearAlgebra.LinearPMap

/-! # Supported torsion in a Noetherian injective module

Mathlib's primary component is the submodule annihilated elementwise by
powers of the original ideal. Artin-Rees and the native injective extension
property show that this submodule is itself injective.
-/

namespace BPFixedPoints.SheafTools
open Submodule
set_option backward.isDefEq.respectTransparency false

universe u v
variable {R : Type u} [CommRing R]
    {I : Type v} [AddCommGroup I] [Module R I]

/-- A finite source has a uniform ideal power annihilating its image in the original torsion part. -/
theorem primaryComponent_finite_image_killed (J : Ideal R)
    {A : Type*} [AddCommGroup A] [Module R A] [Module.Finite R A]
    (g : A →ₗ[R] J.primaryComponent I) :
    ∃ n : ℕ, ∀ (a : A) (r : R), r ∈ J ^ n → r • (g a : I) = 0 := by
  classical
  choose n hn using fun a : A => (J.primaryComponent_mem I (g a : I)).mp (g a).property
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule R A).FG)
  let N := s.sup n
  let g' : A →ₗ[R] I := (J.primaryComponent I).subtype.comp g
  have hle : (⊤ : Submodule R A) ≤ (torsionBySet R I (↑(J ^ N) : Set R)).comap g' := by
    rw [← hs, span_le]
    intro a ha
    apply (mem_torsionBySet_iff _ _).mpr
    rintro ⟨r, hr⟩
    exact ((mem_torsionBySet_iff _ _).mp (hn a))
      ⟨r, Ideal.pow_le_pow_right (Finset.le_sup ha) hr⟩
  refine ⟨N, fun a r hr => ?_⟩
  exact ((mem_torsionBySet_iff _ _).mp (hle (show a ∈ (⊤ : Submodule R A) from mem_top))) ⟨r, hr⟩

variable [IsNoetherianRing R] [Small.{v} R]

/-- The original ideal-supported torsion submodule of an injective module is injective. -/
theorem primaryComponent_injective (J : Ideal R) [Module.Injective R I] :
    Module.Injective R (J.primaryComponent I) := by
  apply Module.Baer.injective
  intro A g
  let g' : A →ₗ[R] I := (J.primaryComponent I).subtype.comp g
  obtain ⟨n, hn⟩ := primaryComponent_finite_image_killed J g
  let K : Submodule R R := g'.ker.map A.subtype
  have hkill : J ^ n • (A : Submodule R R) ≤ K := by
    apply Submodule.smul_le.mpr
    intro r hr a ha
    refine ⟨r • (⟨a, ha⟩ : A), ?_, rfl⟩
    change g' (r • (⟨a, ha⟩ : A)) = 0
    rw [map_smul]
    exact hn ⟨a, ha⟩ r hr
  obtain ⟨k, hk⟩ := J.exists_pow_inf_eq_pow_smul (A : Submodule R R)
  let B : Submodule R R := J ^ (n+k) • ⊤
  have hBA : B ⊓ (A : Submodule R R) ≤ K := by
    dsimp only [B]
    rw [hk (n+k) (Nat.le_add_left k n), Nat.add_sub_cancel_right]
    exact (smul_mono_right (J ^ n) inf_le_right).trans hkill
  let pA : R →ₗ.[R] I := ⟨A, g'⟩
  let pB : R →ₗ.[R] I := ⟨B, 0⟩
  have hc (x : pA.domain) (y : pB.domain) (hxy : (x : R) = y) : pA x = pB y := by
    have hx : (x : R) ∈ K := hBA ⟨hxy ▸ y.property, x.property⟩
    obtain ⟨z, hz, hzx⟩ := hx
    have heq : z = x := Subtype.ext hzx
    change g' z = 0 at hz
    change g' x = 0
    simpa only [heq] using hz
  let p := pA.sup pB hc
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R I p.domain R
    p.domain.subtype p.domain.subtype_injective p.toFun
  have hAP : (A : Submodule R R) ≤ p.domain := le_sup_left
  have hBP : B ≤ p.domain := le_sup_right
  have hA (a : A) : h a = g' a := by
    let z : p.domain := ⟨a, hAP a.property⟩
    have he := LinearMap.congr_fun hh z
    have hp := LinearPMap.sup_apply hc a 0 z (by change (a : R) + 0 = (a : R); exact add_zero _)
    exact he.trans (by simpa only [p, pA, pB, LinearPMap.toFun', LinearMap.zero_apply, add_zero] using hp)
  have hB (b : B) : h b = 0 := by
    let z : p.domain := ⟨b, hBP b.property⟩
    have he := LinearMap.congr_fun hh z
    have hp := LinearPMap.sup_apply hc 0 b z (by change (0 : R) + b = (b : R); exact zero_add _)
    exact he.trans (by simpa only [p, pA, pB, LinearPMap.toFun', LinearMap.zero_apply, map_zero, zero_add] using hp)
  have hmem (q : R) : h q ∈ J.primaryComponent I := by
    apply (J.primaryComponent_mem I (h q)).mpr
    refine ⟨n+k, (mem_torsionBySet_iff _ _).mpr ?_⟩
    rintro ⟨r, hr⟩
    rw [← map_smul]
    exact hB ⟨r • q, Submodule.smul_mem_smul hr (show q ∈ (⊤ : Submodule R R) from mem_top)⟩
  refine ⟨h.codRestrict (J.primaryComponent I) hmem, ?_⟩
  intro r hr
  exact Subtype.ext (hA ⟨r, hr⟩)

end BPFixedPoints.SheafTools
