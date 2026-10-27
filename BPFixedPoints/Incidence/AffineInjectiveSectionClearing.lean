import BPFixedPoints.Incidence.AffineTildeSupportedKernel
import BPFixedPoints.Incidence.SupportedLocalizationExtension
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Clearing sections on arbitrary Noetherian affine opens

The native finite principal cover and original localized values clear a
section vanishing on a principal open by a uniform power. The same actual
sections have no torsion supported in their closed complement.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u
variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R)

/-- A function in the original complement ideal has its principal open inside the original open. -/
theorem affineOpenComplementIdeal_basic_le (U : (Spec R).Opens) (f : R)
    (hf : f ∈ affineOpenComplementIdeal R U) : PrimeSpectrum.basicOpen f ≤ U := by
  intro p hp
  by_contra hpU
  exact (PrimeSpectrum.mem_basicOpen f p).mp hp
    ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hf p hpU)

/-- Actual open sections have no torsion supported in the original closed complement. -/
theorem affineTilde_sections_supported_torsion_zero (U : (Spec R).Opens)
    (s : (structurePresheafInModuleCat R M).obj (op U)) (n : ℕ)
    (hs : ∀ r : R, r ∈ affineOpenComplementIdeal R U ^ n → r • s = 0) : s = 0 := by
  classical
  apply Subtype.ext
  funext p
  have hp : ¬ affineOpenComplementIdeal R U ≤ p.val.asIdeal := by
    intro h
    have hpZ : p.val ∈ PrimeSpectrum.zeroLocus (affineOpenComplementIdeal R U : Set R) := h
    rw [affineOpenComplementIdeal_zeroLocus R U] at hpZ
    exact hpZ p.property
  change ¬ ∀ r : R, r ∈ affineOpenComplementIdeal R U → r ∈ p.val.asIdeal at hp
  obtain ⟨f, hf⟩ := not_forall.mp hp
  obtain ⟨hfJ, hfp⟩ := not_imp.mp hf
  have he := congrArg (fun t => t.val p) (hs (f ^ n) (Ideal.pow_mem_pow hfJ n))
  apply IsLocalizedModule.smul_injective (LocalizedModule.mkLinearMap p.val.asIdeal.primeCompl M)
    (⟨f ^ n, p.val.asIdeal.primeCompl.pow_mem hfp n⟩ : p.val.asIdeal.primeCompl)
  change (f ^ n : R) • s.val p = (f ^ n : R) • (0 : LocalizedModule p.val.asIdeal.primeCompl M)
  change (f ^ n : R) • s.val p = 0 at he
  simpa only [smul_zero] using he

variable [IsNoetherianRing R] [Module.Injective R M]

/-- On a Noetherian affine open, actual vanishing on a contained principal open
is killed by a uniform power of its original defining function. -/
theorem affineInjective_section_power_killed (U : (Spec R).Opens) (f : R)
    (hf : PrimeSpectrum.basicOpen f ≤ U)
    (s : (structurePresheafInModuleCat R M).obj (op U))
    (hs : (structurePresheafInModuleCat R M).map (homOfLE hf).op s = 0) :
    ∃ n : ℕ, f ^ n • s = 0 := by
  classical
  obtain ⟨κ, hκ, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U
    (NoetherianSpace.isCompact (U : Set (Spec R)))
  let : Finite κ := hκ
  have hgi (i : κ) : PrimeSpectrum.basicOpen (g i) ≤ U := by
    rw [hg]
    exact le_iSup (fun i => PrimeSpectrum.basicOpen (g i)) i
  have hlocal (i : κ) : ∃ n : ℕ,
      f ^ n • (structurePresheafInModuleCat R M).map (homOfLE (hgi i)).op s = 0 := by
    obtain ⟨x, hx⟩ := affineInjective_toOpen_surjective R M (g i)
      ((structurePresheafInModuleCat R M).map (homOfLE (hgi i)).op s)
    have hx' : StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (g i)) x =
        (structurePresheafInModuleCat R M).map (homOfLE (hgi i)).op s := hx
    have hz : StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (f * g i)) x = 0 := by
      apply Subtype.ext
      funext p
      have hi := congrArg (fun t => t.val
        ⟨p.val, PrimeSpectrum.basicOpen_mul_le_right f (g i) p.property⟩) hx
      have hfz := congrArg (fun t => t.val
        ⟨p.val, PrimeSpectrum.basicOpen_mul_le_left f (g i) p.property⟩) hs
      exact hi.trans hfz
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers (f * g i))
      (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (f * g i)))).mp hz
    change (f * g i) ^ n • x = 0 at hn
    refine ⟨n, ?_⟩
    apply IsLocalizedModule.smul_injective (StructureSheaf.toOpenₗ R M
      (PrimeSpectrum.basicOpen (g i))) (⟨g i ^ n, n, rfl⟩ : Submonoid.powers (g i))
    have he := congrArg (StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen (g i))) hn
    simpa only [map_smul, map_zero, mul_pow, mul_smul, Submonoid.smul_def,
      smul_comm (f ^ n) (g i ^ n), smul_zero, hx'] using he
  choose n hn using hlocal
  let N := ⨆ i, n i
  refine ⟨N, ?_⟩
  apply Subtype.ext
  funext p
  have hp : p.val ∈ ⨆ i, PrimeSpectrum.basicOpen (g i) := by
    rw [← hg]
    exact p.property
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hp
  have hni : n i ≤ N := le_ciSup (Finite.bddAbove_range _) i
  have he : (structurePresheafInModuleCat R M).map (homOfLE (hgi i)).op (f ^ N • s) = 0 := by
    rw [map_smul, show N = (N - n i) + n i from (Nat.sub_add_cancel hni).symm,
      pow_add, mul_smul, hn i, smul_zero]
  exact congrArg (fun t => t.val ⟨p.val, hi⟩) he

/-- Every actual affine open section clears through the original module by a complement-ideal power. -/
theorem affineInjective_section_denominator_power (U : (Spec R).Opens)
    (s : (structurePresheafInModuleCat R M).obj (op U)) :
    ∃ n : ℕ, affineOpenComplementIdeal R U ^ n ≤
      supportedDenominatorIdeal (StructureSheaf.toOpenₗ R M U) s := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _
    (IsNoetherian.noetherian (affineOpenComplementIdeal R U))
  intro f hfJ
  have hf := affineOpenComplementIdeal_basic_le R U f hfJ
  obtain ⟨x, hx⟩ := affineInjective_toOpen_surjective R M f
    ((structurePresheafInModuleCat R M).map (homOfLE hf).op s)
  let t : (structurePresheafInModuleCat R M).obj (op U) := StructureSheaf.toOpenₗ R M U x
  let d : (structurePresheafInModuleCat R M).obj (op U) := t - s
  have hr : (structurePresheafInModuleCat R M).map (homOfLE hf).op
      (StructureSheaf.toOpenₗ R M U x) =
      StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) x := rfl
  have hx' : StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f) x =
      (structurePresheafInModuleCat R M).map (homOfLE hf).op s := hx
  have hd : (structurePresheafInModuleCat R M).map (homOfLE hf).op d = 0 := by
    dsimp only [d]
    erw [map_sub, hr, hx', sub_self]
  obtain ⟨n, hn⟩ := affineInjective_section_power_killed R M U f hf d hd
  have hn' : f ^ n • t - f ^ n • s = 0 := by
    simpa only [d, smul_sub] using hn
  refine ⟨n, ?_⟩
  change f ^ n • s ∈ (StructureSheaf.toOpenₗ R M U).range
  refine ⟨f ^ n • x, ?_⟩
  exact ((StructureSheaf.toOpenₗ R M U).map_smul (f ^ n) x).trans (sub_eq_zero.mp hn')

end BPFixedPoints.SheafTools
