import BPFixedPoints.Incidence.ResolutionTools
import Mathlib.RingTheory.Depth.Basic

/-!
# Depth lower bounds from finite augmented exact sequences

Transfer depth bounds of free terms to the augmentation target through short
exact sequences of actual kernels. Use Mathlib's Ext-based definition of depth.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory
set_option backward.isDefEq.respectTransparency false

universe u
variable {R : Type u} [CommRing R]

/-- Surjection to the augmentation kernel induced by the first differential. -/
def exactTailAugmentation {F M : Type u} [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    {A : Type u} [AddCommGroup A] [Module R A]
    (d : F →ₗ[R] A) (ε : A →ₗ[R] M) (he : LinearMap.range d = LinearMap.ker ε) :
    F →ₗ[R] LinearMap.ker ε :=
  d.codRestrict _ (fun x => he ▸ LinearMap.mem_range_self d x)

theorem exactTailAugmentation_surjective {F M A : Type u}
    [AddCommGroup F] [Module R F] [AddCommGroup M] [Module R M]
    [AddCommGroup A] [Module R A]
    (d : F →ₗ[R] A) (ε : A →ₗ[R] M) (he : LinearMap.range d = LinearMap.ker ε) :
    Function.Surjective (exactTailAugmentation d ε he) := by
  intro x
  have hx : x.val ∈ LinearMap.range d := by rw [he]; exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- If every term in a length-r exact sequence has depth at least d+r, the augmentation target has depth at least d. -/
theorem depth_ge_of_finite_exact
    (N : ModuleCat.{u} R) (r d : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (hF : ∀ p ≤ r, ((d + r : ℕ) : ℕ∞) ≤ N.depth (ModuleCat.of R (F p)))
    (htop : Subsingleton (F (r + 1))) :
    (d : ℕ∞) ≤ N.depth (ModuleCat.of R M) := by
  induction r generalizing F M d with
  | zero =>
    have hD : D 0 = 0 := by
      haveI := htop
      ext x
      simp only [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
    have hker : LinearMap.ker ε = ⊥ := by rw [← hzero, hD, LinearMap.range_zero]
    let e := LinearEquiv.ofBijective ε ⟨LinearMap.ker_eq_bot.mp hker, hε⟩
    rw [← ModuleCat.depth_eq_of_iso_right N e.toModuleIso]
    simpa using hF 0 (le_refl _)
  | succ r ih =>
    let ε' := exactTailAugmentation (D 0) ε hzero
    have hε' : Function.Surjective ε' := exactTailAugmentation_surjective (D 0) ε hzero
    have he' : LinearMap.range (D 1) = LinearMap.ker ε' := by
      rw [hex 0]
      ext x
      simp only [LinearMap.mem_ker]
      exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
    have hk : ((d + 1 : ℕ) : ℕ∞) ≤ N.depth (ModuleCat.of R (LinearMap.ker ε)) := by
      apply ih (d + 1) (fun p => F (p + 1)) (fun p => D (p + 1)) ε' hε' he'
        (fun p => hex (p + 1))
      · intro p hp
        simpa only [Nat.add_assoc, Nat.add_comm 1 r] using hF (p + 1) (by omega)
      · exact htop
    have hf : (d : ℕ∞) ≤ N.depth (ModuleCat.of R (F 0)) :=
      (show (d : ℕ∞) ≤ ((d + (r + 1) : ℕ) : ℕ∞) by exact_mod_cast Nat.le_add_right d (r + 1)).trans (hF 0 (by omega))
    have hs := ModuleCat.depth_min_snd_fst_sub_one_le_trd_right N ε.shortComplexKer
      (LinearMap.shortExact_shortComplexKer hε)
    apply le_trans (le_inf hf ?_) hs
    have h := tsub_le_tsub_right hk 1
    simpa using h

end BPFixedPoints.ResolutionTools
