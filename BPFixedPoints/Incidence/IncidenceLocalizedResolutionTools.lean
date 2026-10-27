import BPFixedPoints.Incidence.ResolutionDepth
import BPFixedPoints.Incidence.IncidencePrimeDepthTools
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Localization.Finiteness

/-! # Depth bounds from localized finite free resolutions

General tools for the localization argument of `supp:cm-localization`. Depth is Mathlib's Ext
depth `ModuleCat.depth` (with `IsLocalRing.depth` for the maximal ideal of a local ring).

Proved here:
* a finite free module has depth at least the depth of the ring, for every test module
  (`depth_self_le_depth_free`), by the depth lemma (Stacks 00LX) for split sequences
  `0 → R → R × Rⁿ → Rⁿ → 0`;
* the depth lemma along the syzygies of a finite free resolution of length ℓ gives
  depth_N M ≥ depth_N R − ℓ for every test module N
  (`depth_sub_length_le_of_finite_free_resolution`), in particular
  depth_A M ≥ depth A − ℓ over a local ring A
  (`localDepth_sub_length_le_of_finite_free_resolution`);
* localization at a submonoid keeps the localized terms finite free and the localized complex
  exact, so the same bound holds for S⁻¹M over S⁻¹R (`depth_sub_length_le_localizedModule`), at a
  prime p over the local ring R_p (`localizedDepth_sub_length_le`), and, when every prime
  localization of R has depth equal to its dimension (`PrimeDimRegular`, e.g. a polynomial ring
  over a field), in the form depth_{R_p} M_p ≥ ht p − ℓ (`height_sub_length_le_localizedDepth`);
* over a Noetherian local ring, a nonzero finite module has depth at most its support dimension
  (`localDepth_le_supportDim`).

Not treated: resolutions by projective modules that are not finite free, and the
Auslander–Buchsbaum equality depth M + pd M = depth A (only the inequality from a given
resolution is proved).
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

/-- The depth lemma for the split exact sequence `0 → P → P × Q → Q → 0`. -/
theorem depth_inf_le_depth_prod (N : ModuleCat.{u} R) (P Q : Type u) [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] :
    N.depth (ModuleCat.of R P) ⊓ N.depth (ModuleCat.of R Q) ≤
      N.depth (ModuleCat.of R (P × Q)) := by
  have hs := ModuleCat.depth_min_fst_trd_le_snd_right N (LinearMap.snd R P Q).shortComplexKer
    (LinearMap.shortExact_shortComplexKer LinearMap.snd_surjective)
  let e : LinearMap.ker (LinearMap.snd R P Q) ≃ₗ[R] P :=
    (LinearEquiv.ofEq _ _ (LinearMap.ker_snd R P Q)).trans
      (LinearEquiv.ofInjective (LinearMap.inl R P Q) LinearMap.inl_injective).symm
  rwa [ModuleCat.depth_eq_of_iso_right N e.toModuleIso] at hs

/-- A standard free module of finite rank has depth at least the depth of the ring. -/
theorem depth_self_le_depth_pi_fin (N : ModuleCat.{u} R) :
    ∀ n : ℕ, N.depth (ModuleCat.of R R) ≤ N.depth (ModuleCat.of R (Fin n → R))
  | 0 => by
    rw [ModuleCat.depth_eq_top_of_subsingleton N (ModuleCat.of R (Fin 0 → R))]
    exact le_top
  | n + 1 => by
    have h := depth_inf_le_depth_prod N R (Fin n → R)
    rw [ModuleCat.depth_eq_of_iso_right N
      (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).toModuleIso] at h
    exact le_trans (le_inf le_rfl (depth_self_le_depth_pi_fin N n)) h

/-- A finite free module has depth at least the depth of the ring. -/
theorem depth_self_le_depth_free (N : ModuleCat.{u} R) (F : Type u) [AddCommGroup F]
    [Module R F] [Module.Free R F] [Module.Finite R F] :
    N.depth (ModuleCat.of R R) ≤ N.depth (ModuleCat.of R F) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton F := Module.subsingleton R F
    rw [ModuleCat.depth_eq_top_of_subsingleton N (ModuleCat.of R F)]
    exact le_top
  · rw [ModuleCat.depth_eq_of_iso_right N (Module.finBasis R F).equivFun.toModuleIso]
    exact depth_self_le_depth_pi_fin N _

/-- The depth lemma along the syzygies of a finite free resolution: if `M` has a resolution of
length `ℓ` by finite free modules, then `depth_N M ≥ depth_N R − ℓ` for every test module `N`. -/
theorem depth_sub_length_le_of_finite_free_resolution (N : ModuleCat.{u} R) (ℓ : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    [∀ p, Module.Free R (F p)] [∀ p, Module.Finite R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (htop : Subsingleton (F (ℓ + 1))) :
    N.depth (ModuleCat.of R R) - ℓ ≤ N.depth (ModuleCat.of R M) := by
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases Nat.eq_zero_or_pos a with rfl | hapos
  · simp
  have hle : ((a + ℓ : ℕ) : ℕ∞) ≤ N.depth (ModuleCat.of R R) := by
    generalize N.depth (ModuleCat.of R R) = D at ha ⊢
    induction D using ENat.recTopCoe with
    | top => exact le_top
    | coe k =>
      rw [← ENat.natCast_sub] at ha
      have hk : a ≤ k - ℓ := by exact_mod_cast ha
      exact_mod_cast (by omega : a + ℓ ≤ k)
  exact depth_ge_of_finite_exact N ℓ a F D ε hε hzero hex
    (fun p _ => hle.trans (depth_self_le_depth_free N (F p))) htop

/-- Local form: over a local ring `A`, a module with a finite free resolution of length `ℓ` has
depth at least `depth A − ℓ`. -/
theorem localDepth_sub_length_le_of_finite_free_resolution [IsLocalRing R] (ℓ : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    [∀ p, Module.Free R (F p)] [∀ p, Module.Finite R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (htop : Subsingleton (F (ℓ + 1))) :
    IsLocalRing.depth (ModuleCat.of R R) - ℓ ≤ IsLocalRing.depth (ModuleCat.of R M) :=
  depth_sub_length_le_of_finite_free_resolution _ ℓ F D ε hε hzero hex htop

section Localization

/-- Localization at a submonoid carries an exact pair `range f = ker g` to an exact pair of
localized maps over the localized ring. -/
theorem localizedModule_map_range_eq_ker (S : Submonoid R) {P Q T : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q] [AddCommGroup T] [Module R T]
    (f : P →ₗ[R] Q) (g : Q →ₗ[R] T) (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (LocalizedModule.map S f) = LinearMap.ker (LocalizedModule.map S g) := by
  have hl : Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
    LocalizedModule.map_exact S f g (LinearMap.exact_iff.mpr h.symm)
  exact (LinearMap.exact_iff.mp hl).symm

/-- The depth bound after localizing a finite free resolution at a submonoid `S`: the localized
terms form a finite free resolution of `S⁻¹M` over `S⁻¹R` of the same length. -/
theorem depth_sub_length_le_localizedModule (S : Submonoid R)
    (N : ModuleCat.{u} (Localization S)) (ℓ : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    [∀ p, Module.Free R (F p)] [∀ p, Module.Finite R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (htop : Subsingleton (F (ℓ + 1))) :
    N.depth (ModuleCat.of (Localization S) (Localization S)) - ℓ ≤
      N.depth (ModuleCat.of (Localization S) (LocalizedModule S M)) := by
  have : ∀ p, Module.Free (Localization S) (LocalizedModule S (F p)) := fun p =>
    Module.free_of_isLocalizedModule S (LocalizedModule.mkLinearMap S (F p))
  exact depth_sub_length_le_of_finite_free_resolution N ℓ (fun p => LocalizedModule S (F p))
    (fun p => LocalizedModule.map S (D p)) (LocalizedModule.map S ε)
    (LocalizedModule.map_surjective S ε hε) (localizedModule_map_range_eq_ker S _ _ hzero)
    (fun p => localizedModule_map_range_eq_ker S _ _ (hex p)) inferInstance

/-- At a prime `p`, the localized module has depth at least `depth R_p − ℓ` over the local ring
`R_p`. -/
theorem localizedDepth_sub_length_le (p : Ideal R) [p.IsPrime] (ℓ : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    [∀ p, Module.Free R (F p)] [∀ p, Module.Finite R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (htop : Subsingleton (F (ℓ + 1))) :
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) - ℓ ≤
      IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) :=
  depth_sub_length_le_localizedModule p.primeCompl _ ℓ F D ε hε hzero hex htop

/-- If every prime localization of a Noetherian ring `R` has depth equal to its dimension
(`PrimeDimRegular`, e.g. a polynomial ring over a field), then localizing a finite free resolution
of length `ℓ` at a prime `p` gives `depth_{R_p} M_p ≥ ht p − ℓ`. -/
theorem height_sub_length_le_localizedDepth [IsNoetherianRing R] (hR : PrimeDimRegular R)
    (p : Ideal R) [p.IsPrime] (ℓ : ℕ)
    (F : ℕ → Type u) [∀ p, AddCommGroup (F p)] [∀ p, Module R (F p)]
    [∀ p, Module.Free R (F p)] [∀ p, Module.Finite R (F p)]
    (D : ∀ p, F (p + 1) →ₗ[R] F p)
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hε : Function.Surjective ε)
    (hzero : LinearMap.range (D 0) = LinearMap.ker ε)
    (hex : ∀ p, LinearMap.range (D (p + 1)) = LinearMap.ker (D p))
    (htop : Subsingleton (F (ℓ + 1))) :
    p.height - ℓ ≤
      IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) := by
  have hd : IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) =
      p.height := by
    have h := hR.depth_eq p
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at h
    exact_mod_cast h
  rw [← hd]
  exact localizedDepth_sub_length_le p ℓ F D ε hε hzero hex htop

end Localization

/-- Over a Noetherian local ring, a nonzero finite module has depth at most its support
dimension. -/
theorem localDepth_le_supportDim {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] :
    (IsLocalRing.depth (ModuleCat.of A M) : WithBot ℕ∞) ≤ Module.supportDim A M := by
  have hlt : Module.supportDim A M < ⊤ :=
    (Module.supportDim_le_ringKrullDim A M).trans_lt ringKrullDim_lt_top
  obtain ⟨n, hn⟩ := WithBot.ne_bot_iff_exists.mp (Module.supportDim_ne_bot_of_nontrivial A M)
  have hnt : n ≠ ⊤ := by
    rintro rfl
    rw [← hn] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨d, rfl⟩ := ENat.ne_top_iff_exists.mp hnt
  have hproper : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) < ⊤ :=
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).lt_top'
  have h := depth_le_of_supportDim_le (IsLocalRing.maximalIdeal A) (ModuleCat.of A M) hproper d
    (le_of_eq hn.symm)
  rw [← hn]
  exact_mod_cast h

end BPFixedPoints.ResolutionTools
