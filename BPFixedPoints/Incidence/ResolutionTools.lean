import BPFixedPoints.Incidence.ProjectiveDimensionTools
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Construct projective resolutions from linear maps

Build Mathlib `ProjectiveResolution` from image/kernel equalities of a concrete
linear complex and a surjective augmentation. Require degreewise exactness
explicitly rather than identifying a numerical Betti table with a resolution.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Construct a projective resolution from an exact augmented projective complex. -/
noncomputable def projectiveResolutionOfExact
    (K : ChainComplex C ℕ) (hprojective : ∀ n, Projective (K.X n))
    (X : C) (ε : K.X 0 ⟶ X) (hε : K.d 1 0 ≫ ε = 0)
    (hεepi : Epi ε) (hexact₀ : (ShortComplex.mk _ _ hε).Exact)
    (hexact : ∀ n, K.ExactAt (n + 1)) : ProjectiveResolution X where
  complex := K
  projective := hprojective
  π := (ChainComplex.toSingle₀Equiv K X).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        simpa only [ChainComplex.toSingle₀Equiv_symm_apply_f_zero] using
          (show (ShortComplex.mk _ _ hε).Exact ∧ Epi ε from ⟨hexact₀, hεepi⟩)
      · exact K.shape 0 0 (by simp)
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact hexact n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

@[simp] theorem projectiveResolutionOfExact_complex
    (K : ChainComplex C ℕ) (hprojective : ∀ n, Projective (K.X n))
    (X : C) (ε : K.X 0 ⟶ X) (hε : K.d 1 0 ≫ ε = 0)
    (hεepi : Epi ε) (hexact₀ : (ShortComplex.mk _ _ hε).Exact)
    (hexact : ∀ n, K.ExactAt (n + 1)) :
    (projectiveResolutionOfExact K hprojective X ε hε hεepi hexact₀ hexact).complex = K := rfl

end Abelian

section Linear

variable {R : Type u} [Ring R]
variable (F : ℕ → Type u) [∀ n, AddCommGroup (F n)] [∀ n, Module R (F n)]

/-- Package a family of degree-lowering linear maps as a chain complex. -/
def linearChainComplex (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hsquare : ∀ n, (d n).comp (d (n + 1)) = 0) : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (F n)) (fun n => ModuleCat.ofHom (d n))
    (fun n => ModuleCat.hom_ext (hsquare n))

@[simp] theorem linearChainComplex_X (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hsquare : ∀ n, (d n).comp (d (n + 1)) = 0) (n : ℕ) :
    (linearChainComplex F d hsquare).X n = ModuleCat.of R (F n) := rfl

@[simp] theorem linearChainComplex_d (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hsquare : ∀ n, (d n).comp (d (n + 1)) = 0) (n : ℕ) :
    (linearChainComplex F d hsquare).d (n + 1) n = ModuleCat.ofHom (d n) := by
  exact ChainComplex.of_d (fun n => ModuleCat.of R (F n))
    (fun n => ModuleCat.ofHom (d n)) n

/-- Positive-degree exactness of a linear complex whose images equal kernels. -/
theorem linearChainComplex_exactAt_succ (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hsquare : ∀ n, (d n).comp (d (n + 1)) = 0)
    (hexact : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n)) (n : ℕ) :
    (linearChainComplex F d hsquare).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((linearChainComplex F d hsquare).d ((n + 1) + 1) (n + 1)).hom =
    LinearMap.ker ((linearChainComplex F d hsquare).d (n + 1) n).hom
  rw [linearChainComplex_d, linearChainComplex_d]
  exact hexact n

/-- Actual projective resolution built from image/kernel equalities and a surjective augmentation. -/
noncomputable def projectiveResolutionOfLinearExact
    [∀ n, Module.Projective R (F n)]
    (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hexact : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n))
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hεsurj : Function.Surjective ε)
    (hεexact : LinearMap.range (d 0) = LinearMap.ker ε) :
    ProjectiveResolution (ModuleCat.of R M) := by
  let hsquare (n : ℕ) : (d n).comp (d (n + 1)) = 0 :=
    LinearMap.range_le_ker_iff.mp (hexact n).le
  let K := linearChainComplex F d hsquare
  have hε : K.d 1 0 ≫ ModuleCat.ofHom ε = 0 := by
    rw [linearChainComplex_d]
    exact ModuleCat.hom_ext (LinearMap.range_le_ker_iff.mp hεexact.le)
  have hp (n : ℕ) : Projective (K.X n) := by
    change Projective (ModuleCat.of R (F n))
    exact ModuleCat.projective_of_categoryTheory_projective _
  apply projectiveResolutionOfExact K hp (ModuleCat.of R M)
    (ModuleCat.ofHom ε) hε
  · exact (ModuleCat.epi_iff_surjective _).mpr hεsurj
  · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    change LinearMap.range (K.d 1 0).hom = LinearMap.ker ε
    rw [linearChainComplex_d]
    exact hεexact
  · exact linearChainComplex_exactAt_succ F d hsquare hexact

@[simp] theorem projectiveResolutionOfLinearExact_X
    [∀ n, Module.Projective R (F n)]
    (d : ∀ n, F (n + 1) →ₗ[R] F n)
    (hexact : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n))
    {M : Type u} [AddCommGroup M] [Module R M]
    (ε : F 0 →ₗ[R] M) (hεsurj : Function.Surjective ε)
    (hεexact : LinearMap.range (d 0) = LinearMap.ker ε) (n : ℕ) :
    (projectiveResolutionOfLinearExact F d hexact ε hεsurj hεexact).complex.X n =
      ModuleCat.of R (F n) := rfl

end Linear

end BPFixedPoints.ResolutionTools
