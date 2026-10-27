import BPFixedPoints.Incidence.ResolutionTools
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Graded free-module components and projective resolutions

Restrict the differential on the total free module to basis-degree components.
Transfer its degree bound, a top-degree basis element and coefficient-ideal
minimality directly.
-/

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits

universe u

variable {R B : Type u} [CommRing R]

/-- Finite sums supported in a specified basis degree. -/
def gradedPiece (R : Type u) [CommRing R] (degree : B → ℕ) (n : ℕ) :
    Submodule R (B →₀ R) := Finsupp.supported R R {b | degree b = n}

noncomputable instance gradedPiece_moduleFree (degree : B → ℕ) (n : ℕ) :
    Module.Free R (gradedPiece R degree n) :=
  Module.Free.of_equiv
    (Finsupp.supportedEquivFinsupp (R := R) (M := R) {b | degree b = n}).symm

/-- Components above the basis-degree bound vanish. -/
theorem gradedPiece_isZero (degree : B → ℕ) (N : ℕ) (hdegree : ∀ b, degree b ≤ N)
    (n : ℕ) (hn : N < n) : IsZero (ModuleCat.of R (gradedPiece R degree n)) := by
  have hs : {b | degree b = n} = (∅ : Set B) := by
    apply Set.eq_empty_of_forall_notMem
    intro b hb
    have := hdegree b
    change degree b = n at hb
    omega
  apply ModuleCat.isZero_iff_subsingleton.mpr
  apply Submodule.subsingleton_iff_eq_bot.mpr
  rw [gradedPiece, hs, Finsupp.supported_empty]

/-- A component is nonzero whenever it contains a basis element. -/
theorem gradedPiece_nontrivial [Nontrivial R] (degree : B → ℕ) (n : ℕ)
    (b : B) (hb : degree b = n) : Nontrivial (gradedPiece R degree n) := by
  classical
  let x : gradedPiece R degree n :=
    ⟨Finsupp.single b 1, Finsupp.single_mem_supported R 1 hb⟩
  refine ⟨⟨x, 0, ?_⟩⟩
  intro h
  have he := congrArg (fun y : gradedPiece R degree n => y.val b) h
  simp [x] at he

section Differential

variable (degree : B → ℕ) (D : (B →₀ R) →ₗ[R] (B →₀ R))
variable (hdegree : ∀ n x, x ∈ gradedPiece R degree (n + 1) →
  D x ∈ gradedPiece R degree n)

/-- Restrict the total differential from degree n+1 to degree n. -/
noncomputable def gradedDifferential (n : ℕ) :
    gradedPiece R degree (n + 1) →ₗ[R] gradedPiece R degree n :=
  (D.comp (gradedPiece R degree (n + 1)).subtype).codRestrict _
    (fun x => hdegree n x.val x.property)

@[simp] theorem gradedDifferential_val (n : ℕ) (x : gradedPiece R degree (n + 1)) :
    (gradedDifferential degree D hdegree n x).val = D x.val := rfl

theorem gradedDifferential_square (hD : D.comp D = 0) (n : ℕ) :
    (gradedDifferential degree D hdegree n).comp
      (gradedDifferential degree D hdegree (n + 1)) = 0 := by
  ext x : 1
  apply Subtype.ext
  change D (D x.val) = 0
  exact LinearMap.congr_fun hD x.val

/-- Homogeneous preimages of homogeneous cycles imply exactness of the restricted complex. -/
theorem gradedDifferential_exact (hD : D.comp D = 0)
    (hexact : ∀ n x, x ∈ gradedPiece R degree (n + 1) → D x = 0 →
      ∃ y, y ∈ gradedPiece R degree (n + 2) ∧ D y = x) (n : ℕ) :
    LinearMap.range (gradedDifferential degree D hdegree (n + 1)) =
      LinearMap.ker (gradedDifferential degree D hdegree n) := by
  apply le_antisymm
    (LinearMap.range_le_ker_iff.mpr (gradedDifferential_square degree D hdegree hD n))
  intro x hx
  have hxD : D x.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  obtain ⟨y, hy, hxy⟩ := hexact n x.val x.property hxD
  exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

/-- Exactness of the degree-zero augmentation. -/
theorem gradedDifferential_augmentation_exact
    {M : Type u} [AddCommGroup M] [Module R M] (ε : (B →₀ R) →ₗ[R] M)
    (hexact : ∀ x, x ∈ gradedPiece R degree 0 →
      (ε x = 0 ↔ ∃ y, y ∈ gradedPiece R degree 1 ∧ D y = x)) :
    LinearMap.range (gradedDifferential degree D hdegree 0) =
      LinearMap.ker (ε.domRestrict (gradedPiece R degree 0)) := by
  ext x
  change (∃ y : gradedPiece R degree 1, gradedDifferential degree D hdegree 0 y = x) ↔
    ε x.val = 0
  rw [hexact x.val x.property]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y.val, y.property, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩

/-- Actual free resolution obtained from homogeneous exactness and augmentation. -/
noncomputable def gradedResolution (hD : D.comp D = 0)
    (hexact : ∀ n x, x ∈ gradedPiece R degree (n + 1) → D x = 0 →
      ∃ y, y ∈ gradedPiece R degree (n + 2) ∧ D y = x)
    {M : Type u} [AddCommGroup M] [Module R M] (ε : (B →₀ R) →ₗ[R] M)
    (hεexact : ∀ x, x ∈ gradedPiece R degree 0 →
      (ε x = 0 ↔ ∃ y, y ∈ gradedPiece R degree 1 ∧ D y = x))
    (hεsurj : ∀ m, ∃ x, x ∈ gradedPiece R degree 0 ∧ ε x = m) :
    ProjectiveResolution (ModuleCat.of R M) :=
  projectiveResolutionOfLinearExact (fun n => gradedPiece R degree n)
    (gradedDifferential degree D hdegree)
    (gradedDifferential_exact degree D hdegree hD hexact)
    (ε.domRestrict (gradedPiece R degree 0))
    (by
      intro m
      obtain ⟨x, hx, hεx⟩ := hεsurj m
      exact ⟨⟨x, hx⟩, hεx⟩)
    (gradedDifferential_augmentation_exact degree D hdegree ε hεexact)

variable (hD : D.comp D = 0)
  (hexact : ∀ n x, x ∈ gradedPiece R degree (n + 1) → D x = 0 →
    ∃ y, y ∈ gradedPiece R degree (n + 2) ∧ D y = x)
  {M : Type u} [AddCommGroup M] [Module R M] (ε : (B →₀ R) →ₗ[R] M)
  (hεexact : ∀ x, x ∈ gradedPiece R degree 0 →
    (ε x = 0 ↔ ∃ y, y ∈ gradedPiece R degree 1 ∧ D y = x))
  (hεsurj : ∀ m, ∃ x, x ∈ gradedPiece R degree 0 ∧ ε x = m)

@[simp] theorem gradedResolution_X (n : ℕ) :
    (gradedResolution degree D hdegree hD hexact ε hεexact hεsurj).complex.X n =
      ModuleCat.of R (gradedPiece R degree n) := rfl

@[simp] theorem gradedResolution_d (n : ℕ) :
    (gradedResolution degree D hdegree hD hexact ε hεexact hεsurj).complex.d (n + 1) n =
      ModuleCat.ofHom (gradedDifferential degree D hdegree n) := by
  exact linearChainComplex_d (fun n => gradedPiece R degree n)
    (gradedDifferential degree D hdegree)
    (gradedDifferential_square degree D hdegree hD) n

end Differential

section Minimality

variable (I : Ideal R)

/-- A linear map sends I times a submodule into I times the target submodule. -/
theorem map_mem_ideal_smul_top
    {M N : Type u} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) {x : M} (hx : x ∈ I • (⊤ : Submodule R M)) :
    f x ∈ I • (⊤ : Submodule R N) := by
  have hle : I • (⊤ : Submodule R M) ≤ (I • (⊤ : Submodule R N)).comap f := by
    refine Submodule.smul_le.mpr ?_
    intro a ha y _
    change f (a • y) ∈ I • (⊤ : Submodule R N)
    rw [map_smul]
    exact Submodule.smul_mem_smul ha (Submodule.mem_top : f y ∈ (⊤ : Submodule R N))
  exact hle hx

/-- Degree projection transfers an I-multiple condition on the total module to each graded component. -/
theorem gradedPiece_mem_ideal_smul_top (degree : B → ℕ) (n : ℕ)
    (x : gradedPiece R degree n) (hx : x.val ∈ I • (⊤ : Submodule R (B →₀ R))) :
    x ∈ I • (⊤ : Submodule R (gradedPiece R degree n)) := by
  classical
  let q : (B →₀ R) →ₗ[R] gradedPiece R degree n :=
    Finsupp.restrictDom R R {b | degree b = n}
  have hq : q x.val = x :=
    LinearMap.congr_fun
      (Finsupp.restrictDom_comp_subtype (M := R) (R := R) {b | degree b = n}) x
  have hqx := map_mem_ideal_smul_top I q hx
  exact hq ▸ hqx

theorem gradedDifferential_minimal (degree : B → ℕ) (D : (B →₀ R) →ₗ[R] (B →₀ R))
    (hdegree : ∀ n x, x ∈ gradedPiece R degree (n + 1) →
      D x ∈ gradedPiece R degree n)
    (hminimal : ∀ x, D x ∈ I • (⊤ : Submodule R (B →₀ R))) (n : ℕ) :
    LinearMap.range (gradedDifferential degree D hdegree n) ≤
      I • (⊤ : Submodule R (gradedPiece R degree n)) := by
  rintro _ ⟨x, rfl⟩
  exact gradedPiece_mem_ideal_smul_top I degree n _ (hminimal x.val)

end Minimality

section ProjectiveDimension

variable [Nontrivial R]
  {k M : Type u} [CommRing k] [Nontrivial k] [Algebra R k]
  [AddCommGroup M] [Module R M] [Nontrivial M]

/-- Compute the existing projective dimension from a bounded graded minimal free resolution. -/
theorem projectiveDimension_eq_of_gradedResolution
    (degree : B → ℕ) (D : (B →₀ R) →ₗ[R] (B →₀ R))
    (hdegree : ∀ n x, x ∈ gradedPiece R degree (n + 1) →
      D x ∈ gradedPiece R degree n)
    (hD : D.comp D = 0)
    (hexact : ∀ n x, x ∈ gradedPiece R degree (n + 1) → D x = 0 →
      ∃ y, y ∈ gradedPiece R degree (n + 2) ∧ D y = x)
    (ε : (B →₀ R) →ₗ[R] M)
    (hεexact : ∀ x, x ∈ gradedPiece R degree 0 →
      (ε x = 0 ↔ ∃ y, y ∈ gradedPiece R degree 1 ∧ D y = x))
    (hεsurj : ∀ m, ∃ x, x ∈ gradedPiece R degree 0 ∧ ε x = m)
    (N : ℕ) (hbound : ∀ b, degree b ≤ N) (htop : ∃ b, degree b = N)
    (hminimal : ∀ x, D x ∈ RingHom.ker (algebraMap R k) •
      (⊤ : Submodule R (B →₀ R))) :
    projectiveDimension (ModuleCat.of R M) = (N : WithBot ℕ∞) := by
  let P := gradedResolution degree D hdegree hD hexact ε hεexact hεsurj
  let : Module.Free R (P.complex.X N) := by
    change Module.Free R (gradedPiece R degree N)
    infer_instance
  let : Nontrivial (P.complex.X N) := by
    change Nontrivial (gradedPiece R degree N)
    obtain ⟨b, hb⟩ := htop
    exact gradedPiece_nontrivial degree N b hb
  apply projectiveDimension_eq_of_bounded_minimal (k := k) P N
  · intro n hn
    exact gradedPiece_isZero degree N hbound n hn
  · intro p hp
    subst N
    change LinearMap.range
        ((gradedResolution degree D hdegree hD hexact ε hεexact hεsurj).complex.d
          (p + 1) p).hom ≤ _
    rw [gradedResolution_d]
    exact gradedDifferential_minimal (RingHom.ker (algebraMap R k))
      degree D hdegree hminimal p

/-- Projective-dimension computation with augmentation given only on the degree-zero component. -/
theorem projectiveDimension_eq_of_gradedResolution₀
    (degree : B → ℕ) (D : (B →₀ R) →ₗ[R] (B →₀ R))
    (hdegree : ∀ n x, x ∈ gradedPiece R degree (n + 1) →
      D x ∈ gradedPiece R degree n)
    (hD : D.comp D = 0)
    (hexact : ∀ n x, x ∈ gradedPiece R degree (n + 1) → D x = 0 →
      ∃ y, y ∈ gradedPiece R degree (n + 2) ∧ D y = x)
    (ε₀ : gradedPiece R degree 0 →ₗ[R] M)
    (hεexact : ∀ x : gradedPiece R degree 0,
      ε₀ x = 0 ↔ ∃ y, y ∈ gradedPiece R degree 1 ∧ D y = x.val)
    (hεsurj : Function.Surjective ε₀)
    (N : ℕ) (hbound : ∀ b, degree b ≤ N) (htop : ∃ b, degree b = N)
    (hminimal : ∀ x, D x ∈ RingHom.ker (algebraMap R k) •
      (⊤ : Submodule R (B →₀ R))) :
    projectiveDimension (ModuleCat.of R M) = (N : WithBot ℕ∞) := by
  classical
  let q : (B →₀ R) →ₗ[R] gradedPiece R degree 0 :=
    Finsupp.restrictDom R R {b | degree b = 0}
  have hq (x : gradedPiece R degree 0) : q x.val = x :=
    LinearMap.congr_fun
      (Finsupp.restrictDom_comp_subtype (M := R) (R := R) {b | degree b = 0}) x
  let ε := ε₀.comp q
  apply projectiveDimension_eq_of_gradedResolution (k := k)
    degree D hdegree hD hexact ε
  · intro x hx
    change ε₀ (q x) = 0 ↔ _
    rw [hq ⟨x, hx⟩]
    exact hεexact ⟨x, hx⟩
  · intro m
    obtain ⟨x, hx⟩ := hεsurj m
    refine ⟨x.val, x.property, ?_⟩
    change ε₀ (q x.val) = m
    rw [hq x, hx]
  · exact hbound
  · exact htop
  · exact hminimal

end ProjectiveDimension

end BPFixedPoints.ResolutionTools
