import BPFixedPoints.Incidence.DerivedSpecialization
import BPFixedPoints.Incidence.Resolution
import BPFixedPoints.Incidence.ResolutionInternalGrading
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The actual Tor spaces of the incidence module

`incidenceTor` is Mathlib's left derived extension of scalars along the
coefficient-origin augmentation. The state basis is obtained by applying
this functor to the already constructed exact free resolution. It is not
part of the definition of Tor.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory ResolutionTools Finsupp
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

/-- The actual derived tensor product with the coefficient-origin residue
field, viewed as a complex-vector-space-valued left derived functor. -/
noncomputable def incidenceTor (p : ℕ) : ModuleCat ℂ :=
  ((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).leftDerived p).obj
    (ModuleCat.of (IncCoeffRing E) G.IncidenceRing)

section Ordered

variable [LinearOrder E]

/-- The terms of the actual incidence resolution. -/
noncomputable abbrev IncFreeTerm (p : ℕ) : Type :=
  ↥(gradedPiece (IncCoeffRing E) G.incResolutionDegree p)

/-- Its differentials, restricted from the actual transferred differential. -/
noncomputable def incFreeTermDifferential (p : ℕ) :
    G.IncFreeTerm (p + 1) →ₗ[IncCoeffRing E] G.IncFreeTerm p :=
  gradedDifferential G.incResolutionDegree G.incResolutionDifferential
    G.incResolutionDifferential_degree p

theorem incFreeTermDifferential_exact (p : ℕ) :
    LinearMap.range (G.incFreeTermDifferential (p + 1)) =
      LinearMap.ker (G.incFreeTermDifferential p) :=
  gradedDifferential_exact G.incResolutionDegree G.incResolutionDifferential
    G.incResolutionDifferential_degree G.incResolutionDifferential_sq
    G.incResolutionDifferential_exact p

theorem incFreeTermDifferential_augmentation_exact :
    LinearMap.range (G.incFreeTermDifferential 0) =
      LinearMap.ker G.incResolutionAugmentation := by
  ext x
  rw [LinearMap.mem_ker]
  constructor
  · rintro ⟨y, rfl⟩
    apply (G.incResolutionAugmentation_exact _).2
    exact ⟨y.val, y.property, rfl⟩
  · intro hx
    obtain ⟨y, hy, hDy⟩ := (G.incResolutionAugmentation_exact x).1 hx
    exact ⟨⟨y, hy⟩, Subtype.ext hDy⟩

/-- The existing augmented free complex as a Mathlib projective resolution
of the unchanged incidence ring with its original coefficient action. -/
noncomputable def incFreeResolution :
    ProjectiveResolution (ModuleCat.of (IncCoeffRing E) G.IncidenceRing) :=
  projectiveResolutionOfLinearExact G.IncFreeTerm G.incFreeTermDifferential
    G.incFreeTermDifferential_exact G.incResolutionAugmentation
    G.incResolutionAugmentation_surjective G.incFreeTermDifferential_augmentation_exact

@[simp] theorem incFreeResolution_X (p : ℕ) :
    G.incFreeResolution.complex.X p = ModuleCat.of (IncCoeffRing E) (G.IncFreeTerm p) := rfl

@[simp] theorem incFreeResolution_d (p : ℕ) :
    G.incFreeResolution.complex.d (p + 1) p =
      ModuleCat.ofHom (G.incFreeTermDifferential p) := by
  exact linearChainComplex_d G.IncFreeTerm G.incFreeTermDifferential
    (fun n => LinearMap.range_le_ker_iff.mp (G.incFreeTermDifferential_exact n).le) p

theorem incFreeResolution_minimal (i j : ℕ) :
    LinearMap.range (G.incFreeResolution.complex.d i j).hom ≤
      RingHom.ker (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) •
        (⊤ : Submodule (IncCoeffRing E) (G.incFreeResolution.complex.X j)) := by
  by_cases h : j + 1 = i
  · subst i
    rw [G.incFreeResolution_d]
    change LinearMap.range (G.incFreeTermDifferential j) ≤ _
    exact gradedDifferential_minimal (incCoeffAugmentationIdeal E)
      G.incResolutionDegree G.incResolutionDifferential G.incResolutionDifferential_degree
      G.incResolutionDifferential_minimal j
  · rw [G.incFreeResolution.complex.shape i j h]
    rw [ModuleCat.hom_zero, LinearMap.range_zero]
    exact bot_le

/-- Actual Tor identifies with the specialization of the corresponding
term of the constructed minimal free resolution. -/
noncomputable def incidenceTorIsoFreeTerm (p : ℕ) :
    G.incidenceTor p ≅
      (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).obj
        (ModuleCat.of (IncCoeffRing E) (G.IncFreeTerm p)) := by
  change G.incidenceTor p ≅
    (ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).obj
      (G.incFreeResolution.complex.X p)
  exact derivedSpecializationIsoTerm
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ) G.incFreeResolution
    G.incFreeResolution_minimal p

/-- The state basis of one homological term, before specialization. -/
noncomputable def incFreeTermBasis (p : ℕ) :
    Module.Basis {b : G.IncResolutionBasis // G.incResolutionDegree b = p}
      (IncCoeffRing E) (G.IncFreeTerm p) :=
  (Finsupp.basisSingleOne).map
    (Finsupp.supportedEquivFinsupp (R := IncCoeffRing E) (M := IncCoeffRing E)
      {b | G.incResolutionDegree b = p}).symm

/-- Scalar extension of a free term has exactly the same state basis. -/
noncomputable def incSpecializedFreeTermEquiv (p : ℕ) :
    ((ModuleCat.extendScalars (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)).obj
      (ModuleCat.of (IncCoeffRing E) (G.IncFreeTerm p))) ≃ₗ[ℂ]
        ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) := by
  letI : Algebra (IncCoeffRing E) ℂ :=
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra
  exact ((G.incFreeTermBasis p).baseChange ℂ).repr

/-- A state basis for the actual derived specialization, not for a
separately defined vector space with the expected dimension. -/
noncomputable def incidenceTorEquivState (p : ℕ) :
    G.incidenceTor p ≃ₗ[ℂ]
      ({b : G.IncResolutionBasis // G.incResolutionDegree b = p} →₀ ℂ) :=
  (G.incidenceTorIsoFreeTerm p).toLinearEquiv.trans (G.incSpecializedFreeTermEquiv p)

end Ordered

end BPFixedPoints.Multigraph
