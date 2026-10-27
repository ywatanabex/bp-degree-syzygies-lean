import BPFixedPoints.Incidence.IncidencePencilCM
import BPFixedPoints.Incidence.IncidenceCoefficientParameters
import BPFixedPoints.Incidence.Finite
import Mathlib.RingTheory.Polynomial.Quotient

/-! # The coefficient ring of the pencil section

The remark `alg:pencil-sections` calls the pencil section M_G a one-dimensional Cohen–Macaulay
algebra over R ≅ ℂ[λ₁, …, λ_{ρ+1}]. Here R is the coefficient polynomial ring S_G cut by the
first d_G − 1 selected coefficient linear forms (`incidencePencilCoefficientIdeal`).

Proved here, for a tuple on the finite-quotient parameter locus with d_G > 0:
* the kernel of the pencil specialization of the parameter polynomial ring, evaluated at any
  family, generates the ideal of all members except the last
  (`incidencePencilSpecialization_ker_map`);
* R is isomorphic as a ring to the polynomial ring in ρ + 1 variables
  (`incidencePencilCoefficientEquiv`). The coordinates extending the selected forms make S_G a
  polynomial ring over the parameter ring; the cut replaces the parameter ring by ℂ[t], and the
  complementary coordinates number ρ (`card_incidenceCoefficientComplement`);
* the coefficient map S_G → 𝒰_G induces a module-finite map R → M_G
  (`incidencePencilCoefficientHom_finite`);
* together with `incidencePencil_cohenMacaulay`: M_G is a Noetherian ring of Krull dimension one,
  Cohen–Macaulay at every prime, and module-finite over a polynomial ring in ρ + 1 variables
  (`incidencePencil_cohenMacaulay_over_coefficients`).

The isomorphism is a ring isomorphism; its compatibility with the ℂ-algebra structures and any
grading is not stated.
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools Polynomial

set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

/-- Evaluated at any family of elements, the kernel of the pencil specialization generates the
ideal of all elements except the last. -/
theorem incidencePencilSpecialization_ker_map {B : Type*} [CommRing B] [Algebra ℂ B]
    (hd : 0 < G.dG) (y : Fin G.dG → B) :
    (RingHom.ker (G.incidencePencilSpecialization hd)).map (MvPolynomial.aeval y).toRingHom =
      Ideal.span (y '' {i | i ≠ G.incidencePencilIndex hd}) := by
  let J := Ideal.span (y '' {i | i ≠ G.incidencePencilIndex hd})
  apply le_antisymm
  · have hfac : (Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.aeval y) =
        (Polynomial.aeval (Ideal.Quotient.mk J (y (G.incidencePencilIndex hd)))).comp
          (G.incidencePencilSpecialization hd) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, incidencePencilSpecialization,
        Ideal.Quotient.mkₐ_eq_mk]
      by_cases hi : i = G.incidencePencilIndex hd
      · subst hi
        simp
      · simp only [hi, ite_false, map_zero]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, hi, rfl⟩)
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    have h := DFunLike.congr_fun hfac p
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
    rw [RingHom.mem_ker] at hp
    change Ideal.Quotient.mk J (MvPolynomial.aeval y p) = 0
    rw [h, hp, map_zero]
  · apply Ideal.span_le.mpr
    rintro x ⟨i, hi, rfl⟩
    rw [← MvPolynomial.aeval_X (R := ℂ) y i]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp [incidencePencilSpecialization, show i ≠ G.incidencePencilIndex hd from hi]

/-- The coefficient ideal of the pencil: the first d_G − 1 selected coefficient linear forms. -/
noncomputable def incidencePencilCoefficientIdeal (hd : 0 < G.dG) : Ideal (IncCoeffRing E) :=
  Ideal.span
    ((fun i => linearParameterForm (MvPolynomial.X : IncCoeffIdx E → IncCoeffRing E) a i) ''
      {i | i ≠ G.incidencePencilIndex hd})

/-- The coefficient pencil ideal is the kernel of the specialization, evaluated by the coefficient
linear forms. -/
theorem incidencePencilCoefficientIdeal_eq_map (hd : 0 < G.dG) :
    letI := G.incidenceCoefficientParameterAlgebra a
    G.incidencePencilCoefficientIdeal a hd =
      (RingHom.ker (G.incidencePencilSpecialization hd)).map
        (algebraMap (MvPolynomial (Fin G.dG) ℂ) (IncCoeffRing E)) := by
  let := G.incidenceCoefficientParameterAlgebra a
  change _ = (RingHom.ker (G.incidencePencilSpecialization hd)).map
    (MvPolynomial.aeval (polynomialLinearForm ∘ G.incidenceCoefficientParameterVector a)).toRingHom
  rw [G.incidencePencilSpecialization_ker_map hd]
  have hfun : (polynomialLinearForm ∘ G.incidenceCoefficientParameterVector a) =
      fun i => linearParameterForm (MvPolynomial.X : IncCoeffIdx E → IncCoeffRing E) a i :=
    funext fun i => G.incidenceCoefficientParameterVector_form a i
  rw [hfun]
  rfl

/-- The coordinates complementary to the selected coefficient forms number ρ. -/
theorem card_incidenceCoefficientComplement (ha : a ∈ G.incidenceFiniteParameterLocus) :
    Nat.card (Module.Basis.sumExtendIndex
      (G.incidenceCoefficientParameterVector_independent a ha)) = G.rho := by
  let hv := G.incidenceCoefficientParameterVector_independent a ha
  let b := Module.Basis.sumExtend hv
  have : Finite (Fin G.dG ⊕ Module.Basis.sumExtendIndex hv) := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hv) :=
    Finite.of_injective (Sum.inr : _ → Fin G.dG ⊕ Module.Basis.sumExtendIndex hv)
      Sum.inr_injective
  have h1 := Module.finrank_eq_nat_card_basis b
  rw [Module.finrank_finsupp_self, Nat.card_sum, Nat.card_eq_fintype_card (α := Fin G.dG),
    Fintype.card_fin] at h1
  have h2 := G.dG_add_rho
  simp only [IncCoeffIdx, Fintype.card_prod, Fintype.card_fin] at h1
  omega

/-- The coefficient ring of the pencil, the coefficient ring S_G cut by the first d_G − 1
selected coefficient linear forms, is a polynomial ring in ρ + 1 variables. -/
noncomputable def incidencePencilCoefficientEquiv (hd : 0 < G.dG)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    IncCoeffRing E ⧸ G.incidencePencilCoefficientIdeal a hd ≃+*
      MvPolynomial (Fin (G.rho + 1)) ℂ := by
  let := G.incidenceCoefficientParameterAlgebra a
  let hv := G.incidenceCoefficientParameterVector_independent a ha
  let K := RingHom.ker (G.incidencePencilSpecialization hd)
  let e := G.incidenceCoefficientParameterEquiv a ha
  have hJ : K.map (MvPolynomial.C : MvPolynomial (Fin G.dG) ℂ →+*
        MvPolynomial (Module.Basis.sumExtendIndex hv) (MvPolynomial (Fin G.dG) ℂ)) =
      (G.incidencePencilCoefficientIdeal a hd).map (e.toRingEquiv : IncCoeffRing E →+* _) := by
    rw [G.incidencePencilCoefficientIdeal_eq_map a hd, Ideal.map_map]
    congr 1
    refine RingHom.ext fun t => ?_
    change _ = e (algebraMap _ _ t)
    rw [e.commutes, MvPolynomial.algebraMap_eq]
  have : Finite (Module.Basis.sumExtendIndex hv) := by
    have : Finite (Fin G.dG ⊕ Module.Basis.sumExtendIndex hv) :=
      Module.Finite.finite_basis (Module.Basis.sumExtend hv)
    exact Finite.of_injective (Sum.inr : _ → Fin G.dG ⊕ Module.Basis.sumExtendIndex hv)
      Sum.inr_injective
  have hcard : Nat.card (Option (Module.Basis.sumExtendIndex hv)) = G.rho + 1 := by
    rw [Finite.card_option, G.card_incidenceCoefficientComplement a ha]
  exact (Ideal.quotientEquiv _ _ e.toRingEquiv hJ).trans
    ((MvPolynomial.quotientEquivQuotientMvPolynomial (σ := Module.Basis.sumExtendIndex hv)
      K).symm.toRingEquiv.trans
      ((MvPolynomial.mapEquiv (Module.Basis.sumExtendIndex hv)
        (Ideal.quotientKerAlgEquivOfSurjective
          (G.incidencePencilSpecialization_surjective hd)).toRingEquiv).trans
        ((MvPolynomial.optionEquivRight ℂ (Module.Basis.sumExtendIndex hv)).symm.toRingEquiv.trans
          (MvPolynomial.renameEquiv ℂ (Finite.equivFinOfCardEq hcard)).toRingEquiv)))

/-- The coefficient pencil ideal maps to zero in the pencil section. -/
theorem incidencePencilCoefficientIdeal_le_ker (hd : 0 < G.dG) :
    G.incidencePencilCoefficientIdeal a hd ≤
      RingHom.ker ((G.incidencePencilMk a).toRingHom.comp G.coeffHom.toRingHom) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, hi, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  change G.incidencePencilMk a
    (G.coeffHom (linearParameterForm (MvPolynomial.X : IncCoeffIdx E → IncCoeffRing E) a i)) = 0
  rw [← G.incidenceParameterForm_eq a i]
  exact (G.incidencePencilMk_eq_zero_iff a _).mpr
    (G.incidenceParameterForm_mem_pencilIdeal a hd i hi)

/-- The structure map from the coefficient ring of the pencil to the pencil section. -/
noncomputable def incidencePencilCoefficientHom (hd : 0 < G.dG) :
    IncCoeffRing E ⧸ G.incidencePencilCoefficientIdeal a hd →+* G.IncidencePencil a :=
  Ideal.Quotient.lift _ ((G.incidencePencilMk a).toRingHom.comp G.coeffHom.toRingHom)
    (fun _ hs => G.incidencePencilCoefficientIdeal_le_ker a hd hs)

/-- The pencil section is module-finite over its coefficient ring. -/
theorem incidencePencilCoefficientHom_finite (hd : 0 < G.dG) :
    (G.incidencePencilCoefficientHom a hd).Finite := by
  apply RingHom.Finite.of_comp_finite
    (f := Ideal.Quotient.mk (G.incidencePencilCoefficientIdeal a hd))
  have h : (G.incidencePencilCoefficientHom a hd).comp
      (Ideal.Quotient.mk (G.incidencePencilCoefficientIdeal a hd)) =
      (G.incidencePencilMk a).toRingHom.comp G.coeffHom.toRingHom :=
    Ideal.Quotient.lift_comp_mk _ _ _
  rw [h]
  exact (RingHom.Finite.of_surjective _ (G.incidencePencilMk_surjective a)).comp G.coeffHom_finite

/-- `alg:pencil-sections`: the pencil section is a one-dimensional Cohen–Macaulay ring that is
module-finite over a polynomial ring in ρ + 1 variables, through its coefficient ring
S_G/(ℓ₁, …, ℓ_{d_G−1}). -/
theorem incidencePencil_cohenMacaulay_over_coefficients (hd : 0 < G.dG)
    (ha : a ∈ G.incidenceFiniteParameterLocus) :
    ((G.incidencePencilCoefficientHom a hd).comp
        (G.incidencePencilCoefficientEquiv a hd ha).symm.toRingHom).Finite ∧
      IsNoetherianRing (G.IncidencePencil a) ∧ ringKrullDim (G.IncidencePencil a) = 1 ∧
      ∀ (P : Ideal (G.IncidencePencil a)) [P.IsPrime],
        (IsLocalRing.depth (R := Localization.AtPrime P)
          (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime P) :=
  ⟨(G.incidencePencilCoefficientHom_finite a hd).comp
    (RingHom.Finite.of_surjective _ (G.incidencePencilCoefficientEquiv a hd ha).symm.surjective),
    G.incidencePencil_cohenMacaulay a hd ha⟩

end BPFixedPoints.Multigraph
