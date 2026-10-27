import BPFixedPoints.Incidence.IncidencePrimeDepthTools
import BPFixedPoints.Incidence.IncidenceParameterSections
import BPFixedPoints.Incidence.IncidenceParameterBaseChange
import BPFixedPoints.Incidence.IncidenceMaximalDepth
import Mathlib.RingTheory.KrullDimension.PID

/-! # The pencil section is a one-dimensional Cohen–Macaulay ring

Fix a tuple a on the finite-quotient parameter locus with d_G > 0. The pencil section M_G is the
quotient of the incidence ring by the first d_G − 1 selected parameter forms
(`IncidencePencil`); its Hilbert series is `incidenceParameterPencil_hilbert`.

Proved here:
* M_G is finite free of rank omega-tilde(1) over the polynomial ring ℂ[t], with t acting by the
  last parameter form (`incidencePencil_finite_free`). The proof specializes the parameter
  polynomial ring to ℂ[t], identifies the kernel evaluated in the incidence ring with the pencil
  ideal, and transports the cut statement `incidence_parameter_cut_finite_free`;
* every prime of M_G has the height of the prime below it in ℂ[t], every maximal ideal has
  height one, and M_G has Krull dimension one (`incidencePencil_krullDim`);
* M_G is Noetherian and depth equals Krull dimension at every prime localization, with Mathlib's
  Ext depth (`incidencePencil_cohenMacaulay`); at maximal ideals both are one
  (`incidencePencil_local_depth_maximal`).

The paper's remark also calls M_G an algebra over its coefficient ring
R ≅ ℂ[λ₁, …, λ_{ρ+1}], the coefficient polynomial ring cut by the same d_G − 1 linear forms.
That coefficient-ring isomorphism, and finiteness of M_G over it, are proved in
`IncidencePencilCMCoefficients`.
-/

namespace BPFixedPoints.ResolutionTools

/-- Freeness, finiteness and rank transfer along a ring isomorphism together with a compatible
additive isomorphism of modules. -/
theorem free_finite_finrank_of_equiv_equiv {R R' M M' : Type*} [CommRing R] [CommRing R']
    [Nontrivial R] [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R' M']
    (i : R ≃+* R') (j : M ≃+ M') (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m)
    [Module.Free R M] [Module.Finite R M] :
    Module.Free R' M' ∧ Module.Finite R' M' ∧ Module.finrank R' M' = Module.finrank R M := by
  have : Nontrivial R' := i.toEquiv.symm.nontrivial
  let b := Module.Free.chooseBasis R M
  let : Module R M' := Module.compHom M' i.toRingHom
  let jl : M ≃ₗ[R] M' := { j with map_smul' := fun r m => hc r m }
  let b' : Module.Basis (Module.Free.ChooseBasisIndex R M) R' M' :=
    (b.map jl).mapCoeffs i (fun _ _ => rfl)
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]

/-- Algebra version: freeness, finiteness and rank transfer along ring isomorphisms of the
coefficient rings and of the algebras that are compatible with the structure maps. -/
theorem free_finite_finrank_of_algebra_equiv {R R' A A' : Type*} [CommRing R] [CommRing R']
    [Nontrivial R] [CommRing A] [CommRing A'] [Algebra R A] [Algebra R' A']
    (i : R ≃+* R') (j : A ≃+* A') (hc : ∀ r : R, j (algebraMap R A r) = algebraMap R' A' (i r))
    [Module.Free R A] [Module.Finite R A] :
    Module.Free R' A' ∧ Module.Finite R' A' ∧ Module.finrank R' A' = Module.finrank R A := by
  apply free_finite_finrank_of_equiv_equiv i j.toAddEquiv
  intro r m
  change j (r • m) = i r • j m
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]

end BPFixedPoints.ResolutionTools

namespace BPFixedPoints.Multigraph

open ResolutionTools Polynomial
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (a : G.IncidenceLinearParameters)

local instance incPencilNoetherian : IsNoetherianRing G.IncidenceRing :=
  G.incidence_cohenMacaulay.1

/-- The pencil section M_G: the quotient of the incidence ring by the first d_G − 1 selected
parameter forms, the ring of `incidenceParameterPencil_hilbert`. It is a separate type so that
its ring structure is the quotient commutative ring structure only. -/
def IncidencePencil : Type := G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1)

/-- The pencil section is, by definition, the quotient ring of the Hilbert-series statements. -/
theorem incidencePencil_def :
    G.IncidencePencil a = (G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1)) :=
  rfl

/-- The quotient commutative ring structure of the pencil section. -/
noncomputable instance incidencePencilCommRing : CommRing (G.IncidencePencil a) :=
  inferInstanceAs (CommRing (G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1)))

/-- The quotient complex algebra structure of the pencil section. -/
noncomputable instance incidencePencilComplexAlgebra : Algebra ℂ (G.IncidencePencil a) :=
  inferInstanceAs (Algebra ℂ (G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1)))

/-- The pencil section is Noetherian, as a quotient of the Noetherian incidence ring. -/
instance incidencePencilNoetherian : IsNoetherianRing (G.IncidencePencil a) :=
  inferInstanceAs
    (IsNoetherianRing (G.IncidenceRing ⧸ G.incidenceParameterSectionIdeal a (G.dG - 1)))

/-- The quotient map onto the pencil section. -/
noncomputable def incidencePencilMk : G.IncidenceRing →ₐ[ℂ] G.IncidencePencil a :=
  Ideal.Quotient.mkₐ ℂ (G.incidenceParameterSectionIdeal a (G.dG - 1))

/-- The quotient map onto the pencil section is surjective. -/
theorem incidencePencilMk_surjective : Function.Surjective (G.incidencePencilMk a) :=
  Ideal.Quotient.mk_surjective

/-- An element maps to zero in the pencil section exactly when it lies in the pencil ideal. -/
theorem incidencePencilMk_eq_zero_iff (x : G.IncidenceRing) :
    G.incidencePencilMk a x = 0 ↔ x ∈ G.incidenceParameterSectionIdeal a (G.dG - 1) :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The index of the last selected parameter form. -/
noncomputable def incidencePencilIndex (hd : 0 < G.dG) : Fin G.dG :=
  ⟨G.dG - 1, Nat.sub_lt hd Nat.one_pos⟩

/-- The specialization of the parameter polynomial ring sending every variable except the last
to zero and the last to the polynomial variable. -/
noncomputable def incidencePencilSpecialization (hd : 0 < G.dG) :
    MvPolynomial (Fin G.dG) ℂ →ₐ[ℂ] ℂ[X] :=
  MvPolynomial.aeval (fun i => if i = G.incidencePencilIndex hd then (X : ℂ[X]) else 0)

/-- The class of the last selected parameter form in the pencil section. -/
noncomputable def incidencePencilParameter (hd : 0 < G.dG) : G.IncidencePencil a :=
  G.incidencePencilMk a (G.incidenceParameterForm a (G.incidencePencilIndex hd))

/-- The pencil section is an algebra over the polynomial ring in one variable, the variable acting
by the last selected parameter form. -/
@[instance_reducible] noncomputable def incidencePencilAlgebra (hd : 0 < G.dG) :
    Algebra ℂ[X] (G.IncidencePencil a) :=
  (Polynomial.aeval (G.incidencePencilParameter a hd)).toRingHom.toAlgebra

/-- The structure map of the one-variable polynomial algebra is evaluation at the last form. -/
theorem incidencePencilAlgebra_algebraMap (hd : 0 < G.dG) :
    letI := G.incidencePencilAlgebra a hd
    algebraMap ℂ[X] (G.IncidencePencil a) =
      (Polynomial.aeval (G.incidencePencilParameter a hd)).toRingHom := rfl

/-- Membership in the first r selected forms. -/
theorem mem_take_incidenceParameterList_iff (r : ℕ) (x : G.IncidenceRing) :
    x ∈ (G.incidenceParameterList a).take r ↔
      ∃ i : Fin G.dG, i.val < r ∧ G.incidenceParameterForm a i = x := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j < G.dG := by
      have := lt_of_lt_of_le hj (min_le_right _ _)
      simpa using this
    refine ⟨⟨j, hj'⟩, lt_of_lt_of_le hj (min_le_left _ _), ?_⟩
    simp [incidenceParameterList]
  · rintro ⟨i, hi, rfl⟩
    refine ⟨i.val, ?_, ?_⟩
    · simp [hi]
    · simp [incidenceParameterList]

/-- Every selected form except the last lies in the pencil ideal. -/
theorem incidenceParameterForm_mem_pencilIdeal (hd : 0 < G.dG) (i : Fin G.dG)
    (hi : i ≠ G.incidencePencilIndex hd) :
    G.incidenceParameterForm a i ∈ G.incidenceParameterSectionIdeal a (G.dG - 1) := by
  apply Ideal.subset_span
  change G.incidenceParameterForm a i ∈ (G.incidenceParameterList a).take (G.dG - 1)
  rw [G.mem_take_incidenceParameterList_iff]
  refine ⟨i, ?_, rfl⟩
  have : i.val ≠ G.dG - 1 := fun h => hi (Fin.ext h)
  omega

/-- In the pencil section, the parameter action factors through the specialization. -/
theorem incidencePencil_parameter_factor (hd : 0 < G.dG) :
    (G.incidencePencilMk a).comp (G.incidenceParameterHom a) =
      (Polynomial.aeval (G.incidencePencilParameter a hd)).comp
        (G.incidencePencilSpecialization hd) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, incidenceParameterHom_X, incidencePencilSpecialization,
    MvPolynomial.aeval_X]
  by_cases hi : i = G.incidencePencilIndex hd
  · subst hi
    simp [incidencePencilParameter]
  · simp only [hi, ite_false, map_zero]
    exact (G.incidencePencilMk_eq_zero_iff a _).mpr
      (G.incidenceParameterForm_mem_pencilIdeal a hd i hi)

/-- The pencil specialization is surjective. -/
theorem incidencePencilSpecialization_surjective (hd : 0 < G.dG) :
    Function.Surjective (G.incidencePencilSpecialization hd) := by
  intro q
  refine ⟨Polynomial.aeval (MvPolynomial.X (G.incidencePencilIndex hd)) q, ?_⟩
  have h : (G.incidencePencilSpecialization hd).comp
      (Polynomial.aeval (MvPolynomial.X (G.incidencePencilIndex hd))) = AlgHom.id ℂ ℂ[X] := by
    apply Polynomial.algHom_ext
    simp [incidencePencilSpecialization]
  exact DFunLike.congr_fun h q

/-- The kernel of the specialization, evaluated by the parameter forms, is the pencil ideal. -/
theorem incidencePencil_cutIdeal (hd : 0 < G.dG) :
    (RingHom.ker (G.incidencePencilSpecialization hd)).map (G.incidenceParameterHom a).toRingHom =
      G.incidenceParameterSectionIdeal a (G.dG - 1) := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, ← G.incidencePencilMk_eq_zero_iff]
    have h := DFunLike.congr_fun (G.incidencePencil_parameter_factor a hd) p
    simp only [AlgHom.comp_apply] at h
    rw [RingHom.mem_ker] at hp
    change G.incidencePencilMk a (G.incidenceParameterHom a p) = 0
    rw [h, hp, map_zero]
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := (G.mem_take_incidenceParameterList_iff a _ x).mp hx
    have hne : i ≠ G.incidencePencilIndex hd := by
      intro h
      rw [h] at hi
      exact lt_irrefl _ hi
    rw [← incidenceParameterHom_X]
    apply Ideal.mem_map_of_mem
    rw [RingHom.mem_ker]
    simp [incidencePencilSpecialization, hne]

/-- The pencil section is finite free over the polynomial ring in one variable acting by the last
parameter form, of rank omega-tilde(1). -/
theorem incidencePencil_finite_free (hd : 0 < G.dG) (ha : a ∈ G.incidenceFiniteParameterLocus) :
    letI := G.incidencePencilAlgebra a hd
    Module.Free ℂ[X] (G.IncidencePencil a) ∧ Module.Finite ℂ[X] (G.IncidencePencil a) ∧
      (Module.finrank ℂ[X] (G.IncidencePencil a) : ℤ) = G.omegaTilde.eval 1 := by
  let := G.incidenceParameterAlgebra a
  let K := RingHom.ker (G.incidencePencilSpecialization hd)
  have hK : K ≠ ⊤ := by
    intro h
    have h1 : (1 : MvPolynomial (Fin G.dG) ℂ) ∈ K := h ▸ Submodule.mem_top
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  let : Module (MvPolynomial (Fin G.dG) ℂ ⧸ K)
      (G.IncidenceRing ⧸ K.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing)) :=
    @Algebra.toModule (MvPolynomial (Fin G.dG) ℂ ⧸ K)
      (G.IncidenceRing ⧸ K.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing))
      inferInstance inferInstance inferInstance
  obtain ⟨hfree, hfin, -, hrank⟩ := G.incidence_parameter_cut_finite_free a ha K hK
  have : Nontrivial (MvPolynomial (Fin G.dG) ℂ ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
  let e₁ := Ideal.quotientKerAlgEquivOfSurjective (G.incidencePencilSpecialization_surjective hd)
  let e₂ : (G.IncidenceRing ⧸ K.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing))
      ≃+* G.IncidencePencil a := Ideal.quotEquivOfEq (G.incidencePencil_cutIdeal a hd)
  let := G.incidencePencilAlgebra a hd
  have key := free_finite_finrank_of_algebra_equiv (R := MvPolynomial (Fin G.dG) ℂ ⧸ K)
    (R' := ℂ[X])
    (A := G.IncidenceRing ⧸ K.map (algebraMap (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing))
    (A' := G.IncidencePencil a) e₁.toRingEquiv e₂
  obtain ⟨h1, h2, h3⟩ := key (by
    intro r
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h := DFunLike.congr_fun (G.incidencePencil_parameter_factor a hd) p
    simp only [AlgHom.comp_apply] at h
    simp only [e₁, e₂, AlgEquiv.coe_toRingEquiv]
    exact h)
  exact ⟨h1, h2, by rw [h3]; exact hrank⟩

/-- The pencil section is nonzero. -/
theorem incidencePencil_nontrivial (ha : a ∈ G.incidenceFiniteParameterLocus) :
    Nontrivial (G.IncidencePencil a) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (regular_ideal_ofList_ne_top _ (G.incidenceParameterSection_regular a ha (G.dG - 1)))

/-- Every prime localization of the pencil section has a regular sequence of dimension length. -/
theorem incidencePencil_primeDimRegular (hd : 0 < G.dG)
    (ha : a ∈ G.incidenceFiniteParameterLocus) : PrimeDimRegular (G.IncidencePencil a) := by
  let := G.incidencePencilAlgebra a hd
  obtain ⟨h1, h2, -⟩ := G.incidencePencil_finite_free a hd ha
  exact (primeDimRegular_polynomial_field ℂ).of_finite_flat

/-- Every prime of the pencil section has the height of the prime below it in the polynomial
ring. -/
theorem incidencePencil_height_eq (hd : 0 < G.dG) (ha : a ∈ G.incidenceFiniteParameterLocus)
    (P : Ideal (G.IncidencePencil a)) [P.IsPrime] :
    letI := G.incidencePencilAlgebra a hd
    P.height = (P.under ℂ[X]).height := by
  let := G.incidencePencilAlgebra a hd
  obtain ⟨h1, h2, -⟩ := G.incidencePencil_finite_free a hd ha
  exact height_eq_height_under_of_finite_flat P

/-- Every maximal ideal of the pencil section has height one. -/
theorem incidencePencil_height_maximal (hd : 0 < G.dG)
    (ha : a ∈ G.incidenceFiniteParameterLocus) (P : Ideal (G.IncidencePencil a)) [P.IsMaximal] :
    P.height = 1 := by
  let := G.incidencePencilAlgebra a hd
  obtain ⟨h1, h2, -⟩ := G.incidencePencil_finite_free a hd ha
  rw [G.incidencePencil_height_eq a hd ha P]
  have : (P.under ℂ[X]).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  exact IsPrincipalIdealRing.height_eq_one_of_isMaximal _ (Polynomial.not_isField ℂ)

/-- The pencil section has Krull dimension one. -/
theorem incidencePencil_krullDim (hd : 0 < G.dG) (ha : a ∈ G.incidenceFiniteParameterLocus) :
    ringKrullDim (G.IncidencePencil a) = 1 := by
  apply le_antisymm
  · rw [ringKrullDim_le_iff_height_le]
    intro p hp
    let := G.incidencePencilAlgebra a hd
    rw [G.incidencePencil_height_eq a hd ha p]
    calc ((p.under ℂ[X]).height : WithBot ℕ∞) ≤ ringKrullDim ℂ[X] :=
          Ideal.height_le_ringKrullDim_of_isPrime
      _ = 1 := IsPrincipalIdealRing.ringKrullDim_eq_one ℂ[X] (Polynomial.not_isField ℂ)
  · have := G.incidencePencil_nontrivial a ha
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (G.IncidencePencil a)
    have h := G.incidencePencil_height_maximal a hd ha P
    calc (1 : WithBot ℕ∞) = (P.height : WithBot ℕ∞) := by rw [h]; rfl
      _ ≤ ringKrullDim (G.IncidencePencil a) := Ideal.height_le_ringKrullDim_of_isPrime

/-- The pencil section is a one-dimensional Cohen–Macaulay ring: it is Noetherian of Krull
dimension one, and depth equals Krull dimension at every prime localization. -/
theorem incidencePencil_cohenMacaulay (hd : 0 < G.dG) (ha : a ∈ G.incidenceFiniteParameterLocus) :
    IsNoetherianRing (G.IncidencePencil a) ∧ ringKrullDim (G.IncidencePencil a) = 1 ∧
      ∀ (P : Ideal (G.IncidencePencil a)) [P.IsPrime],
        (IsLocalRing.depth (R := Localization.AtPrime P)
          (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
          ringKrullDim (Localization.AtPrime P) :=
  ⟨inferInstance, G.incidencePencil_krullDim a hd ha,
    fun P _ => (G.incidencePencil_primeDimRegular a hd ha).depth_eq P⟩

/-- At every maximal ideal of the pencil section, depth and Krull dimension are one. -/
theorem incidencePencil_local_depth_maximal (hd : 0 < G.dG)
    (ha : a ∈ G.incidenceFiniteParameterLocus) (P : Ideal (G.IncidencePencil a)) [P.IsMaximal] :
    IsLocalRing.depth (R := Localization.AtPrime P)
        (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) = 1 ∧
      ringKrullDim (Localization.AtPrime P) = 1 := by
  have hdim : ringKrullDim (Localization.AtPrime P) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P),
      G.incidencePencil_height_maximal a hd ha P]
    rfl
  refine ⟨?_, hdim⟩
  have h := (G.incidencePencil_primeDimRegular a hd ha).depth_eq P
  rw [hdim] at h
  exact_mod_cast h

end BPFixedPoints.Multigraph
