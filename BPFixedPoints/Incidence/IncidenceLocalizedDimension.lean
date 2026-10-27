import BPFixedPoints.Incidence.Dimension
import BPFixedPoints.Incidence.IncidenceLocalizedResolution

/-! # Dimension of the localized incidence module at a prime of the coefficient ring

This completes the localization argument of `supp:cm-localization`. The coefficient ring
S_G = `IncCoeffRing E` acts on 𝒰_G = `G.IncidenceRing` through `coeffHom`, with kernel
I = ker(S_G → 𝒰_G), and (𝒰_G)_𝔭 is `LocalizedModule 𝔭.primeCompl G.IncidenceRing` over
(S_G)_𝔭 = `Localization.AtPrime 𝔭`.

Proved here:
* ht I ≥ ρ (`rho_le_height_ker_coeffHom`), and in fact ht I = ρ (`height_ker_coeffHom`);
* dim (𝒰_G)_𝔭 ≤ ht 𝔭 − ρ for every prime 𝔭 of S_G (`incidence_localized_supportDim_le`);
* for every prime 𝔭 ⊇ I, dim (𝒰_G)_𝔭 = ht 𝔭 − ρ (`incidence_localized_supportDim`), the dimension
  being the support dimension over (S_G)_𝔭;
* for every prime 𝔭 ⊇ I, depth_{(S_G)_𝔭} (𝒰_G)_𝔭 = ht 𝔭 − ρ = dim (𝒰_G)_𝔭
  (`incidence_localized_cohenMacaulay`): (𝒰_G)_𝔭 is a Cohen–Macaulay (S_G)_𝔭-module.

Method. The d_G coefficients c_J chosen by `incIndependentCoeff` are algebraically independent in
𝒰_G and d_G = trdeg 𝒰_G, so they form a transcendence basis and every element of 𝒰_G is algebraic
over ℂ[c_J]. Renaming variables, S_G is a polynomial ring over ℂ[c_J] in the remaining
ρ = 4m − d_G coefficients. For a prime P of R[X] containing a polynomial outside the extension of
its contraction p, ht P ≥ ht p[X] + 1 ≥ ht p + 1 (`PolynomialHeightTools`); adding the ρ remaining
coefficients one at a time therefore gives ht I ≥ ρ. This replaces the dimension formula for
polynomial rings, which Mathlib lacks. For the upper bound, a chain of length k in the support of
(𝒰_G)_𝔭 contracts to a chain of primes of S_G that starts at a prime containing I and ends inside
𝔭; prefixing a chain of length ρ below its first member gives ρ + k ≤ ht 𝔭. The lower bound
ht 𝔭 − ρ ≤ depth ≤ dim is `incidence_localized_depth_bounds`.
-/

namespace BPFixedPoints.PolynomialHeightTools

open Polynomial

/-- Extending a prime of `R` to `R[X]` does not lower its height. -/
theorem height_le_height_map_C {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime] :
    p.height ≤ (p.map (C : R →+* R[X])).height := by
  let f : PrimeSpectrum R → PrimeSpectrum R[X] := fun q =>
    ⟨q.asIdeal.map C, @Ideal.isPrime_map_C_of_isPrime _ _ _ q.2⟩
  have hcomap (q : Ideal R) : (q.map (C : R →+* R[X])).comap C = q := by
    ext r
    rw [Ideal.mem_comap, Ideal.mem_map_C_iff]
    constructor
    · intro h
      simpa using h 0
    · intro h n
      rw [coeff_C]
      split_ifs
      · exact h
      · exact q.zero_mem
  have hf : StrictMono f := by
    intro a b hab
    refine lt_of_le_of_ne (Ideal.map_mono hab.le) fun h => hab.ne ?_
    ext1
    have := congrArg (Ideal.comap (C : R →+* R[X])) (congrArg PrimeSpectrum.asIdeal h)
    simpa [f, hcomap] using this
  have h := Order.height_le_height_apply_of_strictMono f hf ⟨p, ‹_›⟩
  rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h

/-- If a prime `P` of `R[X]` contains a polynomial outside the extension of its contraction, its
height is at least one more than the height of the contraction. -/
theorem height_add_one_le_of_not_mem_map_comap {R : Type*} [CommRing R] (P : Ideal R[X])
    [P.IsPrime] {f : R[X]} (hf : f ∈ P) (hf' : f ∉ (P.comap C).map C) :
    (P.comap (C : R →+* R[X])).height + 1 ≤ P.height := by
  have hlt : (P.comap (C : R →+* R[X])).map C < P :=
    lt_of_le_of_ne Ideal.map_comap_le fun h => hf' (by rw [h]; exact hf)
  calc (P.comap (C : R →+* R[X])).height + 1
      ≤ ((P.comap (C : R →+* R[X])).map C).height + 1 := by
        gcongr; exact height_le_height_map_C _
    _ ≤ P.height := Ideal.height_add_one_le_of_lt_of_isPrime hlt

/-- Evaluation of `MvPolynomial (Fin (n + 1)) R` factors through `finSuccEquiv`: first evaluate
the coefficients in `MvPolynomial (Fin n) R`, then the variable `X 0`. -/
theorem eval₂Hom_eq_comp_finSuccEquiv {R A : Type*} [CommRing R] [CommRing A] (φ : R →+* A)
    {n : ℕ} (y : Fin (n + 1) → A) :
    MvPolynomial.eval₂Hom φ y =
      (eval₂RingHom (MvPolynomial.eval₂Hom φ (Fin.tail y)) (y 0)).comp
        (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [MvPolynomial.finSuccEquiv_apply]
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [MvPolynomial.finSuccEquiv_X_zero]
    · simp [MvPolynomial.finSuccEquiv_X_succ, Fin.tail]

/-- Adjoining `n` elements of a domain `A`, each a root of a polynomial over `R` whose image under
`φ` is nonzero, raises the height of the kernel by at least `n`. -/
theorem height_ker_add_le_height_ker_eval₂Hom {R A : Type*} [CommRing R] [CommRing A]
    [IsDomain A] (φ : R →+* A) :
    ∀ (n : ℕ) (y : Fin n → A), (∀ i, ∃ g : R[X], g.map φ ≠ 0 ∧ g.eval₂ φ (y i) = 0) →
      (RingHom.ker φ).height + n ≤ (RingHom.ker (MvPolynomial.eval₂Hom φ y)).height := by
  intro n
  induction n with
  | zero =>
    intro y _
    have h : MvPolynomial.eval₂Hom φ y =
        φ.comp (MvPolynomial.isEmptyRingEquiv R (Fin 0)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; exact i.elim0
    rw [h, ← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe,
      RingEquiv.height_comap]
    simp
  | succ n ih =>
    intro y hy
    set φ' := MvPolynomial.eval₂Hom φ (Fin.tail y)
    set Ψ := eval₂RingHom φ' (y 0)
    have hφ' : φ'.comp MvPolynomial.C = φ := MvPolynomial.eval₂Hom_comp_C _ _
    have hcomap :
        (RingHom.ker Ψ).comap (C : MvPolynomial (Fin n) R →+* _) = RingHom.ker φ' := by
      rw [RingHom.comap_ker]
      congr 1
      exact RingHom.ext fun r => eval₂_C _ _
    have hprime : (RingHom.ker Ψ).IsPrime := RingHom.ker_isPrime Ψ
    obtain ⟨g, hg0, hgy⟩ := hy 0
    -- The polynomial `g` over the coefficients lies in ker Ψ but not in the extension of
    -- ker φ', so the last variable raises the height by one.
    have hstep : (RingHom.ker φ').height + 1 ≤ (RingHom.ker Ψ).height := by
      rw [← hcomap]
      refine height_add_one_le_of_not_mem_map_comap (RingHom.ker Ψ)
        (f := g.map MvPolynomial.C) ?_ ?_
      · rw [RingHom.mem_ker]
        change (g.map MvPolynomial.C).eval₂ φ' (y 0) = 0
        rw [eval₂_map, hφ', hgy]
      · rw [hcomap, Ideal.mem_map_C_iff]
        intro hall
        apply hg0
        ext k
        have := hall k
        rw [coeff_map, RingHom.mem_ker] at this
        rw [coeff_map, coeff_zero]
        simpa [φ'] using this
    have hih := ih (Fin.tail y) fun i => hy i.succ
    rw [eval₂Hom_eq_comp_finSuccEquiv, ← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe,
      Ideal.comap_coe, RingEquiv.height_comap]
    calc (RingHom.ker φ).height + ((n + 1 : ℕ) : ℕ∞)
        = ((RingHom.ker φ).height + n) + 1 := by push_cast; ring
      _ ≤ (RingHom.ker φ').height + 1 := by gcongr
      _ ≤ (RingHom.ker Ψ).height := hstep

end BPFixedPoints.PolynomialHeightTools

namespace BPFixedPoints.Multigraph

open MvPolynomial

section KernelHeight

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- The coefficient map restricted to the independent coefficients c_J. -/
noncomputable abbrev incIndependentHom :
    MvPolynomial G.IncIndependentVar ℂ →+* G.IncidenceRing :=
  (G.coeffHom.comp (rename G.incIndependentCoeff)).toRingHom

/-- Every element of 𝒰_G is a root of a polynomial over ℂ[c_J] whose image in 𝒰_G[X] is nonzero:
the independent coefficients form a transcendence basis, since there are d_G = trdeg 𝒰_G of
them. -/
theorem exists_poly_incIndependentHom (a : G.IncidenceRing) :
    ∃ g : Polynomial (MvPolynomial G.IncIndependentVar ℂ),
      g.map G.incIndependentHom ≠ 0 ∧ g.eval₂ G.incIndependentHom a = 0 := by
  set x : G.IncIndependentVar → G.IncidenceRing :=
    fun i => G.coeffHom (X (G.incIndependentCoeff i))
  have hx : AlgebraicIndependent ℂ x := G.incidenceCoefficients_algebraicIndependent
  have hb : IsTranscendenceBasis ℂ x := hx.isTranscendenceBasis_of_trdeg_le_of_finite (by
    rw [G.trdeg_incidenceRing_eq, Cardinal.mk_fintype, G.card_incIndependentVar])
  obtain ⟨p, hp0, hpa⟩ := hb.isAlgebraic.isAlgebraic a
  -- Lift `p` from the subalgebra ℂ[c_J] ⊆ 𝒰_G to the polynomial ring on the indices J.
  have hmem (r : MvPolynomial G.IncIndependentVar ℂ) :
      aeval x r ∈ Algebra.adjoin ℂ (Set.range x) := by
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨r, rfl⟩
  let ψ := (aeval x).codRestrict (Algebra.adjoin ℂ (Set.range x)) hmem
  have hψ : Function.Surjective ψ := by
    rintro ⟨b, hb⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at hb
    obtain ⟨r, rfl⟩ := hb
    exact ⟨r, rfl⟩
  have hφ : G.incIndependentHom =
      (Algebra.adjoin ℂ (Set.range x)).val.toRingHom.comp ψ.toRingHom := by
    have : G.coeffHom.comp (rename G.incIndependentCoeff) = aeval x :=
      MvPolynomial.algHom_ext fun i => by simp [x]
    ext r
    · simp [incIndependentHom, ψ, ← this]
    · simp [incIndependentHom, ψ, ← this]
  obtain ⟨g, rfl⟩ := Polynomial.map_surjective ψ.toRingHom hψ p
  refine ⟨g, ?_, ?_⟩
  · rw [hφ, ← Polynomial.map_map]
    exact (Polynomial.map_ne_zero_iff Subtype.val_injective).mpr hp0
  · rw [hφ, ← Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hpa
    exact hpa

/-- The independent coefficient indices are distinct. -/
theorem incIndependentCoeff_injective : Function.Injective G.incIndependentCoeff := by
  intro a b h
  apply G.incidenceCoefficients_algebraicIndependent.injective
  simp only [h]

/-- The coefficients outside the independent family number ρ = 4m − d_G. -/
theorem card_incDependentCoeff [DecidablePred (· ∈ Set.range G.incIndependentCoeff)] :
    Fintype.card {c : IncCoeffIdx E // c ∉ Set.range G.incIndependentCoeff} = G.rho := by
  rw [Fintype.card_subtype_compl, Fintype.card_congr
    (Equiv.ofInjective _ G.incIndependentCoeff_injective).symm, G.card_incIndependentVar]
  have h := G.dG_add_rho
  simp only [IncCoeffIdx, Fintype.card_prod, Fintype.card_fin] at h ⊢
  omega

/-- `supp:cm-localization`, the height of the kernel: ht I ≥ ρ for I = ker(S_G → 𝒰_G). Over the
polynomial ring ℂ[c_J] in the d_G independent coefficients, S_G is a polynomial ring in the other
ρ coefficients, each algebraic modulo I; each of them raises the height of the contracted kernel
by one. -/
theorem rho_le_height_ker_coeffHom : (G.rho : ℕ∞) ≤ (RingHom.ker G.coeffHom).height := by
  classical
  let j := G.incIndependentCoeff
  let eK : {c : IncCoeffIdx E // c ∉ Set.range j} ≃ Fin G.rho :=
    Fintype.equivFinOfCardEq G.card_incDependentCoeff
  -- Split the 4m coefficient indices into ρ dependent ones and the d_G independent ones.
  let g : Fin G.rho ⊕ G.IncIndependentVar ≃ IncCoeffIdx E :=
    ((Equiv.sumCongr eK.symm (Equiv.ofInjective j G.incIndependentCoeff_injective)).trans
      (Equiv.sumComm _ _)).trans (Equiv.sumCompl (· ∈ Set.range j))
  have hg (i : G.IncIndependentVar) : g (Sum.inr i) = j i := by
    simp [g]
  let e : MvPolynomial (Fin G.rho) (MvPolynomial G.IncIndependentVar ℂ) ≃ₐ[ℂ] IncCoeffRing E :=
    (sumAlgEquiv ℂ (Fin G.rho) G.IncIndependentVar).symm.trans (renameEquiv ℂ g)
  let y : Fin G.rho → G.IncidenceRing := fun k => G.coeffHom (X (g (Sum.inl k)))
  have hcomp : G.coeffHom.toRingHom.comp e.toRingEquiv.toRingHom =
      eval₂Hom G.incIndependentHom y := by
    apply MvPolynomial.ringHom_ext'
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [e]
      · intro i
        simp [e, hg, incIndependentHom, j]
    · intro k
      simp [e, y]
  have key := PolynomialHeightTools.height_ker_add_le_height_ker_eval₂Hom G.incIndependentHom
    G.rho y fun k => G.exists_poly_incIndependentHom (y k)
  rw [← hcomp, ← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe,
    RingEquiv.height_comap] at key
  exact le_trans (by simp) key

end KernelHeight

section LocalizedDimension

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance incLocDimAlgebra : Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

/-- A prime of (S_G)_𝔭 in the support of (𝒰_G)_𝔭 contracts to a prime containing I. -/
theorem ker_coeffHom_le_comap_of_mem_support (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (q : PrimeSpectrum (Localization.AtPrime 𝔭))
    (hq : q ∈ Module.support (Localization.AtPrime 𝔭)
      (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) :
    RingHom.ker G.coeffHom ≤
      q.asIdeal.comap (algebraMap (IncCoeffRing E) (Localization.AtPrime 𝔭)) := by
  intro x hx
  apply Module.annihilator_le_of_mem_support hq
  rw [Module.mem_annihilator]
  intro m
  rw [algebraMap_smul]
  induction m using LocalizedModule.induction_on with
  | h u s =>
    rw [LocalizedModule.smul'_mk, Algebra.smul_def]
    rw [RingHom.mem_ker] at hx
    change LocalizedModule.mk (G.coeffHom x * u) s = 0
    rw [hx, zero_mul, LocalizedModule.zero_mk]

/-- `supp:cm-localization`, upper bound: dim (𝒰_G)_𝔭 ≤ ht 𝔭 − ρ for every prime 𝔭 of S_G. A
chain of length k in the support contracts to a chain of primes of S_G from a prime containing I
to a prime contained in 𝔭; prefixing a chain of length ρ ≤ ht I below its first member gives
ρ + k ≤ ht 𝔭. -/
theorem incidence_localized_supportDim_le (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime] :
    Module.supportDim (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl G.IncidenceRing) ≤
      ((𝔭.height - G.rho : ℕ∞) : WithBot ℕ∞) := by
  let Rp := Localization.AtPrime 𝔭
  let f : Module.support Rp (LocalizedModule 𝔭.primeCompl G.IncidenceRing) →
      PrimeSpectrum (IncCoeffRing E) := fun q =>
    ⟨q.1.asIdeal.comap (algebraMap (IncCoeffRing E) Rp), Ideal.IsPrime.comap _⟩
  have hf : StrictMono f := by
    intro a b hab
    change (IsLocalization.orderEmbedding 𝔭.primeCompl Rp) a.1.asIdeal <
      (IsLocalization.orderEmbedding 𝔭.primeCompl Rp) b.1.asIdeal
    exact (IsLocalization.orderEmbedding 𝔭.primeCompl Rp).strictMono hab
  rw [Module.supportDim, Order.krullDim]
  refine iSup_le fun l => ?_
  let l' := l.map f hf
  have hhead : RingHom.ker G.coeffHom ≤ l'.head.asIdeal :=
    G.ker_coeffHom_le_comap_of_mem_support 𝔭 l.head.1 l.head.2
  have hlast : l'.last ≤ ⟨𝔭, ‹_›⟩ := by
    change (l.last.1.asIdeal.comap (algebraMap (IncCoeffRing E) Rp)) ≤ 𝔭
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal l.last.1.2.ne_top)).trans
      (Localization.AtPrime.under_maximalIdeal (I := 𝔭)).le
  have hρ : (G.rho : ℕ∞) ≤ Order.height l'.head := by
    rw [← PrimeSpectrum.height_eq_orderHeight]
    exact G.rho_le_height_ker_coeffHom.trans (Ideal.height_mono hhead)
  obtain ⟨m, hm_last, hm_len⟩ := Order.exists_series_of_le_height l'.head hρ
  have hlen := Order.length_le_height (p := m.smash l' hm_last) (x := ⟨𝔭, ‹_›⟩)
    (by simpa using hlast)
  rw [← PrimeSpectrum.height_eq_orderHeight] at hlen
  simp only [RelSeries.smash_length, hm_len, l'] at hlen
  push_cast at hlen
  refine WithBot.coe_le_coe.mpr ?_
  exact ENat.le_sub_of_add_le_left (ENat.natCast_ne_top _) hlen

/-- `supp:cm-localization`, dimension: at every prime 𝔭 ⊇ I = ker(S_G → 𝒰_G) of S_G,
dim (𝒰_G)_𝔭 = ht 𝔭 − ρ, the dimension being the support dimension over (S_G)_𝔭. -/
theorem incidence_localized_supportDim (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (h𝔭 : RingHom.ker G.coeffHom ≤ 𝔭) :
    Module.supportDim (Localization.AtPrime 𝔭) (LocalizedModule 𝔭.primeCompl G.IncidenceRing) =
      ((𝔭.height - G.rho : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨hlow, hup⟩ := G.incidence_localized_depth_bounds 𝔭 h𝔭
  exact le_antisymm (G.incidence_localized_supportDim_le 𝔭) (hlow.trans hup)

/-- `supp:cm-localization`: at every prime 𝔭 ⊇ I = ker(S_G → 𝒰_G) of S_G,
depth_{(S_G)_𝔭} (𝒰_G)_𝔭 = ht 𝔭 − ρ = dim (𝒰_G)_𝔭. Thus (𝒰_G)_𝔭 is a Cohen–Macaulay
(S_G)_𝔭-module. -/
theorem incidence_localized_cohenMacaulay (𝔭 : Ideal (IncCoeffRing E)) [𝔭.IsPrime]
    (h𝔭 : RingHom.ker G.coeffHom ≤ 𝔭) :
    IsLocalRing.depth (ModuleCat.of (Localization.AtPrime 𝔭)
        (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) = 𝔭.height - G.rho ∧
      (IsLocalRing.depth (ModuleCat.of (Localization.AtPrime 𝔭)
          (LocalizedModule 𝔭.primeCompl G.IncidenceRing)) : WithBot ℕ∞) =
        Module.supportDim (Localization.AtPrime 𝔭)
          (LocalizedModule 𝔭.primeCompl G.IncidenceRing) := by
  obtain ⟨hlow, hup⟩ := G.incidence_localized_depth_bounds 𝔭 h𝔭
  rw [G.incidence_localized_supportDim 𝔭 h𝔭] at hup ⊢
  have h := le_antisymm hup hlow
  exact ⟨WithBot.coe_inj.mp h, h⟩

/-- `supp:cm-localization`, the height of the kernel: ht I = ρ for I = ker(S_G → 𝒰_G). The lower
bound is `rho_le_height_ker_coeffHom`; at 𝔭 = I the support of (𝒰_G)_I is the closed point, so
ht I − ρ = dim (𝒰_G)_I = 0. -/
theorem height_ker_coeffHom : (RingHom.ker G.coeffHom).height = G.rho := by
  set I := RingHom.ker G.coeffHom
  have : I.IsPrime := RingHom.ker_isPrime _
  refine le_antisymm ?_ G.rho_le_height_ker_coeffHom
  let Rp := Localization.AtPrime I
  have hsub :
      Subsingleton (Module.support Rp (LocalizedModule I.primeCompl G.IncidenceRing)) := by
    refine ⟨fun a b => Subtype.ext (PrimeSpectrum.ext ?_)⟩
    have hcomap (q : Module.support Rp (LocalizedModule I.primeCompl G.IncidenceRing)) :
        q.1.asIdeal.comap (algebraMap (IncCoeffRing E) Rp) = I :=
      le_antisymm ((Ideal.comap_mono (IsLocalRing.le_maximalIdeal q.1.2.ne_top)).trans
          (Localization.AtPrime.under_maximalIdeal (I := I)).le)
        (G.ker_coeffHom_le_comap_of_mem_support I q.1 q.2)
    exact (IsLocalization.orderEmbedding I.primeCompl Rp).injective
      ((hcomap a).trans (hcomap b).symm)
  have h := G.incidence_localized_supportDim I le_rfl
  have hle : Module.supportDim Rp (LocalizedModule I.primeCompl G.IncidenceRing) ≤ 0 :=
    Order.krullDim_nonpos_of_subsingleton
  rw [h] at hle
  have : I.height - G.rho ≤ 0 := by exact_mod_cast hle
  rwa [tsub_le_iff_right, zero_add] at this

end LocalizedDimension

end BPFixedPoints.Multigraph
