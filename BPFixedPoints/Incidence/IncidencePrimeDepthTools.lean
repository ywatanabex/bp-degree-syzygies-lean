import BPFixedPoints.Incidence.RegularDepthTools
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.MonicSpan
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.AdjoinRoot

/-! # Depth at every prime of polynomial rings and of their finite flat extensions

A local ring satisfies `HasDimRegularSequence` when its maximal ideal contains a ring-regular
sequence whose length is at least the Krull dimension. A ring satisfies `PrimeDimRegular` when
every localization at a prime does. For a Noetherian local ring this property gives
depth = Krull dimension with Mathlib's Ext depth (`HasDimRegularSequence.depth_eq`).

Proved here:
* the property is invariant under ring isomorphisms and holds in dimension zero;
* it passes from a Noetherian ring R to R[X]. At a prime over the maximal ideal of a local base,
  either the prime is extended from the base or it contains a monic polynomial; a monic
  polynomial followed by a base regular sequence is weakly regular, since the quotient by a monic
  polynomial is free over the base;
* hence every finite-variable polynomial ring over a field has it
  (`primeDimRegular_mvPolynomial_fin`);
* it passes along finite flat algebras (`PrimeDimRegular.of_finite_flat`): the base sequence stays
  regular after the faithfully flat local map, and integrality bounds the height of a prime by the
  height of the prime below it. Flatness gives the converse height inequality by going-down.

Regular local rings in general, and Cohen–Macaulay rings that are not finite flat over a
polynomial ring, are not treated.
-/

namespace BPFixedPoints.ResolutionTools

open RingTheory.Sequence IsLocalRing Polynomial
open scoped Pointwise

universe u

/-- A local ring has a ring-regular sequence in its maximal ideal whose length is at least
its Krull dimension. -/
def HasDimRegularSequence (A : Type u) [CommRing A] [IsLocalRing A] : Prop :=
  ∃ rs : List A, (∀ r ∈ rs, r ∈ maximalIdeal A) ∧ IsRegular A rs ∧
    ringKrullDim A ≤ (rs.length : WithBot ℕ∞)

/-- Every localization at a prime has a regular sequence of length at least its dimension. -/
def PrimeDimRegular (R : Type u) [CommRing R] : Prop :=
  ∀ (p : Ideal R) [p.IsPrime], HasDimRegularSequence (Localization.AtPrime p)

/-- The local property is invariant under ring isomorphisms. -/
theorem HasDimRegularSequence.of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (e : A ≃+* B) (h : HasDimRegularSequence A) :
    HasDimRegularSequence B := by
  obtain ⟨rs, hmem, hreg, hdim⟩ := h
  refine ⟨rs.map e, ?_, isRegular_map_ringEquiv e rs hreg, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' := hmem x hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
    exact fun hu => hx' ((isUnit_map_iff e x).mp hu)
  · rw [← ringKrullDim_eq_of_ringEquiv e, List.length_map]
    exact hdim

/-- A local ring of dimension at most zero has the empty sequence. -/
theorem hasDimRegularSequence_of_ringKrullDim_le_zero (A : Type u) [CommRing A]
    [IsLocalRing A] (h : ringKrullDim A ≤ 0) : HasDimRegularSequence A :=
  ⟨[], by simp, IsRegular.nil A A, by simpa using h⟩

/-- The prime-localization property is invariant under ring isomorphisms. -/
theorem PrimeDimRegular.of_ringEquiv {R S : Type u} [CommRing R] [CommRing S]
    (e : R ≃+* S) (h : PrimeDimRegular R) : PrimeDimRegular S := by
  intro p hp
  exact (h (p.comap e)).of_ringEquiv (IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (p.comap e)) (Localization.AtPrime p) e (e.map_primeCompl_comap_eq p))

/-- A ring of dimension at most zero has the prime-localization property. -/
theorem primeDimRegular_of_ringKrullDim_le_zero (R : Type u) [CommRing R]
    (h : ringKrullDim R ≤ 0) : PrimeDimRegular R := by
  intro p hp
  apply hasDimRegularSequence_of_ringKrullDim_le_zero
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)]
  exact Ideal.height_le_ringKrullDim_of_isPrime.trans h

/-- Heights do not increase along an integral extension. -/
theorem height_le_height_under_of_isIntegral {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsIntegral R A] (P : Ideal A) [P.IsPrime] :
    P.height ≤ (P.under R).height := by
  let f : PrimeSpectrum A → PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R A)
  have hf : StrictMono f := by
    intro x y hxy
    exact Ideal.IsIntegral.under_lt_under (R := R) hxy
  have h := Order.height_le_height_apply_of_strictMono f hf ⟨P, inferInstance⟩
  rw [← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h

/-- Flat algebras satisfy going-down, so heights do not decrease. -/
theorem height_under_le_height_of_flat {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Flat R A] [IsNoetherianRing R] [IsNoetherianRing A]
    (P : Ideal A) [P.IsPrime] :
    (P.under R).height ≤ P.height := by
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
  exact le_self_add

/-- In a finite flat extension every prime has the height of the prime below it. -/
theorem height_eq_height_under_of_finite_flat {R A : Type u} [CommRing R] [CommRing A]
    [Algebra R A] [Module.Finite R A] [Module.Flat R A] [IsNoetherianRing R]
    [IsNoetherianRing A] (P : Ideal A) [P.IsPrime] : P.height = (P.under R).height :=
  le_antisymm (height_le_height_under_of_isIntegral P) (height_under_le_height_of_flat P)

/-- Over any ring, the quotient by a monic polynomial is a free module. -/
theorem free_quotSMulTop_monic {B : Type u} [CommRing B] {f : B[X]} (hf : f.Monic) :
    Module.Free B (QuotSMulTop f B[X]) := by
  have h : f • (⊤ : Ideal B[X]) = Ideal.span {f} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  let e := (Ideal.quotientEquivAlgOfEq B h).toLinearEquiv
  exact Module.Free.of_basis ((AdjoinRoot.powerBasis' hf).basis.map e.symm)

/-- A monic polynomial followed by a ring-regular sequence of constants is weakly regular. -/
theorem isWeaklyRegular_monic_cons {B : Type u} [CommRing B] {f : B[X]} (hf : f.Monic)
    (xs : List B) (hxs : IsWeaklyRegular B xs) :
    IsWeaklyRegular B[X] (f :: xs.map (algebraMap B B[X])) := by
  rw [isWeaklyRegular_cons_iff]
  refine ⟨hf.isRegular.left, ?_⟩
  have := free_quotSMulTop_monic hf
  have hw := hxs.isWeaklyRegular_lTensor (M₂ := QuotSMulTop f B[X])
  have hw' := ((TensorProduct.rid B (QuotSMulTop f B[X])).isWeaklyRegular_congr xs).mp hw
  exact (isWeaklyRegular_map_algebraMap_iff B[X] (QuotSMulTop f B[X]) xs).mpr hw'

/-- The polynomial ring over a Noetherian local ring, localized at a prime over the maximal
ideal, inherits the local property. -/
theorem hasDimRegularSequence_polynomial_atPrime {B : Type u} [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] (hB : HasDimRegularSequence B) (Q : Ideal B[X]) [Q.IsPrime]
    (hQ : Q.comap C = maximalIdeal B) : HasDimRegularSequence (Localization.AtPrime Q) := by
  obtain ⟨xs, hmem, hreg, hdim⟩ := hB
  let L := Localization.AtPrime Q
  have hxsQ : ∀ r ∈ xs.map (algebraMap B B[X]), r ∈ Q := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have : x ∈ Q.comap C := hQ ▸ hmem x hx
    exact this
  have hmax : ∀ rs : List B[X], (∀ r ∈ rs, r ∈ Q) →
      ∀ r ∈ rs.map (algebraMap B[X] L), r ∈ maximalIdeal L := by
    intro rs hrs r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff L Q x).mpr (hrs x hx)
  have hdimL : ringKrullDim L = Q.height := IsLocalization.AtPrime.ringKrullDim_eq_height Q L
  by_cases hQe : Q = (maximalIdeal B).map C
  · have hw : IsWeaklyRegular B[X] (xs.map (algebraMap B B[X])) :=
      hreg.toIsWeaklyRegular.of_flat
    refine ⟨_, hmax _ hxsQ, hw.isRegular_of_isLocalization_of_mem L Q hxsQ, ?_⟩
    rw [hdimL, List.length_map, List.length_map]
    have hh : Q.height = (maximalIdeal B).height := by
      rw [hQe]
      exact Polynomial.height_map_C (maximalIdeal B)
    rw [hh, IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  · have ism : (Q.comap C).IsMaximal := hQ ▸ maximalIdeal.isMaximal B
    obtain ⟨f, hf, hQf⟩ := Polynomial.exists_monic_span_sup_map_eq B Q ism (by rwa [hQ])
    have hfQ : f ∈ Q := hQf ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f)
    have hall : ∀ r ∈ f :: xs.map (algebraMap B B[X]), r ∈ Q := by
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hfQ
      · exact hxsQ r hr
    have hw := isWeaklyRegular_monic_cons hf xs hreg.toIsWeaklyRegular
    refine ⟨_, hmax _ hall, hw.isRegular_of_isLocalization_of_mem L Q hall, ?_⟩
    rw [hdimL]
    calc (Q.height : WithBot ℕ∞) ≤ ringKrullDim B[X] := Ideal.height_le_ringKrullDim_of_isPrime
      _ = ringKrullDim B + 1 := Polynomial.ringKrullDim_of_isNoetherianRing
      _ ≤ (xs.length : WithBot ℕ∞) + 1 := add_le_add_left hdim 1
      _ = _ := by simp

/-- The prime-localization property passes to one polynomial variable over a Noetherian ring. -/
theorem PrimeDimRegular.polynomial {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : PrimeDimRegular R) : PrimeDimRegular R[X] := by
  intro p hp
  let q := p.comap C
  let S := (Localization.AtPrime q)[X]
  let pc := Submonoid.map Polynomial.C.toMonoidHom q.primeCompl
  let : Algebra R[X] S := Polynomial.algebra R (Localization.AtPrime q)
  have : IsLocalization pc S := Polynomial.isLocalization _ _
  let pS := p.map (algebraMap R[X] S)
  have disj : Disjoint (pc : Set R[X]) (p : Set R[X]) := by
    simpa [pc, q] using! Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr (fun _ a ↦ a))
  have : pS.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint pc _ _ ‹_› disj
  have : IsLocalization.AtPrime (Localization.AtPrime pS) p := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization pc
      (Localization.AtPrime pS) pS
    exact (IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj).symm
  have eq : Ideal.comap C pS = maximalIdeal (Localization.AtPrime q) := by
    rw [← IsLocalization.map_under q.primeCompl _ (Ideal.comap C pS),
      ← IsLocalization.map_under q.primeCompl _ (maximalIdeal (Localization.AtPrime q))]
    simp only [Ideal.comap_comap, S, pS]
    rw [← Polynomial.algebraMap_eq (R := Localization.AtPrime q),
      ← IsScalarTower.algebraMap_eq R (Localization.AtPrime q) (Localization.AtPrime q)[X],
      IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime q)[X], ← Ideal.comap_comap,
      ← Ideal.under_def R[X], IsLocalization.under_map_of_isPrime_disjoint pc _ ‹_› disj]
    simp [q, IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  have h := hasDimRegularSequence_polynomial_atPrime (hR q) pS eq
  exact h.of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime pS) (Localization.AtPrime p)).toRingEquiv

/-- Every finite-variable polynomial ring over a field has the prime-localization property. -/
theorem primeDimRegular_mvPolynomial_fin (K : Type u) [Field K] :
    ∀ n : ℕ, PrimeDimRegular (MvPolynomial (Fin n) K)
  | 0 => (primeDimRegular_of_ringKrullDim_le_zero K
      (ringKrullDim_eq_zero_of_field K).le).of_ringEquiv
      (MvPolynomial.isEmptyRingEquiv K (Fin 0)).symm
  | n + 1 => ((primeDimRegular_mvPolynomial_fin K n).polynomial).of_ringEquiv
      (MvPolynomial.finSuccEquiv K n).toRingEquiv.symm

/-- The one-variable polynomial ring over a field has the prime-localization property. -/
theorem primeDimRegular_polynomial_field (K : Type u) [Field K] : PrimeDimRegular K[X] :=
  (primeDimRegular_of_ringKrullDim_le_zero K (ringKrullDim_eq_zero_of_field K).le).polynomial

/-- A finite flat extension inherits the prime-localization property. The regular sequence of
the base localization stays regular after the faithfully flat local map, and integrality
bounds the height of each prime by the height of the prime below it. -/
theorem PrimeDimRegular.of_finite_flat {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Module.Finite R A] [Module.Flat R A] (hR : PrimeDimRegular R) : PrimeDimRegular A := by
  intro P hP
  let q := P.under R
  let := Localization.AtPrime.algebraOfLiesOver q P
  obtain ⟨xs, hmem, hreg, hdim⟩ := hR q
  have hloc : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime P)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom q P (algebraMap R A) Ideal.LiesOver.over
  have : Module.FaithfullyFlat (Localization.AtPrime q) (Localization.AtPrime P) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨xs.map (algebraMap _ _), ?_, hreg.of_faithfullyFlat, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have hx' := hmem x hx
    rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
    exact fun hu => hx' (IsLocalHom.map_nonunit x hu)
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), List.length_map]
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
    exact (WithBot.coe_le_coe.mpr (height_le_height_under_of_isIntegral P)).trans hdim

/-- In a Noetherian ring, the length of a ring-regular sequence is bounded by the Krull
dimension. -/
theorem regular_length_le_ringKrullDim {A : Type u} [CommRing A] [IsNoetherianRing A]
    (rs : List A) (hrs : IsRegular A rs) : (rs.length : WithBot ℕ∞) ≤ ringKrullDim A := by
  simpa only [Module.supportDim_self_eq_ringKrullDim] using regular_length_le_supportDim A rs hrs

/-- In a Noetherian local ring, a regular sequence of dimension length makes Mathlib's Ext depth
equal to the Krull dimension. -/
theorem HasDimRegularSequence.depth_eq {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (h : HasDimRegularSequence A) :
    (IsLocalRing.depth (ModuleCat.of A A) : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨xs, hmem, hreg, hdim⟩ := h
  have heq : ringKrullDim A = xs.length :=
    le_antisymm hdim (regular_length_le_ringKrullDim xs hreg)
  have hd : IsLocalRing.depth (ModuleCat.of A A) = (xs.length : ℕ∞) := by
    rw [IsLocalRing.depth_eq_sSup_length_isRegular]
    apply le_antisymm
    · apply sSup_le
      rintro n ⟨rs, hrs, _, rfl⟩
      have h := (regular_length_le_ringKrullDim rs hrs).trans (le_of_eq heq)
      exact_mod_cast h
    · exact le_sSup ⟨xs, hreg, hmem, rfl⟩
  rw [hd, heq]
  rfl

/-- A Noetherian ring with the prime-localization property has depth equal to Krull dimension
at every prime localization. -/
theorem PrimeDimRegular.depth_eq {A : Type u} [CommRing A] [IsNoetherianRing A]
    (h : PrimeDimRegular A) (P : Ideal A) [P.IsPrime] :
    (IsLocalRing.depth (R := Localization.AtPrime P)
      (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) :=
  (h P).depth_eq

end BPFixedPoints.ResolutionTools
