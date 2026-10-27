import BPFixedPoints.Incidence.IncidencePrimeDepthTools
import BPFixedPoints.Incidence.IncidenceParameterFree
import BPFixedPoints.Incidence.IncidenceMaximalDepth

/-! # Depth equals dimension at every prime of the incidence ring

For every prime P of the chart-intersection ring 𝒰_G, the localization at P has Mathlib's
Ext depth equal to its Krull dimension, which is the height of P
(`incidence_cohenMacaulay_at_prime`, `incidence_cohenMacaulay_all_primes`). This is the depth
notion of `incidence_cohenMacaulay`, which treats the maximal ideals.

The proof does not localize the free resolution over the coefficient ring, as the paper's
supplement does. It takes a tuple on the finite-quotient parameter locus. Over the polynomial ring
in d_G parameters, 𝒰_G is finite and free (`incidence_parameter_finite_free`). Every prime
localization of that polynomial ring has a regular sequence of dimension length
(`primeDimRegular_mvPolynomial_fin`). The sequence stays regular in (𝒰_G)_P along the faithfully
flat local map, and integrality bounds the height of P by the height of the prime below it.

The module statement over the coefficient ring S_G, depth (𝒰_G)_𝔭 ≥ ht 𝔭 − ρ at primes 𝔭 of
S_G, is not stated separately.
-/

namespace BPFixedPoints.Multigraph

open ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

local instance incPrimeDepthNoetherian : IsNoetherianRing G.IncidenceRing :=
  G.incidence_cohenMacaulay.1

/-- Every prime localization of the incidence ring has a regular sequence in its maximal ideal
whose length is at least its Krull dimension. -/
theorem incidence_primeDimRegular : PrimeDimRegular G.IncidenceRing := by
  obtain ⟨a, ha⟩ := G.incidence_finite_parameter_open.2.1
  let := G.incidenceParameterAlgebra a
  have h := G.incidence_parameter_finite_free a ha
  have : Module.Free (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := h.1
  have : Module.Finite (MvPolynomial (Fin G.dG) ℂ) G.IncidenceRing := h.2.1
  exact (primeDimRegular_mvPolynomial_fin ℂ G.dG).of_finite_flat

/-- Depth equals Krull dimension at the localization of the incidence ring at any prime. -/
theorem incidence_cohenMacaulay_at_prime (P : Ideal G.IncidenceRing) [P.IsPrime] :
    (IsLocalRing.depth (R := Localization.AtPrime P)
      (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime P) :=
  G.incidence_primeDimRegular.depth_eq P

/-- At every prime, depth and Krull dimension of the localization both equal the height. -/
theorem incidence_local_depth_eq_height (P : Ideal G.IncidenceRing) [P.IsPrime] :
    (IsLocalRing.depth (R := Localization.AtPrime P)
      (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
      P.height ∧ ringKrullDim (Localization.AtPrime P) = P.height := by
  have hd := IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P)
  exact ⟨(G.incidence_cohenMacaulay_at_prime P).trans hd, hd⟩

/-- The incidence ring is Noetherian and depth equals Krull dimension at every prime
localization, with Mathlib's Ext depth. -/
theorem incidence_cohenMacaulay_all_primes :
    IsNoetherianRing G.IncidenceRing ∧ ∀ (P : Ideal G.IncidenceRing) [P.IsPrime],
      (IsLocalRing.depth (R := Localization.AtPrime P)
        (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) : WithBot ℕ∞) =
        ringKrullDim (Localization.AtPrime P) :=
  ⟨inferInstance, fun P _ => G.incidence_cohenMacaulay_at_prime P⟩

end BPFixedPoints.Multigraph
