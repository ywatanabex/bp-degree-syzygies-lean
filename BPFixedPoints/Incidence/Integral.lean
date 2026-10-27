import BPFixedPoints.Incidence.Torus
import BPFixedPoints.Incidence.ValuationTools

/-!
# Integrality of the universal incidence ring over the coefficient ring

Any valuation ring containing the coefficients contains at least one of each
vertex coordinate and its inverse. These choices give an affine chart.
A function extending to all charts therefore belongs to every such valuation
ring; the valuation-ring description of integral closure implies integrality
over the coefficient ring. No sheaf-cohomology or dimension hypotheses are used.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable (G : Multigraph V E)

/-- Map from the coefficient ring to the common torus. -/
noncomputable def coeffTorusHom : IncCoeffRing E →ₐ[ℂ] G.IncTorusRing :=
  G.IncidenceRing.val.comp G.coeffHom

@[simp] theorem coeffTorusHom_X (c : IncCoeffIdx E) :
    G.coeffTorusHom (X c) =
      Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
        (X (Sum.inr (Sum.inr c))) := by
  simp [coeffTorusHom, coeffHom]

/-- Functions extending to all charts belong to every valuation ring containing the coefficients. -/
theorem incidenceRing_mem_valuationSubring
    {K : Type*} [Field K] [Algebra ℂ K] (φ : G.IncTorusRing →ₐ[ℂ] K)
    (O : ValuationSubring K) (hO : ∀ c, φ (G.coeffTorusHom c) ∈ O)
    (x : G.IncidenceRing) : φ x.val ∈ O := by
  classical
  let t : V → K := fun v =>
    φ (Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel)) (X (Sum.inl v)))
  let σ : V → Bool := fun v => if t v ∈ O then false else true
  have hvars : ∀ i : IncChartVar V E, φ (G.incChartVal σ i) ∈ O := by
    rintro (v | c)
    · by_cases hv : t v ∈ O
      · simp [incChartVal, σ, hv, t]
      · have hinv : (t v)⁻¹ ∈ O := (O.mem_or_inv_mem (t v)).resolve_left hv
        have hts := congrArg φ (G.incTorus_ts v)
        simp only [map_mul, map_one] at hts
        have hs : φ (Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
            (X (Sum.inr (Sum.inl v)))) = (t v)⁻¹ :=
          eq_inv_of_mul_eq_one_right hts
        simpa [incChartVal, σ, hv, hs] using hinv
    · simpa [incChartVal] using hO (X c)
  have hpoly : ∀ p : MvPolynomial (IncChartVar V E) ℂ,
      φ (aeval (G.incChartVal σ) p) ∈ O := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C c => simpa using hO (C c)
    | add p q hp hq => simpa only [map_add] using O.add_mem _ _ hp hq
    | mul_X p i hp =>
        simpa only [map_mul, aeval_X] using O.mul_mem _ _ hp (hvars i)
  have hx : x.val ∈ (G.incChartMap σ).range :=
    (iInf_le (fun σ => (G.incChartMap σ).range) σ) x.property
  obtain ⟨q, hq⟩ := hx
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [← hq]
  change φ (aeval (G.incChartVal σ) p) ∈ O
  exact hpoly p

/-- The universal incidence ring is integral over the coefficient ring. -/
theorem coeffHom_isIntegral : G.coeffHom.toRingHom.IsIntegral := by
  let K := FractionRing G.IncTorusRing
  let φ : G.IncTorusRing →ₐ[ℂ] K := Algebra.algHom ℂ G.IncTorusRing K
  let ψ : G.IncidenceRing →ₐ[ℂ] K := φ.comp G.IncidenceRing.val
  have hψ : Function.Injective ψ :=
    (IsFractionRing.injective G.IncTorusRing K).comp Subtype.val_injective
  intro x
  apply RingHom.IsIntegralElem.of_map (g := ψ.toRingHom) hψ
  apply IntegralTools.integralElem_of_valuationSubrings
  intro O hO
  exact G.incidenceRing_mem_valuationSubring φ O hO x

end BPFixedPoints.Multigraph
