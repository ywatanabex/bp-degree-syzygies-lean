import Mathlib.RingTheory.Valuation.LocalSubring

/-! # Valuation-ring criterion for integrality -/

namespace BPFixedPoints.IntegralTools

/-- Valuation-ring criterion for integrality of a field element, allowing a nonzero kernel in the ring homomorphism. -/
theorem integralElem_of_valuationSubrings
    {R K : Type*} [CommRing R] [Field K] (f : R →+* K) (x : K)
    (hx : ∀ O : ValuationSubring K, (∀ r, f r ∈ O) → x ∈ O) :
    f.IsIntegralElem x := by
  let : Algebra R K := f.toAlgebra
  have hx' : x ∈ (⨅ O : {O : ValuationSubring K //
      (f.range : Set K) ⊆ O.toSubring}, O.val.toSubring) := by
    rw [Subring.mem_iInf]
    intro O
    exact hx O.val (fun r => O.property ⟨r, rfl⟩)
  rw [iInf_valuationSubring_superset, Subring.closure_eq] at hx'
  have hint : IsIntegral f.range x := by
    exact hx'
  let : Algebra R f.range := f.rangeRestrict.toAlgebra
  have : IsScalarTower R f.range K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.IsIntegral R f.range :=
    ⟨RingHom.isIntegral_of_surjective _ f.rangeRestrict_surjective⟩
  exact isIntegral_trans x hint

end BPFixedPoints.IntegralTools
