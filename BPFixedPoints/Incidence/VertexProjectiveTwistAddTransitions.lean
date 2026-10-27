import BPFixedPoints.Incidence.VertexProjectiveTwistPairChartComparison

/-! # Addition of original twists multiplies their actual transition units

The same original standard pair units, geometric vertex pullbacks and
fixed vertex products are used, including the reversed pair and empty product.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
variable (R : Type) [CommRing R]

/-- Addition preserves every original standard pair unit, including the inverse transition. -/
theorem twistSheafPairUnit_add (m n : ℤ) (i j : Fin 2) :
    twistSheafPairUnit R (m+n) i j = twistSheafPairUnit R m i j * twistSheafPairUnit R n i j := by
  fin_cases i <;> fin_cases j
  · change (1 : Γ((standardOpen R 0).toScheme,⊤)ˣ) = 1*1
    rw [one_mul]
  · exact twistOverlapUnit_add R m n
  · change (twistOverlapUnit R (m+n))⁻¹ = (twistOverlapUnit R m)⁻¹ * (twistOverlapUnit R n)⁻¹
    rw [twistOverlapUnit_add,mul_inv]
  · change (1 : Γ((standardOpen R 1).toScheme,⊤)ˣ) = 1*1
    rw [one_mul]

variable (V : Type) [Fintype V]

/-- The original geometric factor pullback retains the product transition for the sum of twists. -/
theorem vertexTwistPairFactorUnit_add (a b : V → ℤ) (σ τ : V → Fin 2) (v : V) :
    vertexTwistPairFactorUnit R V (a+b) σ τ v =
      vertexTwistPairFactorUnit R V a σ τ v * vertexTwistPairFactorUnit R V b σ τ v := by
  change Units.map _ (twistSheafPairUnit R (a v+b v) (σ v) (τ v)) = _
  rw [twistSheafPairUnit_add,map_mul]
  rfl

/-- Addition of the original integral multi-twists multiplies their original actual product-chart transition units. -/
theorem vertexTwistSheafPairUnit_add (a b : V → ℤ) (σ τ : V → Fin 2) :
    vertexTwistSheafPairUnit R V (a+b) σ τ =
      vertexTwistSheafPairUnit R V a σ τ * vertexTwistSheafPairUnit R V b σ τ := by
  simp only [vertexTwistSheafPairUnit,vertexTwistPairFactorUnit_add,Finset.prod_mul_distrib]

end BPFixedPoints.ProjectiveLine
