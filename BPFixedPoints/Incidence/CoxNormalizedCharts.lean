import BPFixedPoints.Incidence.Chart

/-! # Normalized homogeneous-coordinate charts, independently of incidence quotients

Start with two homogeneous variables at every vertex and universal coefficient
variables. Setting one chosen homogeneous variable at each vertex to one gives
the original affine vertex/coefficient polynomial ring. This is normalization
on a projective chart; the global Proj comparison is a separate construction.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]

/-- Homogeneous vertex variables and independent universal coefficients. -/
abbrev IncCoxVar (V E : Type) := (V × Fin 2) ⊕ IncCoeffIdx E
abbrev IncCoxRing (V E : Type) := MvPolynomial (IncCoxVar V E) ℂ

/-- Chosen nonzero homogeneous coordinate, normalized to one. -/
def incCoxPivot (σ : V → Bool) (v : V) : Fin 2 := if σ v then 1 else 0
/-- Remaining affine coordinate on the chosen homogeneous chart. -/
def incCoxOther (σ : V → Bool) (v : V) : Fin 2 := if σ v then 0 else 1

noncomputable def incCoxNormalization (σ : V → Bool) (v : V) : IncCoxRing V E :=
  X (Sum.inl (v, incCoxPivot σ v)) - 1
noncomputable def incCoxNormalizationIdeal (σ : V → Bool) : Ideal (IncCoxRing V E) :=
  Ideal.span (Set.range (incCoxNormalization (E := E) σ))
abbrev IncNormalizedCoxRing (σ : V → Bool) :=
  IncCoxRing V E ⧸ incCoxNormalizationIdeal (E := E) σ

noncomputable def incCoxNormalizedValue (σ : V → Bool) :
    IncCoxVar V E → MvPolynomial (IncChartVar V E) ℂ
  | Sum.inl (v, α) => incCoord (σ v) α (X (Sum.inl v))
  | Sum.inr c => X (Sum.inr c)

/-- Ambient dehomogenization, before imposing any edge equation. -/
noncomputable def incCoxDehomogenize (σ : V → Bool) :
    IncCoxRing V E →ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  aeval (incCoxNormalizedValue σ)

theorem incCoxDehomogenize_normalization (σ : V → Bool) (v : V) :
    incCoxDehomogenize σ (incCoxNormalization (E := E) σ v) = 0 := by
  cases hv : σ v <;> simp [incCoxDehomogenize, incCoxNormalization,
    incCoxNormalizedValue, incCoxPivot, incCoord, hv]

noncomputable def incNormalizedCoxToChart (σ : V → Bool) :
    IncNormalizedCoxRing (E := E) σ →ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  Ideal.Quotient.liftₐ _ (incCoxDehomogenize σ) <| by
    intro p hp
    have hk : incCoxNormalizationIdeal (E := E) σ ≤ RingHom.ker (incCoxDehomogenize σ).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨v, rfl⟩
      exact incCoxDehomogenize_normalization σ v
    exact hk hp

@[simp] theorem incNormalizedCoxToChart_mk (σ : V → Bool) (p : IncCoxRing V E) :
    incNormalizedCoxToChart σ (Ideal.Quotient.mk _ p) = incCoxDehomogenize σ p := rfl

theorem incNormalizedCox_pivot (σ : V → Bool) (v : V) :
    Ideal.Quotient.mk (incCoxNormalizationIdeal (E := E) σ)
      (X (Sum.inl (v, incCoxPivot σ v))) = 1 := by
  rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨v, rfl⟩

noncomputable def incChartToNormalizedCox (σ : V → Bool) :
    MvPolynomial (IncChartVar V E) ℂ →ₐ[ℂ] IncNormalizedCoxRing (E := E) σ :=
  aeval (fun i => Ideal.Quotient.mk (incCoxNormalizationIdeal (E := E) σ)
    (X (match i with
      | Sum.inl v => Sum.inl (v, incCoxOther σ v)
      | Sum.inr c => Sum.inr c)))

theorem incChartToNormalizedCox_left (σ : V → Bool) :
    (incChartToNormalizedCox σ).comp (incNormalizedCoxToChart σ) =
      AlgHom.id ℂ (IncNormalizedCoxRing (E := E) σ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with ⟨v, α⟩ | c
  · have hp := incNormalizedCox_pivot (E := E) σ v
    fin_cases α <;> cases hv : σ v <;>
      simp [incCoxPivot, hv] at hp <;>
      simp [incCoxDehomogenize, incCoxNormalizedValue, incChartToNormalizedCox,
        incCoxOther, incCoord, hv, hp]
  · simp [incCoxDehomogenize, incCoxNormalizedValue, incChartToNormalizedCox]

theorem incChartToNormalizedCox_right (σ : V → Bool) :
    (incNormalizedCoxToChart σ).comp (incChartToNormalizedCox σ) =
      AlgHom.id ℂ (MvPolynomial (IncChartVar V E) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with v | c
  · cases hv : σ v <;>
      simp [incChartToNormalizedCox, incCoxDehomogenize, incCoxNormalizedValue,
        incCoxOther, incCoord, hv]
  · simp [incChartToNormalizedCox, incCoxDehomogenize, incCoxNormalizedValue]

/-- The independently normalized homogeneous coordinate chart is the original ambient chart. -/
noncomputable def incNormalizedCoxChartEquiv (σ : V → Bool) :
    IncNormalizedCoxRing (E := E) σ ≃ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  AlgEquiv.ofAlgHom (incNormalizedCoxToChart σ) (incChartToNormalizedCox σ)
    (incChartToNormalizedCox_right σ) (incChartToNormalizedCox_left σ)

end BPFixedPoints.Multigraph
