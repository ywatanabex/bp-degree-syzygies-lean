import BPFixedPoints.Incidence.Ring

/-!
# Coefficient elimination on incidence charts

Eliminate the constant coefficient for each edge to present the chart as a
polynomial ring in vertex coordinates and three free coefficients per edge.
Preserving edge IDs permits parallel edges.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial

set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable (G : Multigraph V E)

/-- Free chart variables: vertex coordinates and three coefficients for each edge. -/
abbrev IncFreeVar (V E : Type) := V ⊕ E × Fin 3

abbrev IncFreeRing (V E : Type) := MvPolynomial (IncFreeVar V E) ℂ

/-- Each coefficient after eliminating c₀₀ on the zero chart. -/
noncomputable def incFreeCoeff (e : E) (α β : Fin 2) : IncFreeRing V E :=
  if α = 0 then
    if β = 0 then
      -(X (Sum.inr (e, 0)) * X (Sum.inl (G.snd e)) +
        X (Sum.inr (e, 1)) * X (Sum.inl (G.fst e)) +
        X (Sum.inr (e, 2)) * X (Sum.inl (G.fst e)) * X (Sum.inl (G.snd e)))
    else X (Sum.inr (e, 0))
  else if β = 0 then X (Sum.inr (e, 1)) else X (Sum.inr (e, 2))

noncomputable def incFreeVal : IncChartVar V E → IncFreeRing V E
  | Sum.inl v => X (Sum.inl v)
  | Sum.inr (e, α, β) => G.incFreeCoeff e α β

theorem incFreeVal_eq_zero (e : E) :
    aeval G.incFreeVal (G.incChartEq (fun _ => false) e) = 0 := by
  simp [incChartEq, Fin.sum_univ_two, incCoord, incFreeVal, incFreeCoeff]
  ring

/-- Coefficient-elimination map from the zero chart to the free polynomial ring. -/
noncomputable def incChartToFree : G.IncChartRing (fun _ => false) →ₐ[ℂ] IncFreeRing V E :=
  Ideal.Quotient.liftₐ _ (aeval G.incFreeVal) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨e, rfl⟩; exact G.incFreeVal_eq_zero e
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

@[simp] theorem incChartToFree_mk (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartToFree (Ideal.Quotient.mk _ p) = aeval G.incFreeVal p := rfl

/-- Return free variables to the original chart. -/
noncomputable def incFreeToChart : IncFreeRing V E →ₐ[ℂ] G.IncChartRing (fun _ => false) :=
  aeval <| Sum.elim
    (fun v => Ideal.Quotient.mk _ (X (Sum.inl v)))
    (fun (e, k) => Ideal.Quotient.mk _ (X (Sum.inr
      (e, if k = 0 then 0 else 1, if k = 1 then 0 else 1))))

theorem incChartToFree_comp :
    G.incChartToFree.comp G.incFreeToChart = AlgHom.id ℂ (IncFreeRing V E) := by
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with v | ⟨e, k⟩
  · simp [incFreeToChart, incFreeVal]
  · fin_cases k <;> simp [incFreeToChart, incFreeVal, incFreeCoeff]

theorem incFreeToChart_comp :
    G.incFreeToChart.comp G.incChartToFree = AlgHom.id ℂ (G.IncChartRing (fun _ => false)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with v | ⟨e, α, β⟩
  · simp [incFreeToChart, incFreeVal]
  · have he : Ideal.Quotient.mk (Ideal.span (Set.range (G.incChartEq (fun _ => false))))
        (G.incChartEq (fun _ => false) e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)
    simp only [incChartEq, Fin.sum_univ_two, incCoord, Bool.false_eq_true, ↓reduceIte,
      Fin.isValue, one_ne_zero, mul_one, map_add, map_mul] at he
    fin_cases α <;> fin_cases β <;>
      simp [incFreeToChart, incFreeVal, incFreeCoeff]
    linear_combination -he

/-- **Polynomial chart presentation.** The zero chart is a polynomial ring in n+3m variables. -/
noncomputable def incChartZeroEquiv : G.IncChartRing (fun _ => false) ≃ₐ[ℂ] IncFreeRing V E :=
  AlgEquiv.ofAlgHom G.incChartToFree G.incFreeToChart
    G.incChartToFree_comp G.incFreeToChart_comp

/-- Exchange the two homogeneous-coordinate indices on the infinity chart. -/
def incFlip (b : Bool) : Fin 2 ≃ Fin 2 := if b then Equiv.swap 0 1 else Equiv.refl _

@[simp] theorem incFlip_involutive (b : Bool) (α : Fin 2) : incFlip b (incFlip b α) = α := by
  cases b <;> simp [incFlip]

def incChartFlipVar (σ : V → Bool) : IncChartVar V E → IncChartVar V E
  | Sum.inl v => Sum.inl v
  | Sum.inr (e, α, β) => Sum.inr (e, incFlip (σ (G.fst e)) α, incFlip (σ (G.snd e)) β)

@[simp] theorem incChartFlipVar_involutive (σ : V → Bool) (i : IncChartVar V E) :
    G.incChartFlipVar σ (G.incChartFlipVar σ i) = i := by
  rcases i with v | ⟨e, α, β⟩ <;> simp [incChartFlipVar]

theorem incChartFlip_eq (σ : V → Bool) (e : E) :
    rename (G.incChartFlipVar σ) (G.incChartEq σ e) = G.incChartEq (fun _ => false) e := by
  cases h₁ : σ (G.fst e) <;> cases h₂ : σ (G.snd e) <;>
    simp [incChartEq, Fin.sum_univ_two, incCoord, incChartFlipVar, incFlip, h₁, h₂] <;> ring

theorem incChartFlip_zero_eq (σ : V → Bool) (e : E) :
    rename (G.incChartFlipVar σ) (G.incChartEq (fun _ => false) e) = G.incChartEq σ e := by
  rw [← G.incChartFlip_eq σ e, rename_rename]
  simp only [Function.comp_def, incChartFlipVar_involutive]
  exact AlgHom.congr_fun rename_id _

noncomputable def incChartToZero (σ : V → Bool) :
    G.IncChartRing σ →ₐ[ℂ] G.IncChartRing (fun _ => false) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp (rename (G.incChartFlipVar σ))) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨e, rfl⟩
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, incChartFlip_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

noncomputable def incChartFromZero (σ : V → Bool) :
    G.IncChartRing (fun _ => false) →ₐ[ℂ] G.IncChartRing σ :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ ℂ _).comp (rename (G.incChartFlipVar σ))) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨e, rfl⟩
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, incChartFlip_zero_eq]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

@[simp] theorem incChartToZero_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartToZero σ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (G.incChartFlipVar σ) p) := rfl

@[simp] theorem incChartFromZero_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartFromZero σ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (G.incChartFlipVar σ) p) := rfl

noncomputable def incChartEquivZero (σ : V → Bool) :
    G.IncChartRing σ ≃ₐ[ℂ] G.IncChartRing (fun _ => false) :=
  AlgEquiv.ofAlgHom (G.incChartToZero σ) (G.incChartFromZero σ)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp)
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simp)

/-- **All-chart polynomial presentation.** Every chart is a polynomial ring in n+3m variables. -/
noncomputable def incChartEquiv (σ : V → Bool) : G.IncChartRing σ ≃ₐ[ℂ] IncFreeRing V E :=
  (G.incChartEquivZero σ).trans G.incChartZeroEquiv

@[simp] theorem incChartEquiv_mk (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartEquiv σ (Ideal.Quotient.mk _ p) =
      aeval G.incFreeVal (rename (G.incChartFlipVar σ) p) := rfl

@[simp] theorem incChartEquiv_symm_vertex (σ : V → Bool) (v : V) :
    (G.incChartEquiv σ).symm (X (Sum.inl v)) = Ideal.Quotient.mk _ (X (Sum.inl v)) := by
  apply (G.incChartEquiv σ).injective
  simp [incChartFlipVar, incFreeVal]

instance incChart_isDomain (σ : V → Bool) : IsDomain (G.IncChartRing σ) :=
  (G.incChartEquiv σ).injective.isDomain (G.incChartEquiv σ).toRingHom

instance incChart_isIntegrallyClosed (σ : V → Bool) : IsIntegrallyClosed (G.IncChartRing σ) :=
  IsIntegrallyClosed.of_equiv (G.incChartEquiv σ).symm.toRingEquiv

end BPFixedPoints.Multigraph
