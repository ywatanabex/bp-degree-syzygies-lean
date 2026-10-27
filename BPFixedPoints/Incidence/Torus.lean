import BPFixedPoints.Incidence.Chart

/-! # The common torus is a localization of a free polynomial ring -/

namespace BPFixedPoints.Multigraph

open MvPolynomial
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
variable (G : Multigraph V E)
variable (σ : V → Bool)

noncomputable def incFreeDen : IncFreeRing V E := ∏ v : V, X (Sum.inl v)

theorem incFreeDen_ne_zero : incFreeDen (V := V) (E := E) ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => X_ne_zero _)

abbrev IncLocalRing (V E : Type) [Fintype V] :=
  Localization.Away (incFreeDen (V := V) (E := E))

instance : IsDomain (IncLocalRing V E) := Localization.Away.isDomain incFreeDen_ne_zero

theorem incLocal_vertex_unit (v : V) :
    IsUnit (algebraMap (IncFreeRing V E) (IncLocalRing V E) (X (Sum.inl v))) :=
  IsLocalization.Away.isUnit_of_dvd (incFreeDen (V := V) (E := E))
    (Finset.dvd_prod_of_mem _ (Finset.mem_univ v))

noncomputable def incLocalInv (v : V) : IncLocalRing V E :=
  ↑((incLocal_vertex_unit (E := E) v).unit⁻¹)

@[simp] theorem incLocal_ts (v : V) :
    algebraMap (IncFreeRing V E) (IncLocalRing V E) (X (Sum.inl v)) * incLocalInv v = 1 := by
  simpa only [incLocalInv, IsUnit.unit_spec] using
    Units.mul_inv (incLocal_vertex_unit (E := E) v).unit

noncomputable def incLocalVal : IncTorusVar V E → IncLocalRing V E
  | Sum.inl v => if σ v then incLocalInv v
      else algebraMap (IncFreeRing V E) (IncLocalRing V E) (X (Sum.inl v))
  | Sum.inr (Sum.inl v) => if σ v then
      algebraMap (IncFreeRing V E) (IncLocalRing V E) (X (Sum.inl v)) else incLocalInv v
  | Sum.inr (Sum.inr (e, α, β)) => algebraMap (IncFreeRing V E) (IncLocalRing V E)
      (G.incFreeCoeff e (incFlip (σ (G.fst e)) α) (incFlip (σ (G.snd e)) β))

theorem incLocalVal_rel (i : V ⊕ E) : aeval (G.incLocalVal σ) (G.incTorusRel i) = 0 := by
  rcases i with v | e
  · cases h : σ v
    · simp [incTorusRel, incLocalVal, h]
    · simp [incTorusRel, incLocalVal, h]
      linear_combination incLocal_ts (E := E) v
  · have hu := incLocal_ts (E := E) (G.fst e)
    have hv := incLocal_ts (E := E) (G.snd e)
    cases h₁ : σ (G.fst e) <;> cases h₂ : σ (G.snd e) <;>
      simp [incTorusRel, incChartEq, Fin.sum_univ_two, incCoord, incLocalVal,
        incFreeCoeff, incFlip, h₁, h₂] <;> grind

noncomputable def incTorusToLocal : G.IncTorusRing →ₐ[ℂ] IncLocalRing V E :=
  Ideal.Quotient.liftₐ _ (aeval (G.incLocalVal σ)) <| by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨i, rfl⟩; exact (G.incLocalVal_rel σ) i
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]

@[simp] theorem incTorusToLocal_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    (G.incTorusToLocal σ) (Ideal.Quotient.mk _ p) = aeval (G.incLocalVal σ) p := rfl

theorem incTorusToLocal_chart :
    (G.incTorusToLocal σ).comp (G.incChartMap σ) =
      (Algebra.algHom ℂ (IncFreeRing V E) (IncLocalRing V E)).comp (G.incChartEquiv σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with v | ⟨e, α, β⟩
  · cases h : σ v <;>
      simp [incChartMap_mk, incChartVal, incLocalVal, incChartFlipVar, incFreeVal, h] <;> rfl
  · simp [incChartMap_mk, incChartVal, incLocalVal, incChartFlipVar, incFreeVal]; rfl

/-- Natural map from the free polynomial ring to the torus. -/
noncomputable def incFreeToTorus : IncFreeRing V E →ₐ[ℂ] G.IncTorusRing :=
  (G.incChartMap σ).comp (G.incChartEquiv σ).symm.toAlgHom

@[simp] theorem incFreeToTorus_vertex (v : V) :
    (G.incFreeToTorus σ) (X (Sum.inl v)) = (if σ v then Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))
      else Ideal.Quotient.mk _ (X (Sum.inl v))) := by
  simp [incFreeToTorus, incChartMap_mk, incChartVal]

theorem incFreeToTorus_unit : IsUnit ((G.incFreeToTorus σ) (incFreeDen (V := V) (E := E))) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨∏ v, if σ v then Ideal.Quotient.mk _ (X (Sum.inl v))
      else Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))), ?_⟩
  simp only [incFreeDen, map_prod, incFreeToTorus_vertex, ← Finset.prod_mul_distrib]
  trans ∏ _v : V, (1 : G.IncTorusRing)
  · apply Finset.prod_congr rfl
    intro v _
    cases h : σ v
    · simpa only [h, Bool.false_eq_true, ↓reduceIte] using G.incTorus_ts v
    · simpa only [h, ↓reduceIte] using (mul_comm _ _).trans (G.incTorus_ts v)
  · exact Finset.prod_const_one

noncomputable def incLocalToTorus : IncLocalRing V E →ₐ[ℂ] G.IncTorusRing :=
  IsLocalization.Away.liftAlgHom _ (G.incFreeToTorus_unit σ)

@[simp] theorem incLocalToTorus_algebraMap (p : IncFreeRing V E) :
    (G.incLocalToTorus σ) (algebraMap _ _ p) = (G.incFreeToTorus σ) p :=
  IsLocalization.Away.lift_eq _ (G.incFreeToTorus_unit σ) _

@[simp] theorem incLocalToTorus_inv (v : V) :
    (G.incLocalToTorus σ) (incLocalInv v) =
      (if σ v then Ideal.Quotient.mk _ (X (Sum.inl v))
        else Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))) := by
  have h := congrArg ((G.incLocalToTorus σ)) (incLocal_ts (E := E) v)
  simp only [map_mul, map_one, incLocalToTorus_algebraMap, incFreeToTorus_vertex] at h
  cases hσ : σ v
  · simp only [hσ, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact (isUnit_iff_exists_inv.mpr ⟨_, G.incTorus_ts v⟩).mul_left_cancel
      (h.trans (G.incTorus_ts v).symm)
  · simp only [hσ, ↓reduceIte] at h ⊢
    have ht := (mul_comm _ _).trans (G.incTorus_ts v)
    exact (isUnit_iff_exists_inv.mpr ⟨_, ht⟩).mul_left_cancel (h.trans ht.symm)

theorem incLocalToTorus_freeCoeff (e : E) (α β : Fin 2) :
    (G.incFreeToTorus σ) (G.incFreeCoeff e (incFlip (σ (G.fst e)) α) (incFlip (σ (G.snd e)) β)) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (e, α, β)))) := by
  have h := (G.incChartEquiv σ).symm_apply_apply
    (Ideal.Quotient.mk _ (X (Sum.inr (e, α, β))))
  have h' := congrArg (G.incChartMap σ) h
  simpa [incFreeToTorus, incFreeVal, incChartMap_mk, incChartVal, incChartFlipVar] using h'

theorem incLocalToTorus_comp :
    (G.incLocalToTorus σ).comp (G.incTorusToLocal σ) = AlgHom.id ℂ G.IncTorusRing := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  rcases i with v | v | ⟨e, α, β⟩
  · cases h : σ v <;> simp [incLocalVal, h]
  · cases h : σ v <;> simp [incLocalVal, h]
  · simp [incLocalVal, incLocalToTorus_freeCoeff]

theorem incTorusToLocal_comp :
    (G.incTorusToLocal σ).comp (G.incLocalToTorus σ) = AlgHom.id ℂ (IncLocalRing V E) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (incFreeDen (V := V) (E := E)))
  apply AlgHom.ext
  intro p
  change (G.incTorusToLocal σ) ((G.incLocalToTorus σ) (algebraMap _ _ p)) = algebraMap _ _ p
  rw [incLocalToTorus_algebraMap]
  change ((G.incTorusToLocal σ).comp (G.incChartMap σ)) ((G.incChartEquiv σ).symm.toAlgHom p) = _
  rw [incTorusToLocal_chart]
  change algebraMap _ _ ((G.incChartEquiv σ) ((G.incChartEquiv σ).symm p)) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The common torus is the polynomial ring in n+3m variables with all vertex coordinates inverted. -/
noncomputable def incTorusEquiv : G.IncTorusRing ≃ₐ[ℂ] IncLocalRing V E :=
  AlgEquiv.ofAlgHom (G.incTorusToLocal σ) (G.incLocalToTorus σ)
    (G.incTorusToLocal_comp σ) (G.incLocalToTorus_comp σ)

@[simp] theorem incTorusToLocal_chart_apply (x : G.IncChartRing σ) :
    G.incTorusToLocal σ (G.incChartMap σ x) =
      algebraMap (IncFreeRing V E) (IncLocalRing V E) (G.incChartEquiv σ x) :=
  AlgHom.congr_fun (G.incTorusToLocal_chart σ) x

/-- Every chart restriction to the common torus is injective. -/
theorem incChartMap_injective : Function.Injective (G.incChartMap σ) := by
  intro x y h
  apply (G.incChartEquiv σ).injective
  apply IsLocalization.injective (IncLocalRing V E)
    (powers_le_nonZeroDivisors_of_noZeroDivisors incFreeDen_ne_zero)
  simpa only [incTorusToLocal_chart_apply] using congrArg (G.incTorusToLocal σ) h

instance incTorus_isDomain : IsDomain G.IncTorusRing :=
  (G.incTorusEquiv (fun _ => false)).injective.isDomain
    (G.incTorusEquiv (fun _ => false)).toRingHom

/-- **Domain property in `alg:normal-cm`.** 𝒰_G, as a torus subring, is a domain. -/
theorem incidenceRing_isDomain : IsDomain G.IncidenceRing := inferInstance

end BPFixedPoints.Multigraph
