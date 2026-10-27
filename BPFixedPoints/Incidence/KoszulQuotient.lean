import BPFixedPoints.Incidence.KoszulBilinear

/-! # Identify each face's degree-zero Koszul quotient with its three-free-coefficient presentation -/

namespace BPFixedPoints.Koszul

open MvPolynomial

variable {E R : Type*} [LinearOrder E] [Fintype E] [CommRing R]

set_option linter.unusedSectionVars false

/-- Coefficient values after eliminating c₀₀. -/
noncomputable def bilinearFreeCoeff (x y : E → R) (e : E) (α β : Fin 2) :
    MvPolynomial (E × Fin 3) R :=
  if α = 0 then if β = 0 then -bilinearTail x y e else X (e, 0)
  else if β = 0 then X (e, 1) else X (e, 2)

noncomputable def zeroBilinearIdeal (x y : E → R) :
    Ideal (MvPolynomial (E × Fin 2 × Fin 2) R) :=
  Ideal.span (Set.range (bilinearEquation x y))

@[simp] theorem zeroBilinear_mk_C (x y : E → R) (r : R) :
    Ideal.Quotient.mk (zeroBilinearIdeal x y) (C r) =
      algebraMap R (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) r :=
  (Ideal.Quotient.mkₐ R (zeroBilinearIdeal x y)).commutes r

theorem bilinearFreeCoeff_equation (x y : E → R) (e : E) :
    aeval (fun (j, α, β) => bilinearFreeCoeff x y j α β) (bilinearEquation x y e) = 0 := by
  simp [bilinearEquation, bilinearFreeCoeff, bilinearTail]
  ring

noncomputable def zeroBilinearToFree (x y : E → R) :
    (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) →ₐ[R]
      MvPolynomial (E × Fin 3) R :=
  Ideal.Quotient.liftₐ _ (aeval fun (e, α, β) => bilinearFreeCoeff x y e α β) <| by
    intro p hp
    have hle : zeroBilinearIdeal x y ≤ RingHom.ker
        (aeval (R := R) fun (e, α, β) => bilinearFreeCoeff x y e α β).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨e, rfl⟩
      exact bilinearFreeCoeff_equation x y e
    exact hle hp

@[simp] theorem zeroBilinearToFree_mk (x y : E → R)
    (p : MvPolynomial (E × Fin 2 × Fin 2) R) :
    zeroBilinearToFree x y (Ideal.Quotient.mk _ p) =
      aeval (fun (e, α, β) => bilinearFreeCoeff x y e α β) p := rfl

noncomputable def zeroBilinearFromFree (x y : E → R) :
    MvPolynomial (E × Fin 3) R →ₐ[R]
      (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) :=
  aeval fun (e, k) => Ideal.Quotient.mk _
    (X (e, if k = 0 then 0 else 1, if k = 1 then 0 else 1))

theorem zeroBilinearToFree_comp (x y : E → R) :
    (zeroBilinearToFree x y).comp (zeroBilinearFromFree x y) =
      AlgHom.id R (MvPolynomial (E × Fin 3) R) := by
  apply MvPolynomial.algHom_ext
  rintro ⟨e, k⟩
  fin_cases k <;> simp [zeroBilinearFromFree, bilinearFreeCoeff]

theorem zeroBilinearFromFree_comp (x y : E → R) :
    (zeroBilinearFromFree x y).comp (zeroBilinearToFree x y) =
      AlgHom.id R (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨e, α, β⟩
  have he : Ideal.Quotient.mk (zeroBilinearIdeal x y) (bilinearEquation x y e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨e, rfl⟩)
  simp only [bilinearEquation, map_add, map_mul, zeroBilinear_mk_C] at he
  fin_cases α <;> fin_cases β <;>
    simp [zeroBilinearFromFree, bilinearFreeCoeff, bilinearTail]
  linear_combination -he

/-- Actual quotient-ring isomorphism eliminating every edge's constant coefficient. -/
noncomputable def zeroBilinearFreeEquiv (x y : E → R) :
    (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) ≃ₐ[R]
      MvPolynomial (E × Fin 3) R :=
  AlgEquiv.ofAlgHom (zeroBilinearToFree x y) (zeroBilinearFromFree x y)
    (zeroBilinearToFree_comp x y) (zeroBilinearFromFree_comp x y)

theorem bilinearIdeal_eq_map (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R) :
    bilinearIdeal τ₁ τ₂ x y =
      (zeroBilinearIdeal x y).map (rename (coeffFlip τ₁ τ₂)).toRingHom := by
  rw [zeroBilinearIdeal, Ideal.map_span, ← Set.range_comp]
  rfl

noncomputable def zeroBilinearToFlip (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R) :
    (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ zeroBilinearIdeal x y) ≃ₐ[R]
      (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ bilinearIdeal τ₁ τ₂ x y) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv R (coeffFlip τ₁ τ₂))
    (bilinearIdeal_eq_map τ₁ τ₂ x y)

/-- Each face's Koszul degree-zero quotient is a polynomial ring in 3m variables over its vertex-coordinate ring. -/
noncomputable def bilinearFreeEquiv (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R) :
    (MvPolynomial (E × Fin 2 × Fin 2) R ⧸ bilinearIdeal τ₁ τ₂ x y) ≃ₐ[R]
      MvPolynomial (E × Fin 3) R :=
  (zeroBilinearToFlip τ₁ τ₂ x y).symm.trans (zeroBilinearFreeEquiv x y)

theorem bilinearFreeEquiv_mk (τ₁ τ₂ : E → Fin 2 ≃ Fin 2) (x y : E → R)
    (p : MvPolynomial (E × Fin 2 × Fin 2) R) :
    bilinearFreeEquiv τ₁ τ₂ x y (Ideal.Quotient.mk _ p) =
      aeval (fun (e, α, β) => bilinearFreeCoeff x y e α β)
        (rename (coeffFlip τ₁ τ₂).symm p) := rfl

end BPFixedPoints.Koszul
