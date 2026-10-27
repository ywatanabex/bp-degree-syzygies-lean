import BPFixedPoints.Incidence.IncidenceKernelBundleTransitions

/-! # Local trivializations of `Z_G` as a rank-`3m` bundle with linear transitions

This file is the overlap part of the paper's Lemma `alg:incidence-vector-bundle`
(supplement section `supp:vector-bundle`): the incidence zero scheme `Z_G` is the total
space of the rank-`3m` kernel bundle of the evaluation `O^{4m} → F_G`, with local
trivializations whose transition functions are linear in the fibre coordinates.

* **Kernel total space over any base.** For a commutative ring `R`, a chart `σ` and a point
  `t : V → R`, `IncKernelRing σ t = R[c]/(Σ_{α,β} c_{e,α,β} X_{fst e,α}(t) X_{snd e,β}(t))` is
  the coordinate ring of the total space of the kernel of the evaluation map at `t`, and
  `incKernelRingTriv` identifies it with the polynomial ring in the `3m` kernel coordinates.
* **Trivializations over faces.** On a face `r` refined by chart `σ`, the coordinate ring
  `IncFaceRing r` of `Z_G` is the kernel ring of chart `σ` at the restricted point
  (`incFaceIdeal_eq_kernelIdeal`), so `incFaceKernelTriv hσ` trivializes `Z_G` over the face in
  the chart-`σ` kernel coordinates, linearly over `FaceRing ℂ r`.
* **Compatibility with the chart trivializations.** Restricting the existing chart
  trivialization `incidenceProjectiveZeroChartTrivialization σ` to `r` gives
  `incFaceKernelTriv hσ` (`incFaceKernelTriv_chart`); restriction to a smaller face is compatible
  as well (`incFaceKernelTriv_refinement`).
* **Linear transitions.** On a face refined by charts `σ` and `τ`,
  `Φ_τ ∘ Φ_σ⁻¹ = incLinearSubst g_{στ}`, the algebra map `X_j ↦ Σ_i g_{στ}(e_i)_j X_i` induced by
  the kernel transition of `IncidenceKernelBundleTransitions.lean`
  (`incFaceKernelTriv_transition`); on points, the kernel coordinates change by the linear
  extension of `g_{τσ}` (`incFaceKernelTriv_point`). In terms of the chart trivializations
  themselves: `incidenceProjectiveZeroChartTrivialization_overlap`. Here
  `R[X_{E × Fin 3}] = Sym((R^{3m})^∨)`, and `incLinearSubst g` is `Sym` of the dual map `g^∨`
  (`aeval_incLinearSubst`, `incLinearSubst_comp`).

Not constructed here: a relative spectrum over the scheme `X_G`, the kernel as a locally free
sheaf of modules on `X_G`, or the gluing of the evaluation map as a morphism of sheaves. All
statements are about the affine chart and face rings and the ring maps between them.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section KernelRing

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

variable {R : Type*} [CommRing R]

/-! ### Linearity of the kernel extension -/

/-- The kernel extension `R^{3m} → R^{4m}` as a linear map: the inverse of the kernel coordinates
followed by the inclusion of the kernel. -/
noncomputable def incChartKernelExtendLinear (σ : V → Bool) (t : V → R) :
    (G.IncChartFiberIdx σ → R) →ₗ[R] (IncCoeffIdx E → R) :=
  (LinearMap.ker (G.incChartEvaluation σ t)).subtype ∘ₗ
    (G.incChartEvaluationKernelEquiv σ t).symm.toLinearMap

/-- The underlying function of the linear kernel extension. -/
theorem incChartKernelExtendLinear_apply (σ : V → Bool) (t : V → R)
    (y : G.IncChartFiberIdx σ → R) :
    G.incChartKernelExtendLinear σ t y = G.incChartKernelExtend σ t y :=
  rfl

/-- At a non-unit coefficient the kernel extension is the given coordinate. -/
theorem incChartKernelExtend_of_ne (σ : V → Bool) (t : V → R) (y : G.IncChartFiberIdx σ → R)
    {c : IncCoeffIdx E} (hc : c.2 ≠ G.incChartUnitIdx σ c.1) :
    G.incChartKernelExtend σ t y c = y ⟨c, hc⟩ := by
  simp [incChartKernelExtend, hc]

/-- At the non-unit coefficient numbered `j`, the kernel extension is the `j`-th coordinate. -/
theorem incChartKernelExtend_freeIdxEquiv (σ : V → Bool) (t : V → R)
    (y : G.IncChartFiberIdx σ → R) (j : E × Fin 3) :
    G.incChartKernelExtend σ t y (G.incChartFreeIdxEquiv σ j).1 = y (G.incChartFreeIdxEquiv σ j) :=
  G.incChartKernelExtend_of_ne σ t y (G.incChartFreeIdxEquiv σ j).2

/-- Over a polynomial ring, the kernel extension of the generic coordinate vector is the linear
form whose coefficients are the kernel extensions of the basis vectors. -/
theorem incChartKernelExtend_generic (σ : V → Bool) (t : V → R) (c : IncCoeffIdx E) :
    G.incChartKernelExtend σ (fun v => C (t v))
        (fun k => (X ((G.incChartFreeIdxEquiv σ).symm k) : MvPolynomial (E × Fin 3) R)) c =
      ∑ i, C (G.incChartKernelExtend σ t
        (fun k => (Pi.single i (1 : R) : E × Fin 3 → R) ((G.incChartFreeIdxEquiv σ).symm k)) c) *
          X i := by
  have hy : (fun k => (X ((G.incChartFreeIdxEquiv σ).symm k) : MvPolynomial (E × Fin 3) R)) =
      ∑ i, (X i : MvPolynomial (E × Fin 3) R) • fun k =>
        C ((Pi.single i (1 : R) : E × Fin 3 → R) ((G.incChartFreeIdxEquiv σ).symm k)) := by
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← incChartKernelExtendLinear_apply, hy, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm, incChartKernelExtendLinear_apply]
  congr 1
  rw [G.map_incChartKernelExtend (C : R →+* MvPolynomial (E × Fin 3) R)]

/-! ### The total space of the kernel over a base ring -/

/-- The kernel equation of edge `e` over a base ring `R` at a point `t` of chart `σ`:
`Σ_{α,β} c_{e,α,β} X_{fst e,α}(t) X_{snd e,β}(t)`, the `e`-th component of the evaluation map
applied to the universal coefficient vector. -/
noncomputable def incKernelEquation (σ : V → Bool) (t : V → R) (e : E) :
    MvPolynomial (IncCoeffIdx E) R :=
  ∑ ab : Fin 2 × Fin 2, X (e, ab) * C (G.incChartMonomial σ t e ab)

/-- The kernel equations are the evaluation map applied to the universal coefficient vector. -/
theorem incKernelEquation_eq_evaluation (σ : V → Bool) (t : V → R) (e : E) :
    G.incKernelEquation σ t e =
      G.incChartEvaluation σ (fun v => C (t v)) (fun c => X c) e := by
  simp [incKernelEquation, incChartEvaluation_apply, map_incChartMonomial]

/-- The ideal of the kernel equations. -/
noncomputable def incKernelIdeal (σ : V → Bool) (t : V → R) :
    Ideal (MvPolynomial (IncCoeffIdx E) R) :=
  Ideal.span (Set.range (G.incKernelEquation σ t))

/-- The coordinate ring `R[c]/(evaluation)` of the total space of the kernel of the evaluation map
over `Spec R`, at the point `t` of chart `σ`. -/
abbrev IncKernelRing (σ : V → Bool) (t : V → R) :=
  MvPolynomial (IncCoeffIdx E) R ⧸ G.incKernelIdeal σ t

/-- Images of the coefficient variables in the fibre polynomial ring: the kernel extension of the
generic vector of free coordinates. -/
noncomputable def incKernelRingVal (σ : V → Bool) (t : V → R) :
    IncCoeffIdx E → MvPolynomial (E × Fin 3) R :=
  G.incChartKernelExtend σ (fun v => C (t v)) fun k => X ((G.incChartFreeIdxEquiv σ).symm k)

/-- The kernel extension of the generic coordinates satisfies the kernel equations. -/
theorem aeval_incKernelEquation (σ : V → Bool) (t : V → R) (e : E) :
    aeval (G.incKernelRingVal σ t) (G.incKernelEquation σ t e) = 0 := by
  have h := congrFun (LinearMap.mem_ker.mp (G.incChartKernelExtend_mem σ (fun v => C (t v))
    fun k => X ((G.incChartFreeIdxEquiv σ).symm k))) e
  rw [incChartEvaluation_apply] at h
  simpa [incKernelEquation, incKernelRingVal, map_incChartMonomial] using h

/-- The map from the kernel ring to the fibre polynomial ring. -/
noncomputable def incKernelRingToPoly (σ : V → Bool) (t : V → R) :
    G.IncKernelRing σ t →ₐ[R] MvPolynomial (E × Fin 3) R :=
  Ideal.Quotient.liftₐ _ (aeval (G.incKernelRingVal σ t)) (by
    intro p hp
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hp
    · rintro _ ⟨e, rfl⟩
      exact G.aeval_incKernelEquation σ t e
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])

/-- `incKernelRingToPoly` on representatives. -/
@[simp] theorem incKernelRingToPoly_mk (σ : V → Bool) (t : V → R)
    (p : MvPolynomial (IncCoeffIdx E) R) :
    G.incKernelRingToPoly σ t (Ideal.Quotient.mk _ p) = aeval (G.incKernelRingVal σ t) p :=
  rfl

/-- The map from the fibre polynomial ring to the kernel ring: the free coordinates are the
non-unit coefficients. -/
noncomputable def incPolyToKernelRing (σ : V → Bool) (t : V → R) :
    MvPolynomial (E × Fin 3) R →ₐ[R] G.IncKernelRing σ t :=
  (Ideal.Quotient.mkₐ R _).comp (rename fun j => (G.incChartFreeIdxEquiv σ j).1)

/-- `incPolyToKernelRing` renames the free coordinates to the non-unit coefficients. -/
theorem incPolyToKernelRing_apply (σ : V → Bool) (t : V → R) (p : MvPolynomial (E × Fin 3) R) :
    G.incPolyToKernelRing σ t p =
      Ideal.Quotient.mk _ (rename (fun j => (G.incChartFreeIdxEquiv σ j).1) p) :=
  rfl

/-- In the kernel ring, each unit coefficient is minus the evaluation of the three non-unit
coefficients of its edge. -/
theorem incKernelRing_mk_unit (σ : V → Bool) (t : V → R) (e : E) :
    (Ideal.Quotient.mk (G.incKernelIdeal σ t) (X (e, G.incChartUnitIdx σ e)) :
        G.IncKernelRing σ t) =
      Ideal.Quotient.mk (G.incKernelIdeal σ t)
        (-∑ ab : {ab : Fin 2 × Fin 2 // ab ≠ G.incChartUnitIdx σ e},
          X (e, ab.1) * C (G.incChartMonomial σ t e ab.1)) := by
  rw [Ideal.Quotient.eq, sub_neg_eq_add]
  have h : G.incKernelEquation σ t e = X (e, G.incChartUnitIdx σ e) +
      ∑ ab : {ab : Fin 2 × Fin 2 // ab ≠ G.incChartUnitIdx σ e},
        X (e, ab.1) * C (G.incChartMonomial σ t e ab.1) := by
    rw [incKernelEquation, Fintype.sum_eq_add_sum_subtype_ne _ (G.incChartUnitIdx σ e),
      incChartMonomial_unitIdx, map_one, mul_one]
  rw [← h]
  exact Ideal.subset_span ⟨e, rfl⟩

/-- One composite of the two maps is the identity of the polynomial ring. -/
theorem incKernelRingToPoly_comp (σ : V → Bool) (t : V → R) :
    (G.incKernelRingToPoly σ t).comp (G.incPolyToKernelRing σ t) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, incPolyToKernelRing_apply, rename_X, incKernelRingToPoly_mk, aeval_X,
    incKernelRingVal, incChartKernelExtend_freeIdxEquiv, Equiv.symm_apply_apply, AlgHom.id_apply]

/-- The other composite is the identity of the kernel ring. -/
theorem incPolyToKernelRing_comp (σ : V → Bool) (t : V → R) :
    (G.incPolyToKernelRing σ t).comp (G.incKernelRingToPoly σ t) = AlgHom.id R _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨e, ab⟩
  rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, incKernelRingToPoly_mk,
    aeval_X, AlgHom.comp_apply, AlgHom.id_apply, Ideal.Quotient.mkₐ_eq_mk,
    incPolyToKernelRing_apply, incKernelRingVal]
  by_cases h : ab = G.incChartUnitIdx σ e
  · subst h
    rw [incKernelRing_mk_unit]
    congr 1
    simp only [incChartKernelExtend, ↓reduceDIte, map_neg, map_sum, map_mul, rename_X,
      Equiv.apply_symm_apply]
    congr 1
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [← G.map_incChartMonomial (C : R →+* MvPolynomial (E × Fin 3) R), rename_C]
  · rw [G.incChartKernelExtend_of_ne σ _ _ (c := (e, ab)) h, rename_X, Equiv.apply_symm_apply]

/-- **Trivialization of the kernel total space over any base.** The coordinate ring of the total
space of the kernel of the chart-`σ` evaluation map at a point `t` is a polynomial ring in the `3m`
free coordinates over `R`. -/
noncomputable def incKernelRingTriv (σ : V → Bool) (t : V → R) :
    G.IncKernelRing σ t ≃ₐ[R] MvPolynomial (E × Fin 3) R :=
  AlgEquiv.ofAlgHom (G.incKernelRingToPoly σ t) (G.incPolyToKernelRing σ t)
    (G.incKernelRingToPoly_comp σ t) (G.incPolyToKernelRing_comp σ t)

/-- The trivialization sends each coefficient variable to its kernel-extension formula. -/
@[simp] theorem incKernelRingTriv_mk_X (σ : V → Bool) (t : V → R) (c : IncCoeffIdx E) :
    G.incKernelRingTriv σ t (Ideal.Quotient.mk _ (X c)) = G.incKernelRingVal σ t c := by
  change aeval _ (X c) = _
  rw [aeval_X]

/-- The free coordinates of the trivialization are the non-unit coefficients of chart `σ`. -/
@[simp] theorem incKernelRingTriv_symm_X (σ : V → Bool) (t : V → R) (j : E × Fin 3) :
    (G.incKernelRingTriv σ t).symm (X j) =
      Ideal.Quotient.mk _ (X (j.1, G.incChartFreeIdx σ j.1 j.2)) := by
  change G.incPolyToKernelRing σ t (X j) = _
  rw [incPolyToKernelRing_apply, rename_X]
  rfl

/-- The non-unit coefficient numbered `j` goes to the free coordinate `X_j`. -/
theorem incKernelRingVal_freeIdx (σ : V → Bool) (t : V → R) (j : E × Fin 3) :
    G.incKernelRingVal σ t (j.1, G.incChartFreeIdx σ j.1 j.2) = X j := by
  change G.incKernelRingVal σ t (G.incChartFreeIdxEquiv σ j).1 = X j
  rw [incKernelRingVal, incChartKernelExtend_freeIdxEquiv, Equiv.symm_apply_apply]

end KernelRing

/-! ### Linear substitutions of a polynomial ring -/

section LinearSubst

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- The algebra endomorphism of the polynomial ring `R[X_ι]` induced by a linear endomorphism `g`
of `R^ι`: the coordinate function `X_j` goes to `X_j ∘ g = Σ_i g(e_i)_j X_i`. Viewing
`R[X_ι] = Sym((R^ι)^∨)`, this is `Sym` of the dual map `g^∨`. -/
noncomputable def incLinearSubst (g : (ι → R) →ₗ[R] (ι → R)) :
    MvPolynomial ι R →ₐ[R] MvPolynomial ι R :=
  aeval fun j => ∑ i, C (g (Pi.single i 1) j) * X i

/-- The linear substitution on a variable. -/
@[simp] theorem incLinearSubst_X (g : (ι → R) →ₗ[R] (ι → R)) (j : ι) :
    incLinearSubst g (X j) = ∑ i, C (g (Pi.single i 1) j) * X i :=
  aeval_X _ _

/-- At an `R`-point `x`, the linear substitution by `g` is evaluation at `g x`: it is the pullback
of functions along `g`. -/
theorem aeval_incLinearSubst (g : (ι → R) →ₗ[R] (ι → R)) (x : ι → R)
    (p : MvPolynomial ι R) : aeval x (incLinearSubst g p) = aeval (g x) p := by
  have h : (aeval x).comp (incLinearSubst g) = aeval (g x) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, incLinearSubst_X, aeval_X, map_sum,
      linearMap_apply_eq_sum_single g x j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply, mul_comm]
  exact AlgHom.congr_fun h p

/-- The identity of `R^ι` induces the identity substitution. -/
theorem incLinearSubst_id :
    incLinearSubst (LinearMap.id : (ι → R) →ₗ[R] (ι → R)) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [incLinearSubst_X, AlgHom.id_apply]
  simp [Pi.single_apply]

/-- Linear substitution is contravariant: `Sym((g ∘ h)^∨) = Sym(h^∨) ∘ Sym(g^∨)`. -/
theorem incLinearSubst_comp (g h : (ι → R) →ₗ[R] (ι → R)) :
    incLinearSubst (g ∘ₗ h) = (incLinearSubst h).comp (incLinearSubst g) := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [AlgHom.comp_apply, incLinearSubst_X, incLinearSubst_X, map_sum]
  simp only [map_mul, incLinearSubst_X, LinearMap.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [linearMap_apply_eq_sum_single g (h (Pi.single i 1)) j, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [algHom_C, MvPolynomial.algebraMap_eq, map_mul]
  ring

end LinearSubst

/-! ### Trivializations of `Z_G` over overlap faces -/

section Faces

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

variable {σ τ ρ : V → Bool} {r : V → Fin 3}

/-- The universal edge equation of a face is the kernel equation at the face's own coordinates. -/
theorem incFaceEquation_eq_kernelEquation (r : V → Fin 3) (e : E) :
    G.incFaceEquation r e = G.incKernelEquation (faceOrientation r) (faceVariable ℂ r) e := by
  rw [incFaceEquation, incKernelEquation, Fintype.sum_prod_type]
  simp only [incChartMonomial, map_mul, faceOrientation, mul_assoc]

/-- On a face refined by chart `σ`, the chart-`σ` kernel equation of `e` is the edge transition
unit times the face's edge equation. -/
theorem incKernelEquation_overlap (hσ : FaceRefines (chartFace σ) r) (e : E) :
    G.incKernelEquation σ (incOverlapPoint hσ) e =
      C (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) * G.incFaceEquation r e := by
  rw [incFaceEquation_eq_kernelEquation, incKernelEquation, incKernelEquation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [incChartMonomial_overlapPoint, map_mul]
  ring

/-- On a face refined by chart `σ`, the ideal of `Z_G` is the ideal of the kernel equations of
chart `σ`. -/
theorem incFaceIdeal_eq_kernelIdeal (hσ : FaceRefines (chartFace σ) r) :
    G.incFaceIdeal r = G.incKernelIdeal σ (incOverlapPoint hσ) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, rfl⟩
    have h := (G.incKernelIdeal σ (incOverlapPoint hσ)).mul_mem_left
      (C (↑(G.incOverlapEdgeUnit hσ e)⁻¹ : FaceRing ℂ r)) (Ideal.subset_span ⟨e, rfl⟩)
    rwa [incKernelEquation_overlap, ← mul_assoc, ← map_mul, Units.inv_mul, map_one,
      one_mul] at h
  · apply Ideal.span_le.mpr
    rintro _ ⟨e, rfl⟩
    rw [incKernelEquation_overlap]
    exact (G.incFaceIdeal r).mul_mem_left _ (Ideal.subset_span ⟨e, rfl⟩)

/-- **Trivialization of `Z_G` over a face, in chart-`σ` kernel coordinates.** Over every face `r`
refined by chart `σ` (in particular over every overlap of `σ` with other charts), the coordinate
ring of `Z_G` is the polynomial ring in the `3m` kernel coordinates of chart `σ`. -/
noncomputable def incFaceKernelTriv (hσ : FaceRefines (chartFace σ) r) :
    G.IncFaceRing r ≃ₐ[FaceRing ℂ r] MvPolynomial (E × Fin 3) (FaceRing ℂ r) :=
  (Ideal.quotientEquivAlgOfEq (FaceRing ℂ r) (G.incFaceIdeal_eq_kernelIdeal hσ)).trans
    (G.incKernelRingTriv σ (incOverlapPoint hσ))

/-- The face trivialization on a coefficient variable. -/
@[simp] theorem incFaceKernelTriv_mk_X (hσ : FaceRefines (chartFace σ) r) (c : IncCoeffIdx E) :
    G.incFaceKernelTriv hσ (Ideal.Quotient.mk _ (X c)) =
      G.incKernelRingVal σ (incOverlapPoint hσ) c := by
  rw [incFaceKernelTriv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    incKernelRingTriv_mk_X]

/-- The face trivialization is linear over the face ring. -/
@[simp] theorem incFaceKernelTriv_mk_C (hσ : FaceRefines (chartFace σ) r) (a : FaceRing ℂ r) :
    G.incFaceKernelTriv hσ (Ideal.Quotient.mk _ (C a)) = C a :=
  (G.incFaceKernelTriv hσ).commutes a

/-- The `3m` polynomial variables of the face trivialization are the non-unit coefficients of
chart `σ`, as in the chart trivialization of `Z_G`. -/
@[simp] theorem incFaceKernelTriv_symm_X (hσ : FaceRefines (chartFace σ) r) (j : E × Fin 3) :
    (G.incFaceKernelTriv hσ).symm (X j) =
      Ideal.Quotient.mk _ (X (j.1, G.incChartFreeIdx σ j.1 j.2)) := by
  rw [incFaceKernelTriv, AlgEquiv.symm_trans_apply, incKernelRingTriv_symm_X]
  rfl

/-- The transition of the face trivializations sends a chart-`σ` fibre coordinate to the linear
form given by the kernel transition `g_{στ}`. -/
theorem incFaceKernelTriv_transition_X (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (j : E × Fin 3) :
    G.incFaceKernelTriv hτ ((G.incFaceKernelTriv hσ).symm (X j)) =
      ∑ i, C (G.incKernelTransition hτ hσ (Pi.single i 1) j) * X i := by
  rw [incFaceKernelTriv_symm_X, incFaceKernelTriv_mk_X, incKernelRingVal,
    incChartKernelExtend_generic]
  rfl

/-- **Linear transition functions.** On a face `r` refined by charts `σ` and `τ`, the transition
`Φ_τ ∘ Φ_σ⁻¹` between the two trivializations of `Z_G` is the linear substitution induced by the
kernel transition `g_{στ} = g_{τσ}⁻¹`: functions pull back along the `R`-linear map of fibres. -/
theorem incFaceKernelTriv_transition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    ((G.incFaceKernelTriv hσ).symm.trans (G.incFaceKernelTriv hτ)).toAlgHom =
      incLinearSubst (G.incKernelTransition hτ hσ).toLinearMap := by
  apply MvPolynomial.algHom_ext
  intro j
  rw [incLinearSubst_X]
  exact G.incFaceKernelTriv_transition_X hσ hτ j

/-- **Kernel coordinates of points transform linearly.** For an algebra `A` over the face ring and
an `A`-point `φ` of `Z_G` over the face, its chart-`τ` kernel coordinates are obtained from its
chart-`σ` kernel coordinates by the `A`-linear extension of `g_{τσ}`. -/
theorem incFaceKernelTriv_point (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) {A : Type*} [CommRing A] [Algebra (FaceRing ℂ r) A]
    (φ : G.IncFaceRing r →ₐ[FaceRing ℂ r] A) (j : E × Fin 3) :
    φ ((G.incFaceKernelTriv hτ).symm (X j)) =
      ∑ i, algebraMap (FaceRing ℂ r) A (G.incKernelTransition hσ hτ (Pi.single i 1) j) *
        φ ((G.incFaceKernelTriv hσ).symm (X i)) := by
  have h : (G.incFaceKernelTriv hτ).symm (X j) = (G.incFaceKernelTriv hσ).symm
      (G.incFaceKernelTriv hσ ((G.incFaceKernelTriv hτ).symm (X j))) :=
    ((G.incFaceKernelTriv hσ).symm_apply_apply _).symm
  rw [h, incFaceKernelTriv_transition_X]
  change (φ.comp (G.incFaceKernelTriv hσ).symm.toAlgHom) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
  rfl

/-! ### Compatibility with the chart trivializations and with restriction -/

/-- The chart coordinate ring `ℂ[t_V]` of chart `σ` restricted to a face `r` refined by it. -/
noncomputable def incOverlapBase (hσ : FaceRefines (chartFace σ) r) :
    MvPolynomial V ℂ →ₐ[ℂ] FaceRing ℂ r :=
  (faceRefinementMap ℂ hσ).comp (chartFaceRingEquiv σ).symm.toAlgHom

/-- The base restriction sends `t_v` to the restricted chart coordinate. -/
@[simp] theorem incOverlapBase_X (hσ : FaceRefines (chartFace σ) r) (v : V) :
    incOverlapBase hσ (X v) = incOverlapPoint hσ v := by
  have h : (chartFaceRingEquiv (R := ℂ) σ).symm (X v) = faceVariable ℂ (chartFace σ) v := by
    rw [AlgEquiv.symm_apply_eq, chartFaceRingEquiv_variable]
  change faceRefinementMap ℂ hσ ((chartFaceRingEquiv (R := ℂ) σ).symm (X v)) = _
  rw [h]
  rfl

/-- Restriction of the chart ring of `Z_G` on chart `σ` (the ring of
`incidenceProjectiveZeroChartTrivialization`) to a face `r` refined by chart `σ`. -/
noncomputable def incZeroChartRestrict (hσ : FaceRefines (chartFace σ) r) :
    G.IncidenceProjectiveZeroChartRing σ →ₐ[ℂ] G.IncFaceRing r :=
  (G.incFaceRefinement hσ).comp (G.incidenceProjectiveZeroChartEquiv σ).toAlgHom

/-- The restriction of `Z_G` on representatives. -/
theorem incZeroChartRestrict_mk (hσ : FaceRefines (chartFace σ) r)
    (p : MvPolynomial V (IncCoeffRing E)) :
    G.incZeroChartRestrict hσ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (facePolynomialRefinement ℂ (IncCoeffIdx E) hσ
        (G.incidenceChartAmbientPolynomialEquiv σ p)) :=
  rfl

/-- The inverse chart trivialization of `Z_G` is the base map on base coefficients. -/
theorem incidenceProjectiveZeroChartTrivialization_symm_C (σ : V → Bool) (p : MvPolynomial V ℂ) :
    (G.incidenceProjectiveZeroChartTrivialization σ).symm (C p) =
      G.incidenceProjectiveZeroChartBase σ p := by
  rw [AlgEquiv.symm_apply_eq]
  exact (AlgHom.congr_fun (G.incidenceProjectiveZeroChartTrivialization_base σ) p).symm

/-- The face trivialization on a restricted base coefficient. -/
theorem incFaceKernelTriv_mk_facePolynomialRefinement_C (hσ : FaceRefines (chartFace σ) r)
    {q : V → Fin 3} (h : FaceRefines q r) (a : FaceRing ℂ q) :
    G.incFaceKernelTriv hσ
        (Ideal.Quotient.mk _ (facePolynomialRefinement ℂ (IncCoeffIdx E) h (C a))) =
      C (faceRefinementMap ℂ h a) := by
  rw [facePolynomialRefinement, MvPolynomial.mapAlgHom_apply, map_C]
  exact G.incFaceKernelTriv_mk_C hσ _

/-- The face trivialization on a restricted coefficient variable. -/
theorem incFaceKernelTriv_mk_facePolynomialRefinement_X (hσ : FaceRefines (chartFace σ) r)
    {q : V → Fin 3} (h : FaceRefines q r) (c : IncCoeffIdx E) :
    G.incFaceKernelTriv hσ
        (Ideal.Quotient.mk _ (facePolynomialRefinement ℂ (IncCoeffIdx E) h (X c))) =
      G.incKernelRingVal σ (incOverlapPoint hσ) c := by
  rw [facePolynomialRefinement, MvPolynomial.mapAlgHom_apply, map_X]
  exact G.incFaceKernelTriv_mk_X hσ c

/-- **Compatibility with the chart trivializations.** Restricting the chart trivialization
`incidenceProjectiveZeroChartTrivialization σ` of `Z_G` to a face `r` refined by chart `σ` gives the
face trivialization `incFaceKernelTriv`: the square formed by the restriction of `Z_G`, the two
trivializations and the restriction of base coefficients `ℂ[t_V] → R` commutes. -/
theorem incFaceKernelTriv_chart (hσ : FaceRefines (chartFace σ) r) :
    ((G.incFaceKernelTriv hσ).toAlgHom.restrictScalars ℂ).comp (G.incZeroChartRestrict hσ) =
      (MvPolynomial.mapAlgHom (incOverlapBase hσ)).comp
        (G.incidenceProjectiveZeroChartTrivialization σ).toAlgHom := by
  have key : ∀ f g : G.IncidenceProjectiveZeroChartRing σ →ₐ[ℂ]
      MvPolynomial (E × Fin 3) (FaceRing ℂ r),
      f.comp (G.incidenceProjectiveZeroChartTrivialization σ).symm.toAlgHom =
        g.comp (G.incidenceProjectiveZeroChartTrivialization σ).symm.toAlgHom → f = g := by
    intro f g h
    refine AlgHom.ext fun x => ?_
    have hx := AlgHom.congr_fun h (G.incidenceProjectiveZeroChartTrivialization σ x)
    simpa using hx
  apply key
  apply MvPolynomial.algHom_ext'
  · apply MvPolynomial.algHom_ext
    intro v
    change G.incFaceKernelTriv hσ (G.incZeroChartRestrict hσ
        ((G.incidenceProjectiveZeroChartTrivialization σ).symm (C (X v)))) =
      MvPolynomial.map (incOverlapBase hσ) ((G.incidenceProjectiveZeroChartTrivialization σ)
        ((G.incidenceProjectiveZeroChartTrivialization σ).symm (C (X v))))
    rw [AlgEquiv.apply_symm_apply, map_C, RingHom.coe_coe, incOverlapBase_X,
      incidenceProjectiveZeroChartTrivialization_symm_C, incidenceProjectiveZeroChartBase, aeval_X,
      incZeroChartRestrict_mk, incidenceChartAmbientPolynomialEquiv_X,
      incFaceKernelTriv_mk_facePolynomialRefinement_C]
    rfl
  · intro j
    change G.incFaceKernelTriv hσ (G.incZeroChartRestrict hσ
        ((G.incidenceProjectiveZeroChartTrivialization σ).symm (X j))) =
      MvPolynomial.map (incOverlapBase hσ) ((G.incidenceProjectiveZeroChartTrivialization σ)
        ((G.incidenceProjectiveZeroChartTrivialization σ).symm (X j)))
    rw [AlgEquiv.apply_symm_apply, map_X, incidenceProjectiveZeroChartTrivialization_symm_X,
      incZeroChartRestrict_mk, incidenceChartAmbientPolynomialEquiv_C_X,
      incFaceKernelTriv_mk_facePolynomialRefinement_X, incKernelRingVal_freeIdx]

/-- **Compatibility with restriction to smaller faces.** For a face `s` refining `r`, restricting
the chart-`σ` trivialization over `r` gives the chart-`σ` trivialization over `s`. -/
theorem incFaceKernelTriv_refinement (hσ : FaceRefines (chartFace σ) r) {s : V → Fin 3}
    (hrs : FaceRefines r s) :
    ((G.incFaceKernelTriv (faceRefines_trans hσ hrs)).toAlgHom.restrictScalars ℂ).comp
        (G.incFaceRefinement hrs) =
      (MvPolynomial.mapAlgHom (faceRefinementMap ℂ hrs)).comp
        ((G.incFaceKernelTriv hσ).toAlgHom.restrictScalars ℂ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · refine AlgHom.ext fun a => ?_
    change G.incFaceKernelTriv (faceRefines_trans hσ hrs) (G.incFaceRefinement hrs
        (Ideal.Quotient.mk _ (C a))) =
      MvPolynomial.map (faceRefinementMap ℂ hrs)
        (G.incFaceKernelTriv hσ (Ideal.Quotient.mk _ (C a)))
    rw [incFaceRefinement_mk, incFaceKernelTriv_mk_facePolynomialRefinement_C,
      incFaceKernelTriv_mk_C, map_C]
    rfl
  · intro c
    change G.incFaceKernelTriv (faceRefines_trans hσ hrs) (G.incFaceRefinement hrs
        (Ideal.Quotient.mk _ (X c))) =
      MvPolynomial.map (faceRefinementMap ℂ hrs)
        (G.incFaceKernelTriv hσ (Ideal.Quotient.mk _ (X c)))
    rw [incFaceRefinement_mk, incFaceKernelTriv_mk_facePolynomialRefinement_X,
      incFaceKernelTriv_mk_X, incKernelRingVal, incKernelRingVal,
      G.map_incChartKernelExtend
        (MvPolynomial.map (faceRefinementMap ℂ hrs : FaceRing ℂ r →+* FaceRing ℂ s))]
    congr 1
    · funext v
      rw [map_C, RingHom.coe_coe, faceRefinementMap_incOverlapPoint]
    · funext k
      rw [map_X]

/-- **The chart trivializations of `Z_G` have linear transition functions.** Let `r` be a face
refined by charts `σ` and `τ` (for instance their overlap). If functions `x` on the chart-`σ` part
and `x'` on the chart-`τ` part of `Z_G` agree on the face `r`, then their images under the chart
trivializations `incidenceProjectiveZeroChartTrivialization`, with base coefficients restricted to
`R = FaceRing ℂ r`, differ by the linear substitution induced by the kernel transition `g_{στ}`. -/
theorem incidenceProjectiveZeroChartTrivialization_overlap (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (x : G.IncidenceProjectiveZeroChartRing σ)
    (x' : G.IncidenceProjectiveZeroChartRing τ)
    (h : G.incZeroChartRestrict hσ x = G.incZeroChartRestrict hτ x') :
    MvPolynomial.map (incOverlapBase hτ) (G.incidenceProjectiveZeroChartTrivialization τ x') =
      incLinearSubst (G.incKernelTransition hτ hσ).toLinearMap
        (MvPolynomial.map (incOverlapBase hσ)
          (G.incidenceProjectiveZeroChartTrivialization σ x)) := by
  have hσx : G.incFaceKernelTriv hσ (G.incZeroChartRestrict hσ x) =
      MvPolynomial.map (incOverlapBase hσ) (G.incidenceProjectiveZeroChartTrivialization σ x) :=
    AlgHom.congr_fun (G.incFaceKernelTriv_chart hσ) x
  have hτx : G.incFaceKernelTriv hτ (G.incZeroChartRestrict hτ x') =
      MvPolynomial.map (incOverlapBase hτ) (G.incidenceProjectiveZeroChartTrivialization τ x') :=
    AlgHom.congr_fun (G.incFaceKernelTriv_chart hτ) x'
  have ht := AlgHom.congr_fun (G.incFaceKernelTriv_transition hσ hτ)
    (G.incFaceKernelTriv hσ (G.incZeroChartRestrict hσ x))
  rewrite [← hτx, ← hσx]
  refine Eq.trans ?_ ht
  rewrite [AlgEquiv.coe_toAlgHom, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, h]
  rfl

end Faces

end BPFixedPoints.Multigraph
