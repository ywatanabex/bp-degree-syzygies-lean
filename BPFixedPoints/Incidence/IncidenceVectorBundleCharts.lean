import BPFixedPoints.Incidence.PolynomialRegularSequence
import BPFixedPoints.Incidence.Chart
import BPFixedPoints.Incidence.IncidenceProjectiveZeroCharts

/-! # The incidence scheme as a vector bundle, chart by chart

This file formalizes the chart-level algebra of the paper's proof that the
incidence scheme `Z_G` is the total space of a rank-`3m` vector bundle on
`X_G = (P¹)^V` (supplement section `supp:vector-bundle`, Lemma
`alg:incidence-vector-bundle`).

Fix a standard chart `σ : V → Bool` of `X_G`, with one affine coordinate `t_v`
per vertex. On this chart the edge bundle `L_e` is trivialized and the
universal edge equation is `b_e^σ = Σ_{α,β} c_{e,α,β} X_{fst e,α} X_{snd e,β}`,
where each chart monomial is a monomial in `t_{fst e}, t_{snd e}`. Exactly one
chart monomial of each edge, at `G.incChartUnitIdx σ e`, is the constant `1`.

* `incChartEvaluation` is the evaluation map `B_G ⊗ O → F_G` on the chart, at
  an arbitrary `R`-valued point `t` of the chart. It has an explicit section
  (`incChartEvaluation_comp_section`), so it is surjective
  (`incChartEvaluation_surjective`: global generation chart by chart), and
  its kernel is free of rank `3m` on the non-unit coefficients
  (`incChartEvaluationKernelEquiv`, `incChartEvaluationKernelEquivFree`,
  `incChartEvaluation_ker_free`, `incChartEvaluation_ker_finrank`).
* `incChartCoordinateChange` is an automorphism of the chart polynomial ring
  `ℂ[t, c]`, fixing all vertex coordinates and all non-unit coefficients, that
  sends the unit coefficient `c_{e,u_e}` to the edge equation `b_e^σ`. Hence the
  edge equations, in any order, form a regular sequence
  (`incChartEq_isRegular`), and the same holds for the paper's original
  equations in `MvPolynomial V S_G` (`incidenceProjectiveEquation_isRegular`);
  the full sequences generate the chart ideals (`incChartEqList_ofList`,
  `incidenceProjectiveEquationList_ofList`).
* The chart quotient is a polynomial ring in the `3m` non-unit coefficients over
  the chart coordinate ring `ℂ[t_V]` (`incChartTrivialization`,
  `incidenceProjectiveZeroChartTrivialization`, with base compatibility
  `incChartTrivialization_base`, `incidenceProjectiveZeroChartTrivialization_base`).
  The latter is about the same ring `IncidenceProjectiveZeroChartRing σ` as
  `Paper.alg_incidence_projective_zero_charts`.
* `incChartPointEquiv` identifies the `A`-points of the chart quotient with pairs
  `(t, c)` where `c` lies in the kernel of the evaluation map at `t`: on charts,
  `Z_G` is the total space of that kernel. Its kernel coordinates are the
  polynomial variables of the trivialization (`incChartPointEquiv_kernelCoordinates`).

Not constructed here: the kernel as a locally free sheaf on the scheme `X_G`,
the gluing of these chart trivializations (transition maps), and the relative
spectrum of its dual symmetric algebra; nor the sheaf-level surjectivity of
`B_G ⊗ O_{X_G} → F_G`. Only the algebra on each standard chart is formalized.
The regular-sequence statements are in the chart polynomial rings, not in local
rings of the scheme `X_G × B_G`.
-/

namespace BPFixedPoints

namespace ResolutionTools

open RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false

/-- Distinct variables, in any order, form a regular sequence in a polynomial ring over a
nontrivial commutative ring. -/
theorem isRegular_mvPolynomial_X_of_nodup {R : Type} [CommRing R] [Nontrivial R]
    {σ : Type} (l : List σ) (hl : l.Nodup) :
    IsRegular (MvPolynomial σ R) (l.map (MvPolynomial.X (R := R))) := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, l.length = n := ⟨_, rfl⟩
  induction n generalizing σ l with
  | zero =>
    rw [List.length_eq_zero_iff.mp hn]
    exact IsRegular.nil _ _
  | succ n ih =>
    obtain _ | ⟨i, l⟩ := l
    · simp at hn
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hne : ∀ j ∈ l, j ≠ i := fun j hj hji => hi (hji ▸ hj)
    let l' : List {j // j ≠ i} := l.pmap Subtype.mk hne
    have hl' : l'.Nodup := List.Nodup.pmap (fun _ _ _ _ h => congrArg Subtype.val h) hl
    have hlen : l'.length = n := by simpa [l'] using hn
    let φ : Polynomial (MvPolynomial {j // j ≠ i} R) ≃+* MvPolynomial σ R :=
      ((MvPolynomial.optionEquivLeft R _).symm.trans
        (MvPolynomial.renameEquiv R (Equiv.optionSubtypeNe i))).toRingEquiv
    have h := isRegular_map_ringEquiv φ _ (isRegular_polynomial_X_cons _ (ih l' hl' hlen))
    convert h using 1
    simp only [List.map_cons, List.map_map, List.cons.injEq]
    constructor
    · simp [φ]
    · simp [l', List.map_pmap, φ]

end ResolutionTools

namespace Multigraph

open MvPolynomial RingTheory.Sequence
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Charts

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-! ### The unit coefficient of each edge on a chart -/

/-- On chart `σ`, the coefficient index `(α, β)` of edge `e` whose chart monomial
`X_{fst e,α} X_{snd e,β}` is the constant `1`. -/
def incChartUnitIdx (σ : V → Bool) (e : E) : Fin 2 × Fin 2 :=
  (incFlip (σ (G.fst e)) 0, incFlip (σ (G.snd e)) 0)

theorem incCoord_incFlip_zero {R : Type*} [CommRing R] (b : Bool) (t : R) :
    incCoord b (incFlip b 0) t = 1 := by
  cases b <;> simp [incCoord, incFlip]

/-- The three non-unit coefficient indices of edge `e` on chart `σ`, numbered as the
free variables of `IncFreeRing`. -/
def incChartFreeIdx (σ : V → Bool) (e : E) (k : Fin 3) : Fin 2 × Fin 2 :=
  (incFlip (σ (G.fst e)) (if k = 0 then 0 else 1), incFlip (σ (G.snd e)) (if k = 1 then 0 else 1))

theorem incChartFreeIdx_ne_unitIdx (σ : V → Bool) (e : E) (k : Fin 3) :
    G.incChartFreeIdx σ e k ≠ G.incChartUnitIdx σ e := by
  intro h
  simp only [incChartFreeIdx, incChartUnitIdx, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  have h₁' := congrArg (incFlip (σ (G.fst e))) h₁
  have h₂' := congrArg (incFlip (σ (G.snd e))) h₂
  simp only [incFlip_involutive] at h₁' h₂'
  fin_cases k <;> simp_all

/-! ### The chart-wise evaluation map `B_G ⊗ O → F_G` -/

section Evaluation

variable {R : Type*} [CommRing R]

/-- The chart monomial `X_{fst e,α} X_{snd e,β}` of the coefficient `c_{e,α,β}`, evaluated at
an `R`-valued point `t` of the standard chart `σ` of `X_G`. -/
def incChartMonomial (σ : V → Bool) (t : V → R) (e : E) (ab : Fin 2 × Fin 2) : R :=
  incCoord (σ (G.fst e)) ab.1 (t (G.fst e)) * incCoord (σ (G.snd e)) ab.2 (t (G.snd e))

/-- On every chart, the monomial of the unit coefficient is the constant `1`. -/
@[simp] theorem incChartMonomial_unitIdx (σ : V → Bool) (t : V → R) (e : E) :
    G.incChartMonomial σ t e (G.incChartUnitIdx σ e) = 1 := by
  simp [incChartMonomial, incChartUnitIdx, incCoord_incFlip_zero]

/-- The evaluation map `B_G ⊗ O_{X_G} → F_G` on chart `σ` at the point `t`:
`c ↦ (Σ_{α,β} c_{e,α,β} X_{fst e,α}(t) X_{snd e,β}(t))_e`. -/
def incChartEvaluation (σ : V → Bool) (t : V → R) : (IncCoeffIdx E → R) →ₗ[R] (E → R) where
  toFun c e := ∑ ab : Fin 2 × Fin 2, c (e, ab) * G.incChartMonomial σ t e ab
  map_add' c d := by
    funext e
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext e
    simp [Finset.mul_sum, mul_assoc]

theorem incChartEvaluation_apply (σ : V → Bool) (t : V → R) (c : IncCoeffIdx E → R) (e : E) :
    G.incChartEvaluation σ t c e = ∑ ab : Fin 2 × Fin 2, c (e, ab) * G.incChartMonomial σ t e ab :=
  rfl

/-- The universal chart edge equation is the evaluation map applied to the universal coefficient
vector at the universal chart point. -/
theorem incChartEq_eq_evaluation (σ : V → Bool) (e : E) :
    G.incChartEq σ e = G.incChartEvaluation σ (fun v => X (Sum.inl v))
      (fun c => X (Sum.inr c)) e := by
  rw [incChartEvaluation_apply, incChartEq, ← Finset.univ_product_univ, Finset.sum_product]
  simp only [incChartMonomial, mul_assoc]

/-- The splitting of the chart evaluation map: put `y_e` on the unit coefficient of `e`. -/
def incChartEvaluationSection (σ : V → Bool) : (E → R) →ₗ[R] (IncCoeffIdx E → R) where
  toFun y c := if c.2 = G.incChartUnitIdx σ c.1 then y c.1 else 0
  map_add' y z := by
    funext c
    split_ifs <;> simp [*]
  map_smul' r y := by
    funext c
    split_ifs <;> simp [*]

/-- The evaluation map is split by `incChartEvaluationSection`. -/
theorem incChartEvaluation_comp_section (σ : V → Bool) (t : V → R) :
    (G.incChartEvaluation σ t).comp (G.incChartEvaluationSection σ) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  funext e
  simp [incChartEvaluation_apply, incChartEvaluationSection, ite_mul, Finset.sum_ite_eq']

/-- **Global generation on charts.** The chart-wise evaluation map `B_G ⊗ O → F_G` is
surjective at every `R`-valued point of every standard chart. -/
theorem incChartEvaluation_surjective (σ : V → Bool) (t : V → R) :
    Function.Surjective (G.incChartEvaluation σ t) := fun y =>
  ⟨G.incChartEvaluationSection σ y, LinearMap.congr_fun (G.incChartEvaluation_comp_section σ t) y⟩

/-- The `3m` coefficient indices other than the unit ones on chart `σ`. -/
abbrev IncChartFiberIdx (σ : V → Bool) := {c : IncCoeffIdx E // c.2 ≠ G.incChartUnitIdx σ c.1}

/-- A coefficient vector lies in the kernel iff each unit coefficient is minus the evaluation
of the remaining three coefficients of its edge. -/
theorem incChartEvaluation_eq_zero_iff (σ : V → Bool) (t : V → R) (c : IncCoeffIdx E → R) :
    G.incChartEvaluation σ t c = 0 ↔ ∀ e, c (e, G.incChartUnitIdx σ e) =
      -∑ ab : {ab : Fin 2 × Fin 2 // ab ≠ G.incChartUnitIdx σ e},
        c (e, ab.1) * G.incChartMonomial σ t e ab.1 := by
  rw [funext_iff]
  refine forall_congr' fun e => ?_
  rw [incChartEvaluation_apply, Fintype.sum_eq_add_sum_subtype_ne _ (G.incChartUnitIdx σ e),
    incChartMonomial_unitIdx, mul_one, Pi.zero_apply, eq_neg_iff_add_eq_zero]

/-- Extend a vector of non-unit coefficients to the unique kernel vector with these entries. -/
def incChartKernelExtend (σ : V → Bool) (t : V → R) (y : G.IncChartFiberIdx σ → R) :
    IncCoeffIdx E → R := fun c =>
  if h : c.2 = G.incChartUnitIdx σ c.1 then
    -∑ ab : {ab : Fin 2 × Fin 2 // ab ≠ G.incChartUnitIdx σ c.1},
      y ⟨(c.1, ab.1), ab.2⟩ * G.incChartMonomial σ t c.1 ab.1
  else y ⟨c, h⟩

theorem incChartKernelExtend_mem (σ : V → Bool) (t : V → R) (y : G.IncChartFiberIdx σ → R) :
    G.incChartKernelExtend σ t y ∈ LinearMap.ker (G.incChartEvaluation σ t) := by
  rw [LinearMap.mem_ker, incChartEvaluation_eq_zero_iff]
  intro e
  simp only [incChartKernelExtend, ↓reduceDIte]
  congr 1
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp [ab.2]

/-- **Local freeness of the kernel.** On each chart and at each point, the kernel of the
evaluation map is the free module on the `3m` non-unit coefficients. -/
def incChartEvaluationKernelEquiv (σ : V → Bool) (t : V → R) :
    LinearMap.ker (G.incChartEvaluation σ t) ≃ₗ[R] (G.IncChartFiberIdx σ → R) where
  toFun k c := k.1 c.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun y := ⟨G.incChartKernelExtend σ t y, G.incChartKernelExtend_mem σ t y⟩
  left_inv k := by
    obtain ⟨k, hk⟩ := k
    apply Subtype.ext
    funext ⟨e, ab⟩
    have hk' := (G.incChartEvaluation_eq_zero_iff σ t k).mp (LinearMap.mem_ker.mp hk) e
    simp only [incChartKernelExtend]
    split_ifs with h
    · subst h
      exact hk'.symm
    · rfl
  right_inv y := by
    funext ⟨c, hc⟩
    simp [incChartKernelExtend, hc]

theorem incChartFiberIdx_card (σ : V → Bool) :
    Fintype.card (G.IncChartFiberIdx σ) = 3 * Fintype.card E := by
  have hunit : Fintype.card {c : IncCoeffIdx E // c.2 = G.incChartUnitIdx σ c.1} =
      Fintype.card E := by
    refine Fintype.card_congr
      { toFun := fun c => c.1.1
        invFun := fun e => ⟨(e, G.incChartUnitIdx σ e), rfl⟩
        left_inv := ?_
        right_inv := fun _ => rfl }
    rintro ⟨⟨e, ab⟩, h⟩
    simp only at h
    subst h
    rfl
  rw [Fintype.card_subtype_compl, hunit]
  simp only [IncCoeffIdx, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The numbering `E × Fin 3` of the non-unit coefficient indices used by `IncFreeRing` and by
the trivializations below. -/
noncomputable def incChartFreeIdxEquiv (σ : V → Bool) : E × Fin 3 ≃ G.IncChartFiberIdx σ :=
  Equiv.ofBijective
    (fun p => ⟨(p.1, G.incChartFreeIdx σ p.1 p.2), G.incChartFreeIdx_ne_unitIdx σ p.1 p.2⟩) (by
      rw [Fintype.bijective_iff_injective_and_card, incChartFiberIdx_card, Fintype.card_prod,
        Fintype.card_fin, mul_comm]
      refine ⟨?_, rfl⟩
      rintro ⟨e, k⟩ ⟨e', k'⟩ h
      simp only [Subtype.mk.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [incChartFreeIdx, Prod.mk.injEq] at h
      have h₁ := (incFlip _).injective h.1
      have h₂ := (incFlip _).injective h.2
      fin_cases k <;> fin_cases k' <;> simp_all)

@[simp] theorem incChartFreeIdxEquiv_apply (σ : V → Bool) (e : E) (k : Fin 3) :
    (G.incChartFreeIdxEquiv σ (e, k)).1 = (e, G.incChartFreeIdx σ e k) :=
  rfl

/-- The kernel of the evaluation map is free on the `3m` coordinates `E × Fin 3`, numbered as the
polynomial variables of the trivializations below. -/
noncomputable def incChartEvaluationKernelEquivFree (σ : V → Bool) (t : V → R) :
    LinearMap.ker (G.incChartEvaluation σ t) ≃ₗ[R] (E × Fin 3 → R) :=
  (G.incChartEvaluationKernelEquiv σ t).trans
    (LinearEquiv.funCongrLeft R R (G.incChartFreeIdxEquiv σ))

theorem incChartEvaluationKernelEquivFree_apply (σ : V → Bool) (t : V → R)
    (k : LinearMap.ker (G.incChartEvaluation σ t)) (e : E) (i : Fin 3) :
    G.incChartEvaluationKernelEquivFree σ t k (e, i) = k.1 (e, G.incChartFreeIdx σ e i) :=
  rfl

/-- The kernel of the chart-wise evaluation map is a free module. -/
theorem incChartEvaluation_ker_free (σ : V → Bool) (t : V → R) :
    Module.Free R (LinearMap.ker (G.incChartEvaluation σ t)) :=
  Module.Free.of_equiv (G.incChartEvaluationKernelEquiv σ t).symm

/-- **Rank `3m`.** Over a nontrivial ring, the kernel of the chart-wise evaluation map has rank
`3m = 4m - m`. -/
theorem incChartEvaluation_ker_finrank [Nontrivial R] (σ : V → Bool) (t : V → R) :
    Module.finrank R (LinearMap.ker (G.incChartEvaluation σ t)) = 3 * Fintype.card E := by
  rw [(G.incChartEvaluationKernelEquiv σ t).finrank_eq, Module.finrank_fintype_fun_eq_card,
    incChartFiberIdx_card]

end Evaluation

/-! ### The edge equations as linear coordinates in the coefficient directions -/

/-- The non-constant part of the zero-chart edge equation. -/
noncomputable def incZeroChartTail (e : E) : MvPolynomial (IncChartVar V E) ℂ :=
  X (Sum.inr (e, 0, 1)) * X (Sum.inl (G.snd e)) + X (Sum.inr (e, 1, 0)) * X (Sum.inl (G.fst e)) +
    X (Sum.inr (e, 1, 1)) * X (Sum.inl (G.fst e)) * X (Sum.inl (G.snd e))

theorem incChartEq_zero_eq_add_tail (e : E) :
    G.incChartEq (fun _ => false) e = X (Sum.inr (e, 0, 0)) + G.incZeroChartTail e := by
  simp [incChartEq, incZeroChartTail, Fin.sum_univ_two, incCoord]
  ring

/-- Images of the chart variables under the shear `c_{e,0,0} ↦ c_{e,0,0} + s·tail_e`. -/
noncomputable def incZeroChartShearVal (s : ℂ) :
    IncChartVar V E → MvPolynomial (IncChartVar V E) ℂ
  | Sum.inl v => X (Sum.inl v)
  | Sum.inr c => if c.2 = (0, 0) then X (Sum.inr c) + C s * G.incZeroChartTail c.1
      else X (Sum.inr c)

/-- The shear `c_{e,0,0} ↦ c_{e,0,0} + s·tail_e` of the chart polynomial ring. -/
noncomputable def incZeroChartShear (s : ℂ) :
    MvPolynomial (IncChartVar V E) ℂ →ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  aeval (G.incZeroChartShearVal s)

theorem incZeroChartShear_X_inl (s : ℂ) (v : V) :
    G.incZeroChartShear s (X (Sum.inl v)) = X (Sum.inl v) := by
  simp [incZeroChartShear, incZeroChartShearVal]

theorem incZeroChartShear_X_unit (s : ℂ) (e : E) :
    G.incZeroChartShear s (X (Sum.inr (e, 0, 0))) =
      X (Sum.inr (e, 0, 0)) + C s * G.incZeroChartTail e := by
  simp [incZeroChartShear, incZeroChartShearVal]

theorem incZeroChartShear_X_of_ne (s : ℂ) (e : E) {ab : Fin 2 × Fin 2} (h : ab ≠ (0, 0)) :
    G.incZeroChartShear s (X (Sum.inr (e, ab))) = X (Sum.inr (e, ab)) := by
  simp [incZeroChartShear, incZeroChartShearVal, h]

theorem incZeroChartShear_tail (s : ℂ) (e : E) :
    G.incZeroChartShear s (G.incZeroChartTail e) = G.incZeroChartTail e := by
  simp only [incZeroChartTail, map_add, map_mul, incZeroChartShear_X_inl]
  rw [G.incZeroChartShear_X_of_ne s e (ab := (0, 1)) (by decide),
    G.incZeroChartShear_X_of_ne s e (ab := (1, 0)) (by decide),
    G.incZeroChartShear_X_of_ne s e (ab := (1, 1)) (by decide)]

theorem incZeroChartShear_comp (s : ℂ) :
    (G.incZeroChartShear (-s)).comp (G.incZeroChartShear s) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  rintro (v | ⟨e, ab⟩)
  · simp [incZeroChartShear_X_inl]
  · by_cases h : ab = (0, 0)
    · subst h
      simp only [AlgHom.comp_apply, AlgHom.id_apply, incZeroChartShear_X_unit, map_add, map_mul,
        incZeroChartShear_tail]
      rw [show G.incZeroChartShear (-s) (C s) = C s from
        (G.incZeroChartShear (-s)).commutes s]
      simp only [map_neg]
      ring
    · simp [incZeroChartShear_X_of_ne _ _ _ h]

/-- The shear as an automorphism of the chart polynomial ring. -/
noncomputable def incZeroChartShearEquiv :
    MvPolynomial (IncChartVar V E) ℂ ≃ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  AlgEquiv.ofAlgHom (G.incZeroChartShear 1) (G.incZeroChartShear (-1))
    (by simpa using G.incZeroChartShear_comp (-1)) (G.incZeroChartShear_comp 1)

theorem incZeroChartShearEquiv_X_unit (e : E) :
    G.incZeroChartShearEquiv (X (Sum.inr (e, 0, 0))) = G.incChartEq (fun _ => false) e := by
  change G.incZeroChartShear 1 _ = _
  rw [incZeroChartShear_X_unit, incChartEq_zero_eq_add_tail, map_one, one_mul]

/-- The coefficient-index flip relating chart `σ` to the zero chart, as a permutation. -/
def incChartFlipPerm (σ : V → Bool) : Equiv.Perm (IncChartVar V E) :=
  Function.Involutive.toPerm _ (G.incChartFlipVar_involutive σ)

/-- **Edge equations as coordinates.** An automorphism of the chart polynomial ring `ℂ[t, c]`
that fixes every vertex coordinate and every non-unit coefficient and sends the unit coefficient
`c_{e,u_e}` of each edge to the chart edge equation `b_e^σ`. -/
noncomputable def incChartCoordinateChange (σ : V → Bool) :
    MvPolynomial (IncChartVar V E) ℂ ≃ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ :=
  (renameEquiv ℂ (G.incChartFlipPerm σ)).trans
    (G.incZeroChartShearEquiv.trans (renameEquiv ℂ (G.incChartFlipPerm σ)))

theorem incChartCoordinateChange_apply (σ : V → Bool) (p : MvPolynomial (IncChartVar V E) ℂ) :
    G.incChartCoordinateChange σ p =
      rename (G.incChartFlipVar σ) (G.incZeroChartShearEquiv (rename (G.incChartFlipVar σ) p)) :=
  rfl

theorem incChartCoordinateChange_unit (σ : V → Bool) (e : E) :
    G.incChartCoordinateChange σ (X (Sum.inr (e, G.incChartUnitIdx σ e))) = G.incChartEq σ e := by
  rw [incChartCoordinateChange_apply, rename_X]
  have hflip : G.incChartFlipVar σ (Sum.inr (e, G.incChartUnitIdx σ e)) = Sum.inr (e, 0, 0) := by
    simp [incChartFlipVar, incChartUnitIdx]
  rw [hflip, incZeroChartShearEquiv_X_unit, incChartFlip_zero_eq]

theorem incChartCoordinateChange_vertex (σ : V → Bool) (v : V) :
    G.incChartCoordinateChange σ (X (Sum.inl v)) = X (Sum.inl v) := by
  rw [incChartCoordinateChange_apply, rename_X]
  change rename _ (G.incZeroChartShear 1 (X (Sum.inl v))) = _
  rw [incZeroChartShear_X_inl, rename_X]
  rfl

theorem incChartCoordinateChange_coeff_of_ne (σ : V → Bool) (e : E) {ab : Fin 2 × Fin 2}
    (h : ab ≠ G.incChartUnitIdx σ e) :
    G.incChartCoordinateChange σ (X (Sum.inr (e, ab))) = X (Sum.inr (e, ab)) := by
  rw [incChartCoordinateChange_apply, rename_X]
  have hne : (incFlip (σ (G.fst e)) ab.1, incFlip (σ (G.snd e)) ab.2) ≠
      ((0 : Fin 2), (0 : Fin 2)) := by
    intro h0
    apply h
    simp only [Prod.mk.injEq] at h0
    have h₁ := congrArg (incFlip (σ (G.fst e))) h0.1
    have h₂ := congrArg (incFlip (σ (G.snd e))) h0.2
    simp only [incFlip_involutive] at h₁ h₂
    exact Prod.ext h₁ h₂
  change rename _ (G.incZeroChartShear 1 (X (G.incChartFlipVar σ (Sum.inr (e, ab))))) = _
  rw [show G.incChartFlipVar σ (Sum.inr (e, ab)) =
      Sum.inr (e, incFlip (σ (G.fst e)) ab.1, incFlip (σ (G.snd e)) ab.2) from rfl,
    incZeroChartShear_X_of_ne _ _ _ hne, rename_X]
  simp [incChartFlipVar]

/-- The coordinate change is linear over the chart coordinate ring `ℂ[t_V]` of `X_G`. -/
theorem incChartCoordinateChange_comp_rename_inl (σ : V → Bool) :
    (G.incChartCoordinateChange σ).toAlgHom.comp (rename Sum.inl) =
      (rename Sum.inl : MvPolynomial V ℂ →ₐ[ℂ] MvPolynomial (IncChartVar V E) ℂ) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [incChartCoordinateChange_vertex]

/-- The chart edge equations, listed along any duplicate-free list of edges, are the images of
distinct variables under `incChartCoordinateChange`. -/
theorem incChartEq_list_eq_map (σ : V → Bool) (l : List E) :
    l.map (G.incChartEq σ) = ((l.map fun e => (Sum.inr (e, G.incChartUnitIdx σ e) :
      IncChartVar V E)).map (X (R := ℂ))).map (G.incChartCoordinateChange σ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro e _
  exact (G.incChartCoordinateChange_unit σ e).symm

/-- **Regular sequence on charts.** On every standard chart, the universal edge equations, in any
order, form a regular sequence in the chart polynomial ring `ℂ[t_V, c]` in the vertex
coordinates and all `4m` coefficients. -/
theorem incChartEq_isRegular (σ : V → Bool) (l : List E) (hl : l.Nodup) :
    IsRegular (MvPolynomial (IncChartVar V E) ℂ) (l.map (G.incChartEq σ)) := by
  rw [G.incChartEq_list_eq_map σ l]
  apply ResolutionTools.isRegular_map_ringEquiv (G.incChartCoordinateChange σ).toRingEquiv
  apply ResolutionTools.isRegular_mvPolynomial_X_of_nodup
  refine hl.map fun e₁ e₂ h => ?_
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  exact h.1

/-- The universal edge equations listed along all edges. -/
noncomputable def incChartEqList (σ : V → Bool) : List (MvPolynomial (IncChartVar V E) ℂ) :=
  (Finset.univ : Finset E).toList.map (G.incChartEq σ)

theorem incChartEqList_length (σ : V → Bool) :
    (G.incChartEqList σ).length = Fintype.card E := by
  simp [incChartEqList]

/-- All `m` universal edge equations form a regular sequence on every standard chart. -/
theorem incChartEqList_isRegular (σ : V → Bool) :
    IsRegular (MvPolynomial (IncChartVar V E) ℂ) (G.incChartEqList σ) :=
  G.incChartEq_isRegular σ _ (Finset.nodup_toList _)

/-- This regular sequence generates exactly the chart ideal of `Z_G`. -/
theorem incChartEqList_ofList (σ : V → Bool) :
    Ideal.ofList (G.incChartEqList σ) = Ideal.span (Set.range (G.incChartEq σ)) := by
  rw [Ideal.ofList]
  congr 1
  ext p
  simp [incChartEqList]

/-! ### The chart quotient as a polynomial ring over the chart coordinate ring -/

/-- The chart coordinate ring `ℂ[t_V]` of `X_G` in the chart ring of `Z_G`. -/
noncomputable def incChartBase (σ : V → Bool) : MvPolynomial V ℂ →ₐ[ℂ] G.IncChartRing σ :=
  aeval fun v => Ideal.Quotient.mk _ (X (Sum.inl v))

/-- **Local trivialization of the kernel bundle.** The chart ring `ℂ[t, c]/(b_e^σ)` of `Z_G` is a
polynomial ring in `3m` variables over the chart coordinate ring `ℂ[t_V]` of `X_G`. -/
noncomputable def incChartTrivialization (σ : V → Bool) :
    G.IncChartRing σ ≃ₐ[ℂ] MvPolynomial (E × Fin 3) (MvPolynomial V ℂ) :=
  (G.incChartEquiv σ).trans
    ((renameEquiv ℂ (Equiv.sumComm V (E × Fin 3))).trans (sumAlgEquiv ℂ (E × Fin 3) V))

theorem incChartTrivialization_vertex (σ : V → Bool) (v : V) :
    G.incChartTrivialization σ (Ideal.Quotient.mk _ (X (Sum.inl v))) = C (X v) := by
  simp [incChartTrivialization, incChartFlipVar, incFreeVal]

/-- The trivialization is an isomorphism over the chart coordinate ring `ℂ[t_V]`. -/
theorem incChartTrivialization_base (σ : V → Bool) :
    (G.incChartTrivialization σ).toAlgHom.comp (G.incChartBase σ) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial V ℂ)
        (MvPolynomial (E × Fin 3) (MvPolynomial V ℂ)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [incChartBase, incChartTrivialization_vertex, algebraMap_eq]

/-- The `3m` polynomial variables of the trivialization are the non-unit coefficients. -/
theorem incChartTrivialization_symm_X (σ : V → Bool) (e : E) (k : Fin 3) :
    (G.incChartTrivialization σ).symm (X (e, k)) =
      Ideal.Quotient.mk _ (X (Sum.inr (e, G.incChartFreeIdx σ e k))) := by
  apply (G.incChartTrivialization σ).injective
  rw [AlgEquiv.apply_symm_apply]
  simp only [incChartTrivialization, AlgEquiv.trans_apply, incChartEquiv_mk, rename_X]
  fin_cases k <;>
    simp [incChartFreeIdx, incChartFlipVar, incFreeVal, incFreeCoeff, incFlip_involutive]

/-- **`Z_G` is the total space of the kernel, on charts.** For every commutative `ℂ`-algebra `A`,
`A`-points of the chart of `Z_G` are pairs of an `A`-point `t` of the chart of `X_G` and a
coefficient vector in the kernel of the evaluation map at `t`. -/
noncomputable def incChartPointEquiv (σ : V → Bool) (A : Type*) [CommRing A] [Algebra ℂ A] :
    (G.IncChartRing σ →ₐ[ℂ] A) ≃
      {p : (V → A) × (IncCoeffIdx E → A) // p.2 ∈ LinearMap.ker (G.incChartEvaluation σ p.1)} where
  toFun φ := ⟨(fun v => φ (Ideal.Quotient.mk _ (X (Sum.inl v))),
      fun c => φ (Ideal.Quotient.mk _ (X (Sum.inr c)))), by
    rw [LinearMap.mem_ker]
    funext e
    have hmem : G.incChartEq σ e ∈ Ideal.span (Set.range (G.incChartEq σ)) :=
      Ideal.subset_span ⟨e, rfl⟩
    have h0 : φ (Ideal.Quotient.mk (Ideal.span (Set.range (G.incChartEq σ))) (G.incChartEq σ e)) =
        0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
    rw [incChartEq_eq_evaluation, incChartEvaluation_apply] at h0
    simpa [incChartEvaluation_apply, incChartMonomial, map_incCoord] using h0⟩
  invFun p := Ideal.Quotient.liftₐ _ (aeval (Sum.elim p.1.1 p.1.2)) (by
    intro q hq
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨e, rfl⟩
      have hk := congrFun (LinearMap.mem_ker.mp p.2) e
      rw [incChartEq_eq_evaluation, incChartEvaluation_apply]
      simpa [incChartEvaluation_apply, incChartMonomial, map_incCoord] using hk
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro a x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero])
  left_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro (v | c) <;> simp [Ideal.Quotient.liftₐ_apply]
  right_inv p := by
    obtain ⟨⟨t, c⟩, hp⟩ := p
    apply Subtype.ext
    apply Prod.ext <;> funext x <;> simp [Ideal.Quotient.liftₐ_apply]

/-- Under `incChartPointEquiv`, the base point of an `A`-point is its value on the chart
coordinate ring `ℂ[t_V]`. -/
theorem incChartPointEquiv_base (σ : V → Bool) (A : Type*) [CommRing A] [Algebra ℂ A]
    (φ : G.IncChartRing σ →ₐ[ℂ] A) (v : V) :
    (G.incChartPointEquiv σ A φ).1.1 v = φ (G.incChartBase σ (X v)) := by
  simp [incChartPointEquiv, incChartBase]

/-- Under `incChartPointEquiv`, the free kernel coordinates of an `A`-point are the values of the
`3m` polynomial variables of `incChartTrivialization`. -/
theorem incChartPointEquiv_kernelCoordinates (σ : V → Bool) (A : Type*) [CommRing A]
    [Algebra ℂ A] (φ : G.IncChartRing σ →ₐ[ℂ] A) (e : E) (k : Fin 3) :
    (G.incChartPointEquiv σ A φ).1.2 (e, G.incChartFreeIdx σ e k) =
      φ ((G.incChartTrivialization σ).symm (X (e, k))) := by
  rw [incChartTrivialization_symm_X]
  rfl

end Charts

/-! ### The paper's projective-chart objects -/

section ProjectiveCharts

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- **Regular sequence for the paper's chart equations.** The original dehomogenized edge
equations in `MvPolynomial V S_G`, in any order, form a regular sequence. -/
theorem incidenceProjectiveEquation_isRegular (σ : V → Bool) (l : List E) (hl : l.Nodup) :
    IsRegular (MvPolynomial V (IncCoeffRing E)) (l.map (G.incidenceProjectiveEquation σ)) := by
  have h := ResolutionTools.isRegular_map_ringEquiv
    (sumAlgEquiv ℂ V (IncCoeffIdx E)).toRingEquiv _ (G.incChartEq_isRegular σ l hl)
  convert h using 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro e _
  exact G.incidenceProjectiveEquation_original σ e

/-- All `m` original chart equations, listed along the edges. -/
noncomputable def incidenceProjectiveEquationList (σ : V → Bool) :
    List (MvPolynomial V (IncCoeffRing E)) :=
  (Finset.univ : Finset E).toList.map (G.incidenceProjectiveEquation σ)

/-- All `m` original chart equations form a regular sequence. -/
theorem incidenceProjectiveEquationList_isRegular (σ : V → Bool) :
    IsRegular (MvPolynomial V (IncCoeffRing E)) (G.incidenceProjectiveEquationList σ) :=
  G.incidenceProjectiveEquation_isRegular σ _ (Finset.nodup_toList _)

/-- This regular sequence generates the paper's chart ideal. -/
theorem incidenceProjectiveEquationList_ofList (σ : V → Bool) :
    Ideal.ofList (G.incidenceProjectiveEquationList σ) = G.incidenceProjectiveChartIdeal σ := by
  rw [Ideal.ofList, incidenceProjectiveChartIdeal]
  congr 1
  ext p
  simp [incidenceProjectiveEquationList]

theorem incidenceProjectiveChartIdeal_map_sumAlgEquiv_symm (σ : V → Bool) :
    Ideal.span (Set.range (G.incChartEq σ)) =
      (G.incidenceProjectiveChartIdeal σ).map (sumAlgEquiv ℂ V (IncCoeffIdx E)).symm := by
  rw [incidenceProjectiveChartIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  ext p
  simp [incidenceProjectiveEquation_original]

/-- The paper's chart ring of `Z_G` is the chart ring `ℂ[t, c]/(b_e^σ)`. -/
noncomputable def incidenceProjectiveZeroChartIncChartEquiv (σ : V → Bool) :
    G.IncidenceProjectiveZeroChartRing σ ≃ₐ[ℂ] G.IncChartRing σ :=
  Ideal.quotientEquivAlg _ _ (sumAlgEquiv ℂ V (IncCoeffIdx E)).symm
    (G.incidenceProjectiveChartIdeal_map_sumAlgEquiv_symm σ)

@[simp] theorem incidenceProjectiveZeroChartIncChartEquiv_mk (σ : V → Bool)
    (p : MvPolynomial V (IncCoeffRing E)) :
    G.incidenceProjectiveZeroChartIncChartEquiv σ (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ ((sumAlgEquiv ℂ V (IncCoeffIdx E)).symm p) :=
  rfl

/-- The chart coordinate ring `ℂ[t_V]` of `X_G` in the paper's chart ring of `Z_G`. -/
noncomputable def incidenceProjectiveZeroChartBase (σ : V → Bool) :
    MvPolynomial V ℂ →ₐ[ℂ] G.IncidenceProjectiveZeroChartRing σ :=
  aeval fun v => Ideal.Quotient.mk _ (X v : MvPolynomial V (IncCoeffRing E))

/-- **Local trivialization for the paper's chart.** The chart ring of `Z_G` appearing in
`Paper.alg_incidence_projective_zero_charts` is a polynomial ring in `3m` variables over the
chart coordinate ring `ℂ[t_V]` of `X_G`. -/
noncomputable def incidenceProjectiveZeroChartTrivialization (σ : V → Bool) :
    G.IncidenceProjectiveZeroChartRing σ ≃ₐ[ℂ] MvPolynomial (E × Fin 3) (MvPolynomial V ℂ) :=
  (G.incidenceProjectiveZeroChartIncChartEquiv σ).trans (G.incChartTrivialization σ)

/-- The trivialization of the paper's chart is an isomorphism over `ℂ[t_V]`. -/
theorem incidenceProjectiveZeroChartTrivialization_base (σ : V → Bool) :
    (G.incidenceProjectiveZeroChartTrivialization σ).toAlgHom.comp
        (G.incidenceProjectiveZeroChartBase σ) =
      IsScalarTower.toAlgHom ℂ (MvPolynomial V ℂ)
        (MvPolynomial (E × Fin 3) (MvPolynomial V ℂ)) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [incidenceProjectiveZeroChartTrivialization, incidenceProjectiveZeroChartBase,
    incChartTrivialization_vertex, algebraMap_eq]

/-- The `3m` polynomial variables of the paper-chart trivialization are the non-unit
coefficients `c_{e,α,β}` of `S_G`. -/
theorem incidenceProjectiveZeroChartTrivialization_symm_X (σ : V → Bool) (e : E) (k : Fin 3) :
    (G.incidenceProjectiveZeroChartTrivialization σ).symm (X (e, k)) =
      Ideal.Quotient.mk _
        (C (X (e, G.incChartFreeIdx σ e k)) : MvPolynomial V (IncCoeffRing E)) := by
  rw [AlgEquiv.symm_apply_eq, incidenceProjectiveZeroChartTrivialization, AlgEquiv.trans_apply,
    incidenceProjectiveZeroChartIncChartEquiv_mk, sumAlgEquiv_symm_C_X,
    ← incChartTrivialization_symm_X, AlgEquiv.apply_symm_apply]

end ProjectiveCharts

end Multigraph

end BPFixedPoints
