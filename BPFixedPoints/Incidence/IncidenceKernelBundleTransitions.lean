import BPFixedPoints.Incidence.IncidenceVectorBundleCharts
import BPFixedPoints.Incidence.IncidenceEquationTransitions
import BPFixedPoints.Incidence.IncidenceFaceRefinement
import BPFixedPoints.Incidence.CechLineBundleTransitions

/-! # Transitions of the incidence kernel bundle on chart overlaps

This file continues `IncidenceVectorBundleCharts.lean` (supplement section
`supp:vector-bundle`, Lemma `alg:incidence-vector-bundle`) from single charts to
overlaps. An overlap of standard charts is a Čech face `r : V → Fin 3`, with
coordinate ring `R = FaceRing ℂ r`; a chart `σ` contributes to `r` when
`FaceRefines (chartFace σ) r`; for the overlap `faceJoin (chartFace σ) (chartFace τ)` of two
charts these hypotheses are `faceRefines_join_left` and `faceRefines_join_right`. The affine
coordinates of `σ` restrict into `R` as `incOverlapPoint hσ`.

* **Edge-bundle transitions.** On `R`, the chart-`σ` evaluation map
  `E_σ : R^{4m} → R^m` is the face's own evaluation map `incFaceEvaluation r`
  followed by the invertible diagonal action `incEdgeScaling` of the edge units
  `incOverlapEdgeUnit hσ e = u_{fst e} u_{snd e}` (`incChartEvaluation_overlap`).
  Hence `E_τ = D_{τσ} ∘ E_σ` for two charts (`incChartEvaluation_overlap_transition`),
  and all chart evaluation maps have the same kernel `IncOverlapKernel r`
  (`ker_incChartEvaluation_overlap`, `ker_incChartEvaluation_overlap_eq`). The edge units
  are the multi-twist transitions of the edge line bundles
  (`incOverlapEdgeUnit_eq_multiTwistTransition`).
* **Kernel transitions.** The chart kernel coordinates give
  `κ_σ : IncOverlapKernel r ≃ R^{3m}` (`incOverlapKernelCoord`), and
  `g_{τσ} = κ_τ ∘ κ_σ⁻¹` (`incKernelTransition`) is an `R`-linear automorphism of
  `R^{3m}`. From the cancellation of inverse isomorphisms: `g_{σσ} = id`,
  `g_{στ} = g_{τσ}⁻¹` and the cocycle condition on any face refined by three charts
  (`incKernelTransition_self`, `incKernelTransition_symm`, `incKernelTransition_trans`).
  Restriction to a smaller face commutes with the transitions
  (`faceRefinementMap_incKernelTransition`, `incKernelTransition_single_restrict`), so the
  restricted pairwise transitions satisfy the cocycle condition on a triple overlap
  (`incKernelTransition_cocycle_restrict`).

Only kernel isomorphisms are used; the `3m × 3m` matrix entries are never computed. The
compatibility with the trivializations of `Z_G` is in
`IncidenceKernelBundleTrivialization.lean`. Not constructed here: the kernel as a sheaf on
the scheme `X_G` and its gluing as a sheaf of modules.
-/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-! ### Composition of face restrictions -/

/-- Exponent restrictions compose along successive face refinements. -/
theorem overlapRefinementExponent_trans {q r s : V → Fin 3} (hqr : FaceRefines q r)
    (hrs : FaceRefines r s) (m : FaceMonoid q) :
    refinementExponent hrs (refinementExponent hqr m) =
      refinementExponent (faceRefines_trans hqr hrs) m := by
  apply faceToInt_injective
  funext v
  rw [faceToInt_refinement, faceToInt_refinement, faceToInt_refinement]
  have h₁ := hqr v
  have h₂ := hrs v
  by_cases hq : q v = 1 <;> by_cases hr : r v = 1 <;> by_cases hs : s v = 2 <;>
    by_cases hr2 : r v = 2 <;> simp_all

/-- Ring restrictions compose along successive face refinements. -/
theorem overlapFaceRefinementMap_trans (R : Type*) [CommRing R] {q r s : V → Fin 3}
    (hqr : FaceRefines q r) (hrs : FaceRefines r s) (x : FaceRing R q) :
    faceRefinementMap R hrs (faceRefinementMap R hqr x) =
      faceRefinementMap R (faceRefines_trans hqr hrs) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m c => simp only [faceRefinementMap_single, overlapRefinementExponent_trans]

section Scaling

variable {R : Type*} [CommRing R]

/-- Multiplication of the `e`-th edge coordinate by the unit `u e`: the diagonal action of
transition units on the trivialized edge bundle `R^m`. -/
def incEdgeScaling (u : E → Rˣ) : (E → R) ≃ₗ[R] (E → R) where
  toFun y e := u e * y e
  invFun y e := ((u e)⁻¹ : Rˣ) * y e
  map_add' y z := by funext e; simp [mul_add]
  map_smul' a y := by funext e; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
  left_inv y := by funext e; simp [← mul_assoc]
  right_inv y := by funext e; simp [← mul_assoc]

/-- The diagonal action multiplies each edge coordinate by its unit. -/
@[simp] theorem incEdgeScaling_apply (u : E → Rˣ) (y : E → R) (e : E) :
    incEdgeScaling u y e = u e * y e := rfl

/-- Diagonal actions compose by multiplying the units. -/
theorem incEdgeScaling_mul (u w : E → Rˣ) :
    (incEdgeScaling (fun e => u e * w e)).toLinearMap =
      (incEdgeScaling u).toLinearMap ∘ₗ (incEdgeScaling w).toLinearMap := by
  apply LinearMap.ext
  intro y
  funext e
  simp [mul_assoc]

end Scaling

/-! ### Chart coordinates restricted to an overlap face -/

section Overlap

variable {σ τ ρ : V → Bool} {r : V → Fin 3}

/-- The affine coordinates `t_v` of the standard chart `σ`, restricted to a face `r` of the
Čech cover refined by `chartFace σ` (for instance the overlap of `σ` with other charts). -/
noncomputable def incOverlapPoint (hσ : FaceRefines (chartFace σ) r) : V → FaceRing ℂ r :=
  fun v => faceRefinementMap ℂ hσ (faceVariable ℂ (chartFace σ) v)

/-- Restriction of chart coordinates is compatible with further refinement of the face. -/
theorem faceRefinementMap_incOverlapPoint (hσ : FaceRefines (chartFace σ) r)
    {s : V → Fin 3} (hrs : FaceRefines r s) (v : V) :
    faceRefinementMap ℂ hrs (incOverlapPoint hσ v) =
      incOverlapPoint (faceRefines_trans hσ hrs) v :=
  overlapFaceRefinementMap_trans ℂ hσ hrs _

/-- The edge-bundle transition unit from chart `σ` to the face `r`: the product of the vertex
transition units at both endpoints of `e` (twice the same unit for a loop). -/
noncomputable def incOverlapEdgeUnit (hσ : FaceRefines (chartFace σ) r) (e : E) :
    (FaceRing ℂ r)ˣ :=
  faceTransitionUnit ℂ hσ (G.fst e) * faceTransitionUnit ℂ hσ (G.snd e)

/-- The orientation of a chart face is the chart itself. -/
theorem chartFace_orientation (σ : V → Bool) (v : V) : decide (chartFace σ v = 1) = σ v := by
  cases h : σ v <;> simp [chartFace, h]

/-- On the face `r`, each chart monomial of chart `σ` is the edge transition unit times the
face's own chart monomial. -/
theorem incChartMonomial_overlapPoint (hσ : FaceRefines (chartFace σ) r) (e : E)
    (ab : Fin 2 × Fin 2) :
    G.incChartMonomial σ (incOverlapPoint hσ) e ab =
      (G.incOverlapEdgeUnit hσ e : FaceRing ℂ r) *
        G.incChartMonomial (faceOrientation r) (faceVariable ℂ r) e ab := by
  have hv (v : V) (α : Fin 2) : incCoord (σ v) α (incOverlapPoint hσ v) =
      (faceTransitionUnit ℂ hσ v : FaceRing ℂ r) *
        incCoord (faceOrientation r v) α (faceVariable ℂ r v) := by
    rw [incOverlapPoint, ← map_incCoord, ← chartFace_orientation σ v]
    exact faceRefinement_incCoord ℂ hσ v α
  simp only [incChartMonomial, hv, incOverlapEdgeUnit, Units.val_mul]
  ring

/-- The evaluation map `B_G ⊗ O → F_G` in the face's own trivialization of the edge bundle. -/
noncomputable def incFaceEvaluation (r : V → Fin 3) :
    (IncCoeffIdx E → FaceRing ℂ r) →ₗ[FaceRing ℂ r] (E → FaceRing ℂ r) :=
  G.incChartEvaluation (faceOrientation r) (faceVariable ℂ r)

/-- On the face `r`, the chart-`σ` evaluation map is the face evaluation map followed by the
diagonal action of the edge transition units. -/
theorem incChartEvaluation_overlap (hσ : FaceRefines (chartFace σ) r) :
    G.incChartEvaluation σ (incOverlapPoint hσ) =
      (incEdgeScaling (G.incOverlapEdgeUnit hσ)).toLinearMap ∘ₗ G.incFaceEvaluation r := by
  apply LinearMap.ext
  intro c
  funext e
  simp only [incChartEvaluation_apply, incChartMonomial_overlapPoint, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, incEdgeScaling_apply, incFaceEvaluation,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun ab _ => ?_
  ring

/-- **Edge-bundle transition on an overlap.** On a face `r` refined by both charts `σ` and `τ`,
the two chart evaluation maps `R^{4m} → R^m` differ by the invertible diagonal action of the
edge-bundle transition units: `E_τ = D_{τσ} ∘ E_σ`. -/
theorem incChartEvaluation_overlap_transition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    G.incChartEvaluation τ (incOverlapPoint hτ) =
      (incEdgeScaling fun e =>
          G.incOverlapEdgeUnit hτ e * (G.incOverlapEdgeUnit hσ e)⁻¹).toLinearMap ∘ₗ
        G.incChartEvaluation σ (incOverlapPoint hσ) := by
  rw [incChartEvaluation_overlap, incChartEvaluation_overlap, ← LinearMap.comp_assoc,
    ← incEdgeScaling_mul]
  congr 3
  funext e
  simp

/-- On a face refined by chart `σ`, the chart-`σ` evaluation map has the same kernel as the face
evaluation map. -/
theorem ker_incChartEvaluation_overlap (hσ : FaceRefines (chartFace σ) r) :
    LinearMap.ker (G.incChartEvaluation σ (incOverlapPoint hσ)) =
      LinearMap.ker (G.incFaceEvaluation r) := by
  rw [incChartEvaluation_overlap, LinearEquiv.ker_comp]

/-- **Same kernel on overlaps.** On a face refined by two charts, their evaluation maps have the
same kernel inside `R^{4m}`. -/
theorem ker_incChartEvaluation_overlap_eq (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    LinearMap.ker (G.incChartEvaluation σ (incOverlapPoint hσ)) =
      LinearMap.ker (G.incChartEvaluation τ (incOverlapPoint hτ)) := by
  rw [ker_incChartEvaluation_overlap, ker_incChartEvaluation_overlap]

/-! ### Kernel coordinates and their transitions -/

/-- The kernel of the evaluation map on the face `r`, the common kernel of all chart evaluation
maps restricted to `r`. -/
noncomputable abbrev IncOverlapKernel (r : V → Fin 3) :=
  LinearMap.ker (G.incFaceEvaluation r)

/-- The kernel coordinates `κ_σ : K ≃ R^{3m}` of chart `σ` on the face `r`: the `3m` non-unit
coefficients of chart `σ`, numbered by `E × Fin 3` as in the chart trivialization. -/
noncomputable def incOverlapKernelCoord (hσ : FaceRefines (chartFace σ) r) :
    G.IncOverlapKernel r ≃ₗ[FaceRing ℂ r] (E × Fin 3 → FaceRing ℂ r) :=
  (LinearEquiv.ofEq _ _ (G.ker_incChartEvaluation_overlap hσ).symm).trans
    (G.incChartEvaluationKernelEquivFree σ (incOverlapPoint hσ))

/-- The kernel coordinates of chart `σ` read off its non-unit coefficients. -/
@[simp] theorem incOverlapKernelCoord_apply (hσ : FaceRefines (chartFace σ) r)
    (k : G.IncOverlapKernel r) (e : E) (i : Fin 3) :
    G.incOverlapKernelCoord hσ k (e, i) = k.1 (e, G.incChartFreeIdx σ e i) :=
  rfl

/-- The inverse kernel coordinates are the chart-`σ` kernel extension. -/
theorem incOverlapKernelCoord_symm_apply (hσ : FaceRefines (chartFace σ) r)
    (y : E × Fin 3 → FaceRing ℂ r) :
    ((G.incOverlapKernelCoord hσ).symm y).1 =
      G.incChartKernelExtend σ (incOverlapPoint hσ) (y ∘ (G.incChartFreeIdxEquiv σ).symm) :=
  rfl

/-- The linear transition `g_{τσ} = κ_τ ∘ κ_σ⁻¹` of the kernel bundle on the face `r`, from
chart-`σ` kernel coordinates to chart-`τ` kernel coordinates. -/
noncomputable def incKernelTransition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    (E × Fin 3 → FaceRing ℂ r) ≃ₗ[FaceRing ℂ r] (E × Fin 3 → FaceRing ℂ r) :=
  (G.incOverlapKernelCoord hσ).symm.trans (G.incOverlapKernelCoord hτ)

/-- Explicit form of the transition: extend the chart-`σ` coordinates to the unique kernel vector
and read off its chart-`τ` non-unit coefficients. -/
theorem incKernelTransition_apply (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (y : E × Fin 3 → FaceRing ℂ r) (e : E) (i : Fin 3) :
    G.incKernelTransition hσ hτ y (e, i) =
      G.incChartKernelExtend σ (incOverlapPoint hσ) (y ∘ (G.incChartFreeIdxEquiv σ).symm)
        (e, G.incChartFreeIdx τ e i) :=
  rfl

/-- `κ_τ = g_{τσ} ∘ κ_σ`. -/
theorem incKernelTransition_kernelCoord (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (k : G.IncOverlapKernel r) :
    G.incKernelTransition hσ hτ (G.incOverlapKernelCoord hσ k) = G.incOverlapKernelCoord hτ k := by
  simp [incKernelTransition]

/-- **Identity.** `g_{σσ} = id`. -/
theorem incKernelTransition_self (hσ : FaceRefines (chartFace σ) r) :
    G.incKernelTransition hσ hσ = LinearEquiv.refl _ _ :=
  LinearEquiv.symm_trans_self _

/-- **Inverse.** `g_{στ} = g_{τσ}⁻¹`. -/
theorem incKernelTransition_symm (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    (G.incKernelTransition hσ hτ).symm = G.incKernelTransition hτ hσ := by
  ext y : 1
  rfl

/-- **Cocycle condition.** On a face refined by three charts, `g_{ρτ} ∘ g_{τσ} = g_{ρσ}`. -/
theorem incKernelTransition_trans (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (hρ : FaceRefines (chartFace ρ) r) :
    (G.incKernelTransition hσ hτ).trans (G.incKernelTransition hτ hρ) =
      G.incKernelTransition hσ hρ := by
  ext y : 1
  simp [incKernelTransition]

/-- **The edge units are the multi-twist transitions of the edge line bundles.** The unit
`u_{fst e} u_{snd e}` is the transition `∏_v u_v^{endCount e v}` of `O(endCount e)`, the twist of
`edgeLineSheaf`; for a loop both factors sit at the same vertex. -/
theorem incOverlapEdgeUnit_eq_multiTwistTransition (hσ : FaceRefines (chartFace σ) r) (e : E) :
    G.incOverlapEdgeUnit hσ e = multiTwistTransition ℂ hσ (fun v => (G.endCount e v : ℤ)) := by
  have h (w : V) : ∏ v, faceTransitionUnit ℂ hσ v ^ (if w = v then (1 : ℤ) else 0) =
      faceTransitionUnit ℂ hσ w := by
    rw [Finset.prod_eq_single w (fun v _ hv => by simp [Ne.symm hv])
      (fun hw => (hw (Finset.mem_univ w)).elim)]
    simp
  simp only [multiTwistTransition, endCount, Nat.cast_add, zpow_add, Finset.prod_mul_distrib,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, h, incOverlapEdgeUnit]

/-! ### Compatibility with restriction to smaller faces -/

/-- A linear endomorphism of `R^ι` is determined by its columns `L(e_k)`. -/
theorem linearMap_apply_eq_sum_single {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (L : (ι → R) →ₗ[R] (ι → R)) (x : ι → R) (j : ι) :
    L x j = ∑ k, x k * L (Pi.single k 1) j := by
  have hx : x = ∑ k, x k • Pi.single k (1 : R) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, map_smul, Finset.sum_apply]

section Naturality

variable {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S]

/-- Chart monomials commute with ring homomorphisms. -/
theorem map_incChartMonomial (φ : F) (σ : V → Bool) (t : V → R) (e : E) (ab : Fin 2 × Fin 2) :
    φ (G.incChartMonomial σ t e ab) = G.incChartMonomial σ (fun v => φ (t v)) e ab := by
  simp [incChartMonomial, map_incCoord]

/-- The kernel extension commutes with ring homomorphisms. -/
theorem map_incChartKernelExtend (φ : F) (σ : V → Bool) (t : V → R)
    (y : G.IncChartFiberIdx σ → R) (c : IncCoeffIdx E) :
    φ (G.incChartKernelExtend σ t y c) =
      G.incChartKernelExtend σ (fun v => φ (t v)) (fun i => φ (y i)) c := by
  unfold incChartKernelExtend
  split_ifs <;> simp [map_incChartMonomial]

end Naturality

/-- **Restriction of transitions.** For a face `s` refining `r`, the transition on `s` is the
restriction of the transition on `r`: restricting the entries commutes with `g_{τσ}`. -/
theorem faceRefinementMap_incKernelTransition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) {s : V → Fin 3} (hrs : FaceRefines r s)
    (y : E × Fin 3 → FaceRing ℂ r) (j : E × Fin 3) :
    faceRefinementMap ℂ hrs (G.incKernelTransition hσ hτ y j) =
      G.incKernelTransition (faceRefines_trans hσ hrs) (faceRefines_trans hτ hrs)
        (fun i => faceRefinementMap ℂ hrs (y i)) j := by
  obtain ⟨e, i⟩ := j
  rw [incKernelTransition_apply, incKernelTransition_apply, map_incChartKernelExtend]
  congr 1
  funext v
  exact faceRefinementMap_incOverlapPoint hσ hrs v

/-- The transition on a smaller face has the restricted columns: `g^s(e_i) = g^r(e_i)|_s`. -/
theorem incKernelTransition_single_restrict (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) {s : V → Fin 3} (hrs : FaceRefines r s)
    (i j : E × Fin 3) :
    G.incKernelTransition (faceRefines_trans hσ hrs) (faceRefines_trans hτ hrs)
        (Pi.single i 1) j =
      faceRefinementMap ℂ hrs (G.incKernelTransition hσ hτ (Pi.single i 1) j) := by
  have hy : (fun k => faceRefinementMap ℂ hrs
      ((Pi.single i (1 : FaceRing ℂ r) : E × Fin 3 → FaceRing ℂ r) k)) =
      Pi.single i 1 := by
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_eq_of_ne hk]
  rw [faceRefinementMap_incKernelTransition, hy]

/-- **Cocycle condition for restricted pairwise transitions.** Let `q₁, q₂, q₃` be faces refined
by the chart pairs `(σ, τ)`, `(τ, ρ)` and `(σ, ρ)` (for instance the pairwise chart overlaps), and
let `s` refine all three (for instance the triple overlap). After restricting the columns of the
three pairwise transitions to `s`, they satisfy `g_{ρτ} ∘ g_{τσ} = g_{ρσ}`, written on the
columns `e_i`: `Σ_k g_{τσ}(e_i)_k · g_{ρτ}(e_k)_j = g_{ρσ}(e_i)_j`. -/
theorem incKernelTransition_cocycle_restrict {q₁ q₂ q₃ s : V → Fin 3}
    (hσ₁ : FaceRefines (chartFace σ) q₁) (hτ₁ : FaceRefines (chartFace τ) q₁)
    (hτ₂ : FaceRefines (chartFace τ) q₂) (hρ₂ : FaceRefines (chartFace ρ) q₂)
    (hσ₃ : FaceRefines (chartFace σ) q₃) (hρ₃ : FaceRefines (chartFace ρ) q₃)
    (h₁ : FaceRefines q₁ s) (h₂ : FaceRefines q₂ s) (h₃ : FaceRefines q₃ s) (i j : E × Fin 3) :
    ∑ k, faceRefinementMap ℂ h₁ (G.incKernelTransition hσ₁ hτ₁ (Pi.single i 1) k) *
        faceRefinementMap ℂ h₂ (G.incKernelTransition hτ₂ hρ₂ (Pi.single k 1) j) =
      faceRefinementMap ℂ h₃ (G.incKernelTransition hσ₃ hρ₃ (Pi.single i 1) j) := by
  simp only [← incKernelTransition_single_restrict]
  have hs := LinearEquiv.congr_fun (G.incKernelTransition_trans (faceRefines_trans hσ₁ h₁)
    (faceRefines_trans hτ₁ h₁) (faceRefines_trans hρ₂ h₂)) (Pi.single i 1)
  rw [LinearEquiv.trans_apply] at hs
  have hsum := congrFun hs j
  rw [← hsum]
  exact (linearMap_apply_eq_sum_single (G.incKernelTransition _ _).toLinearMap _ j).symm

end Overlap

end BPFixedPoints.Multigraph
