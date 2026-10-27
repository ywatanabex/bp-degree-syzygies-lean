import BPFixedPoints.StrongField.Branch
import BPFixedPoints.Degree.Generic.SimpleTransfer
import BPFixedPoints.Degree.WeakCoupling.Index

/-!
# Simplicity of strong-field roots (`thm:real` (i))

A BP Jacobian kernel element w, with u=w/y, satisfies
P_αu_α+R_αΣ_{γ∈N(α)}u_γ=0, P_α=y_α(X_α+a), R_α=(y_α−a)X_α
(`bpMvPoly_dirDeriv`, `cavity_dirDeriv`). On a state-S chart, divide rows by
P off S and R on S to form `normC`. Its coefficients R/P off S and P/R on S
tend to zero at strong fields. The limit `normLim` has nonbacktracking rows
on S and identity rows elsewhere; its determinant is
(−1)^{|S|}∏_v(1−d_S(v))≠0 (`det_normLim`). Hence every root is simple for
sufficiently strong fields (`strong_field_all_simple`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Filter Topology Matrix

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

section Limit

variable (S : Finset E)

/-- Limit normalized matrix: nonbacktracking rows on S and identity rows elsewhere. -/
def normLim : Matrix (Dart E) (Dart E) ℂ := fun α γ =>
  if α.1 ∈ S then G.nbMatrix ℂ α γ else if α = γ then 1 else 0

/-- **The limit determinant equals the state determinant.** -/
theorem det_normLim : (G.normLim S).det = (-1) ^ S.card * ∏ v, (1 - (G.deg S v : ℂ)) := by
  let e := Equiv.sumCompl (fun α : Dart E => α.1 ∈ S)
  have hblock : (G.normLim S).submatrix e e =
      fromBlocks ((G.normLim S).submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E)
          Subtype.val)
        ((G.normLim S).submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E)
          (Subtype.val : {α : Dart E // α.1 ∉ S} → Dart E)) 0 1 := by
    ext (⟨α, hα⟩ | ⟨α, hα⟩) (⟨γ, hγ⟩ | ⟨γ, hγ⟩)
    · rfl
    · rfl
    · simp only [normLim, e, Equiv.sumCompl_apply_inr, Equiv.sumCompl_apply_inl, submatrix_apply,
        hα, ↓reduceIte, fromBlocks_apply₂₁]
      have h : α ≠ γ := by rintro rfl; exact hα hγ
      simp [h]
    · simp only [normLim, e, Equiv.sumCompl_apply_inr, submatrix_apply, hα, ↓reduceIte,
        fromBlocks_apply₂₂, one_apply]
      by_cases h : α = γ
      · subst h; simp
      · simp [h]
  rw [← det_submatrix_equiv_self e, hblock, det_fromBlocks_zero₂₁, det_one, mul_one,
    ← det_submatrix_equiv_self (activeDartEquiv S)]
  have hA : ((G.normLim S).submatrix (Subtype.val : {α : Dart E // α.1 ∈ S} → Dart E)
      Subtype.val).submatrix (activeDartEquiv S) (activeDartEquiv S) = G.stateMatrix ℂ S := by
    rw [stateMatrix_eq_submatrix]
    ext ⟨⟨a, ha⟩, d⟩ ⟨⟨b, hb⟩, d'⟩
    simp [normLim, activeDartEquiv, ha]
  rw [hA, det_stateMatrix]

theorem det_normLim_ne_zero (hS : IsState G S) : (G.normLim S).det ≠ 0 := by
  rw [det_normLim]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
  rw [sub_ne_zero]
  exact_mod_cast (hS v).symm

end Limit

section Coeff

variable (S : Finset E)

/-- Normalized chart coefficient, zero at the base point: P/R on S, R/P outside S. -/
noncomputable def coeffS (x : E ⊕ V → ℂ) (z : Dart E ⊕ V → ℂ) (α : Dart E) : ℂ :=
  if α.1 ∈ S then
    ((-(x (Sum.inr (G.head α)) * z (Sum.inr (G.head α))) / z (Sum.inl α)) *
        (x (Sum.inl α.1) - z (Sum.inl (rev α)))) /
      ((-(x (Sum.inr (G.head α)) * z (Sum.inr (G.head α))) / z (Sum.inl α) - x (Sum.inl α.1)) *
        (-z (Sum.inl (rev α))))
  else if G.deg S (G.tail α) = 0 then
    (z (Sum.inl α) - x (Sum.inl α.1)) /
      (z (Sum.inl α) * (1 + x (Sum.inl α.1) * (x (Sum.inr (G.tail α)) * z (Sum.inr (G.tail α))) *
        z (Sum.inl (rev α))))
  else
    (z (Sum.inl α) - x (Sum.inl α.1)) * (x (Sum.inr (G.tail α)) * z (Sum.inr (G.tail α))) /
      (z (Sum.inl α) * (x (Sum.inr (G.tail α)) * z (Sum.inr (G.tail α)) +
        x (Sum.inl α.1) * z (Sum.inl (rev α))))

/-- Normalized matrix. -/
noncomputable def normC (x : E ⊕ V → ℂ) (z : Dart E ⊕ V → ℂ) : Matrix (Dart E) (Dart E) ℂ :=
  fun α γ => if α.1 ∈ S then G.coeffS S x z α * (if α = γ then 1 else 0) + G.nbMatrix ℂ α γ
    else (if α = γ then 1 else 0) + G.coeffS S x z α * G.nbMatrix ℂ α γ

/-- Denominator of a row on S, normalizing R. -/
noncomputable def denS (_S : Finset E) (x : E ⊕ V → ℂ) (z : Dart E ⊕ V → ℂ) (α : Dart E) : ℂ :=
  (-(x (Sum.inr (G.head α)) * z (Sum.inr (G.head α))) / z (Sum.inl α) - x (Sum.inl α.1)) *
    (-z (Sum.inl (rev α)))

variable {G S} {a : E → ℂ} {ω : V → ℂ}

theorem coeffS_base (α : Dart E) :
    G.coeffS S (Sum.elim a 0) (Sum.elim (G.q0 S a) ω) α = 0 := by
  unfold coeffS
  split_ifs with h1 h2
  · simp
  · simp [q0, h2]
  · simp

theorem normC_base :
    G.normC S (Sum.elim a 0) (Sum.elim (G.q0 S a) ω) = G.normLim S := by
  ext α γ
  simp only [normC, normLim, coeffS_base, zero_mul, zero_add, add_zero]

theorem denS_base (ha : ∀ e, a e ≠ 0) {α : Dart E} (hα : α.1 ∈ S) :
    G.denS S (Sum.elim a 0) (Sum.elim (G.q0 S a) ω) α ≠ 0 := by
  have hh : G.deg S (G.head α) ≠ 0 := deg_ne_zero_of_mem hα (head_incident α)
  simp only [denS, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_mul, neg_zero, zero_div,
    zero_sub, q0, tail_rev, rev_fst, hh, ↓reduceIte]
  have := ha α.1
  field_simp
  simp

/-- The normalized matrix is continuous at the base point. -/
theorem continuousAt_normC (ha : ∀ e, a e ≠ 0) {ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)}
    (hψ0 : ψ (Sum.elim a 0) = Sum.elim (G.q0 S a) ω) (hc : ContinuousAt ψ (Sum.elim a 0)) :
    ContinuousAt (fun x => G.normC S x (ψ x)) (Sum.elim a 0) := by
  have hcq : ∀ v, ContinuousAt (fun x => ψ x v) (Sum.elim a 0) := fun v =>
    (continuous_apply v).continuousAt.comp hc
  have hcx : ∀ j, ContinuousAt (fun x : E ⊕ V → ℂ => x j) (Sum.elim a 0) := fun j =>
    (continuous_apply j).continuousAt
  have hq0 : ∀ α, ψ (Sum.elim a 0) (Sum.inl α) = G.q0 S a α := fun α => by rw [hψ0]; rfl
  have hq0ne : ∀ α, ψ (Sum.elim a 0) (Sum.inl α) ≠ 0 := fun α => by
    rw [hq0]; exact q0_ne_zero ha α
  have hcoef : ∀ α, ContinuousAt (fun x => G.coeffS S x (ψ x) α) (Sum.elim a 0) := by
    intro α
    unfold coeffS
    by_cases h1 : α.1 ∈ S
    · simp only [h1, ↓reduceIte]
      have hd := denS_base (G := G) (ω := ω) ha h1
      rw [← hψ0] at hd
      refine ContinuousAt.div ?_ ?_ hd
      · exact ((((hcx _).mul (hcq _)).neg.div (hcq _) (hq0ne α))).mul ((hcx _).sub (hcq _))
      · exact (((((hcx _).mul (hcq _)).neg.div (hcq _) (hq0ne α))).sub (hcx _)).mul (hcq _).neg
    · simp only [h1, ↓reduceIte]
      split_ifs with h2
      · refine ((hcq _).sub (hcx _)).div ((hcq _).mul (continuousAt_const.add
          (((hcx _).mul ((hcx _).mul (hcq _))).mul (hcq _)))) ?_
        simp only [hq0, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_mul, mul_zero, add_zero,
          mul_one]
        exact q0_ne_zero ha α
      · refine (((hcq _).sub (hcx _)).mul ((hcx _).mul (hcq _))).div ((hcq _).mul
          (((hcx _).mul (hcq _)).add ((hcx _).mul (hcq _)))) ?_
        simp only [hq0, Sum.elim_inr, Sum.elim_inl, Pi.zero_apply, zero_mul, zero_add]
        exact mul_ne_zero (q0_ne_zero ha α) (mul_ne_zero (ha _) (q0_ne_zero ha _))
  refine continuousAt_pi.2 fun α => continuousAt_pi.2 fun γ => ?_
  by_cases h : α.1 ∈ S
  · simp only [normC, h, ↓reduceIte]
    exact ((hcoef α).mul continuousAt_const).add continuousAt_const
  · simp only [normC, h, ↓reduceIte]
    exact continuousAt_const.add ((hcoef α).mul continuousAt_const)

end Coeff

section Alg

theorem rowS_alg {yα X A w su : ℂ} (hy : yα ≠ 0) (hR : (yα - A) * X ≠ 0)
    (hr : w * (X + A) + (yα - A) * (X * su) = 0) :
    (yα * (X + A)) / ((yα - A) * X) * (w / yα) + su = 0 := by
  have h1 : (yα * (X + A)) / ((yα - A) * X) * (w / yα) = w * (X + A) / ((yα - A) * X) := by
    field_simp
  rw [h1, div_add' _ _ _ hR, div_eq_zero_iff]
  left
  linear_combination hr

theorem rowN_alg {yα X A w su : ℂ} (hy : yα ≠ 0) (hP : X + A ≠ 0)
    (hr : w * (X + A) + (yα - A) * (X * su) = 0) :
    w / yα + ((yα - A) * X) / (yα * (X + A)) * su = 0 := by
  have hyP : yα * (X + A) ≠ 0 := mul_ne_zero hy hP
  have h1 : w / yα = w * (X + A) / (yα * (X + A)) := by field_simp
  rw [h1, div_mul_eq_mul_div, ← add_div, div_eq_zero_iff]
  left
  linear_combination hr

theorem coeff_in_alg {q q' f A : ℂ} (hq' : q' ≠ 0) (hf : f ≠ 0) :
    (q - A) / (q * (1 + A * f * q')) = ((q - A) * (f⁻¹ / q')) / (q * (f⁻¹ / q' + A)) := by
  have e1 : (q - A) * (f⁻¹ / q') = (q - A) / (f * q') := by field_simp
  have e2 : q * (f⁻¹ / q' + A) = q * (1 + A * f * q') / (f * q') := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ (mul_ne_zero hf hq')]

theorem coeff_act_alg {q q' f A : ℂ} (hq' : q' ≠ 0) :
    (q - A) * f / (q * (f + A * q')) = ((q - A) * (f / q')) / (q * (f / q' + A)) := by
  have e1 : (q - A) * (f / q') = (q - A) * f / q' := by ring
  have e2 : q * (f / q' + A) = q * (f + A * q') / q' := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hq']

end Alg

section Kernel

variable {S : Finset E}

theorem sum_nbMatrix_mul (u : Dart E → ℂ) (α : Dart E) :
    ∑ γ, G.nbMatrix ℂ α γ * u γ = ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), u γ := by
  classical
  have h : ∀ γ, G.nbMatrix ℂ α γ * u γ =
      if γ ∈ (G.inDarts (G.tail α)).erase (rev α) then u γ else 0 := by
    intro γ
    simp only [nbMatrix, Finset.mem_erase, inDarts, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h1 : G.head γ = G.tail α <;> by_cases h2 : γ = rev α <;> simp [h1, h2]
  simp_rw [h]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Kernel transfer.** At a good chart point, a BP Jacobian kernel element w gives u=w/y in the normalized matrix kernel. -/
theorem normC_mulVec_eq_zero (hG : G.Loopless) (hS : IsState G S)
    {ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)} {x : E ⊕ V → ℂ} (hx : GoodAt G S ψ x)
    (hπ : ∀ i, x (Sum.inr i) ≠ 0) (hden : ∀ α, α.1 ∈ S → G.denS S x (ψ x) α ≠ 0)
    {w : Dart E → ℂ}
    (hw : (G.jacobian (fun e => x (Sum.inl e)) (G.chartB S fun i => x (Sum.inr i))
      (G.chartY S (fun i => x (Sum.inr i)) (ψ x))).mulVec w = 0) :
    (G.normC S x (ψ x)).mulVec
      (fun γ => w γ / G.chartY S (fun i => x (Sum.inr i)) (ψ x) γ) = 0 := by
  classical
  set π : V → ℂ := fun i => x (Sum.inr i)
  set a : E → ℂ := fun e => x (Sum.inl e)
  set z := ψ x
  set y := G.chartY S π z
  set b := G.chartB S π
  obtain ⟨hadm, htot⟩ := hx.admissible hG hS hπ
  have hy0 : ∀ γ, y γ ≠ 0 := hadm.2.1
  have hcav : ∀ α, G.cavity b y α = G.chartF S π z (G.tail α) / y (rev α) := by
    intro α
    have := G.totalField_tail_eq b y α
    rw [htot] at this
    rw [this, mul_div_cancel_right₀ _ (hy0 _)]
  -- Row identities.
  have hrow : ∀ α, w α * (G.cavity b y α + a α.1) +
      (y α - a α.1) * (G.cavity b y α * ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ) =
        0 := by
    intro α
    have h := congrFun hw α
    rw [mulVec_apply'] at h
    have h1 := G.bpMvPoly_dirDeriv b y a α w
    have h2 := G.cavity_dirDeriv b y hy0 α w
    simp only [jacobian] at h
    rw [h1, h2] at h
    exact h
  funext α
  rw [mulVec_apply', Pi.zero_apply]
  have hsum := G.sum_nbMatrix_mul (fun γ => w γ / y γ) α
  have hw0 := hx.w_ne
  have hq0 := hx.q_ne
  set su := ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ
  set X := G.cavity b y α
  have hP : y α * (X + a α.1) ≠ 0 := mul_ne_zero (hy0 α) (hadm.2.2.1 α)
  have hr := hrow α
  have hXne : X ≠ 0 := by
    simp only [X, cavity, b, chartB]
    exact mul_ne_zero (div_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      (pow_ne_zero _ (hπ _))) (Finset.prod_ne_zero_iff.2 fun γ _ => hy0 γ)
  by_cases hα : α.1 ∈ S
  · -- Rows on S: (P/R)u_α+Σu=0.
    have hrow' : ∑ γ, G.normC S x z α γ * (w γ / y γ) =
        G.coeffS S x z α * (w α / y α) + su := by
      simp only [normC, hα, ↓reduceIte, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul,
        one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ]
      rw [hsum]
    rw [hrow']
    obtain ⟨ht, hh⟩ : G.deg S (G.tail α) ≠ 0 ∧ G.deg S (G.head α) ≠ 0 :=
      ⟨deg_ne_zero_of_mem hα (tail_incident α), deg_ne_zero_of_mem hα (head_incident α)⟩
    have hrS : (rev α).1 ∈ S := hα
    have hyα : y α = -(π (G.head α) * z (Sum.inr (G.head α))) / z (Sum.inl α) := by
      simp only [y, chartY, chartF, hα, hh, ↓reduceIte]
    have hyr : y (rev α) = -(π (G.tail α) * z (Sum.inr (G.tail α))) / z (Sum.inl (rev α)) := by
      simp only [y, chartY, chartF, hrS, head_rev, ht, ↓reduceIte]
    have hX : X = -z (Sum.inl (rev α)) := by
      simp only [X]
      rw [hcav, hyr]
      simp only [chartF, ht, ↓reduceIte]
      have hf : π (G.tail α) * z (Sum.inr (G.tail α)) ≠ 0 := mul_ne_zero (hπ _) (hw0 _)
      rw [neg_div, div_neg, div_div_eq_mul_div, mul_div_cancel_left₀ _ hf]
    have hc : G.coeffS S x z α = (y α * (X + a α.1)) / ((y α - a α.1) * X) := by
      rw [hyα, hX]
      unfold coeffS
      simp only [hα, ↓reduceIte]
      ring
    have hR : (y α - a α.1) * X ≠ 0 := by
      have := hden α hα
      unfold denS at this
      rw [hyα, hX]
      exact this
    rw [hc]
    exact rowS_alg (hy0 α) hR hr
  · -- Rows outside S: u_α+(R/P)Σu=0.
    have hrow' : ∑ γ, G.normC S x z α γ * (w γ / y γ) =
        w α / y α + G.coeffS S x z α * su := by
      simp only [normC, hα, ↓reduceIte, add_mul, Finset.sum_add_distrib, mul_assoc, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
      rw [← Finset.mul_sum, hsum]
    rw [hrow']
    have hrS : (rev α).1 ∉ S := hα
    have hyα : y α = z (Sum.inl α) := by simp only [y, chartY, hα, ↓reduceIte]
    have hyr : y (rev α) = z (Sum.inl (rev α)) := by simp only [y, chartY, hrS, ↓reduceIte]
    have hqr := hq0 (rev α)
    have hqa := hq0 α
    have hf : π (G.tail α) * z (Sum.inr (G.tail α)) ≠ 0 := mul_ne_zero (hπ _) (hw0 _)
    have hc : G.coeffS S x z α = ((y α - a α.1) * X) / (y α * (X + a α.1)) := by
      simp only [X]
      rw [hcav, hyr, hyα]
      unfold coeffS chartF
      simp only [hα, ↓reduceIte]
      split_ifs with ht
      · exact coeff_in_alg hqr hf
      · exact coeff_act_alg hqr
    rw [hc]
    exact rowN_alg (hy0 α) (hadm.2.2.1 α) hr

/-- At a good chart point, a nonsingular normalized matrix makes the BP solution simple. -/
theorem isSimple_of_det_normC (hG : G.Loopless) (hS : IsState G S)
    {ψ : (E ⊕ V → ℂ) → (Dart E ⊕ V → ℂ)} {x : E ⊕ V → ℂ} (hx : GoodAt G S ψ x)
    (hπ : ∀ i, x (Sum.inr i) ≠ 0) (hden : ∀ α, α.1 ∈ S → G.denS S x (ψ x) α ≠ 0)
    (hdet : (G.normC S x (ψ x)).det ≠ 0) :
    G.IsSimpleSolution (fun e => x (Sum.inl e)) (G.chartB S fun i => x (Sum.inr i))
      (G.chartY S (fun i => x (Sum.inr i)) (ψ x)) := by
  classical
  obtain ⟨hadm, -⟩ := hx.admissible hG hS hπ
  unfold IsSimpleSolution
  intro h0
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hu := G.normC_mulVec_eq_zero hG hS hx hπ hden hw
  have hu0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hu
  apply hw0
  funext γ
  have := congrFun hu0 γ
  simp only [Pi.zero_apply, div_eq_zero_iff] at this
  rcases this with h | h
  · exact h
  · exact absurd h (hadm.2.1 γ)

end Kernel

end Multigraph

end BPFixedPoints
