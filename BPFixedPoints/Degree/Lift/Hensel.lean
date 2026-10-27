import BPFixedPoints.Degree.Lift.Taylor

/-!
# Multivariate Hensel lemma: formal implicit function theorem

For a square polynomial system f_i over K⟦X⟧ and residue point x₀:ι→K,
if f(x₀)≡0 mod X and the residue Jacobian determinant is nonzero, there is
a unique x:ι→K⟦X⟧ with x≡x₀ mod X and f(x)=0.
Newton iteration upgrades a solution modulo X^{n+1} to one modulo X^{n+2}
by x−X^{n+1}J(x)⁻¹u when f(x)=X^{n+1}u. The quadratic remainder is divisible
by X^{2n+2} (`taylor_first_order`); stabilized coefficients define the limit.
For uniqueness, if a difference h is divisible by X^m, then J(x)h is divisible
by X^{2m}; invertibility forces h to be divisible by X^{2m} as well.
-/

namespace BPFixedPoints.BP

open MvPolynomial
open scoped PowerSeries

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (f : ι → MvPolynomial ι K⟦X⟧) (x₀ : ι → K)

/-- Jacobian matrix over K[[X]] at x. -/
noncomputable def jacPS (x : ι → K⟦X⟧) : Matrix ι ι K⟦X⟧ :=
  Matrix.of fun i j => eval x (pderiv j (f i))

/-- Residue Jacobian over K at x₀. -/
noncomputable def jacRes : Matrix ι ι K :=
  Matrix.of fun i j => PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (pderiv j (f i)))

/-- Residue point x₀: every component has constant coefficient x₀. -/
def Reduces (x : ι → K⟦X⟧) : Prop := ∀ j, PowerSeries.constantCoeff (x j) = x₀ j

variable {f x₀}

theorem X_dvd_sub_C_of_reduces {x : ι → K⟦X⟧} (hx : Reduces x₀ x) (j : ι) :
    (PowerSeries.X : K⟦X⟧) ∣ x j - PowerSeries.C (x₀ j) := by
  rw [PowerSeries.X_dvd_iff, map_sub, PowerSeries.constantCoeff_C, hx j, sub_self]

/-- At residue point x₀, evaluation has the same constant coefficient as evaluation at x₀. -/
theorem PowerSeries.constantCoeff_eval_eq {x : ι → K⟦X⟧} (hx : Reduces x₀ x) (g : MvPolynomial ι K⟦X⟧) :
    PowerSeries.constantCoeff (eval x g) = PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) g) := by
  have := dvd_eval_sub_eval (c := (PowerSeries.X : K⟦X⟧)) (x := fun j => PowerSeries.C (x₀ j)) (x' := x)
    (fun j => X_dvd_sub_C_of_reduces hx j) g
  rw [PowerSeries.X_dvd_iff, map_sub, sub_eq_zero] at this
  exact this

theorem PowerSeries.constantCoeff_mapMatrix_jacPS {x : ι → K⟦X⟧} (hx : Reduces x₀ x) :
    (PowerSeries.constantCoeff : K⟦X⟧ →+* K).mapMatrix (jacPS f x) = jacRes f x₀ := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, jacPS, jacRes, Matrix.of_apply]
  exact PowerSeries.constantCoeff_eval_eq hx _

/-- An invertible residue Jacobian makes the Jacobian invertible over K[[X]] at every lift of x₀. -/
theorem isUnit_det_jacPS (hJ : (jacRes f x₀).det ≠ 0) {x : ι → K⟦X⟧} (hx : Reduces x₀ x) :
    IsUnit (jacPS f x).det := by
  rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det, PowerSeries.constantCoeff_mapMatrix_jacPS hx]
  exact isUnit_iff_ne_zero.2 hJ

omit [DecidableEq ι] in
theorem mulVec_eq_sum (M : Matrix ι ι K⟦X⟧) (w : ι → K⟦X⟧) (i : ι) :
    M.mulVec w i = ∑ j, M i j * w j := by
  simp [Matrix.mulVec, dotProduct]

section Newton

variable (f x₀)

open Classical in
/-- One Newton step improves precision from X^{n+1} to X^{n+2} at residue x₀; inputs failing the conditions are returned unchanged. -/
noncomputable def newtonStep (n : ℕ) (x : ι → K⟦X⟧) : ι → K⟦X⟧ :=
  if h : Reduces x₀ x ∧ ∀ i, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ eval x (f i) then
    fun j => x j - PowerSeries.X ^ (n + 1) *
      ((jacPS f x)⁻¹.mulVec (fun i => Classical.choose (h.2 i))) j
  else x

variable {f x₀}

theorem newtonStep_spec (hJ : (jacRes f x₀).det ≠ 0) (n : ℕ) {x : ι → K⟦X⟧}
    (hx : Reduces x₀ x) (hdiv : ∀ i, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ eval x (f i)) :
    Reduces x₀ (newtonStep f x₀ n x) ∧
      (∀ j, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ newtonStep f x₀ n x j - x j) ∧
      ∀ i, (PowerSeries.X : K⟦X⟧) ^ (n + 2) ∣ eval (newtonStep f x₀ n x) (f i) := by
  have hcond : Reduces x₀ x ∧ ∀ i, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ eval x (f i) := ⟨hx, hdiv⟩
  simp only [newtonStep, dif_pos hcond]
  set u : ι → K⟦X⟧ := fun i => Classical.choose (hcond.2 i) with hu
  have hu_spec : ∀ i, eval x (f i) = PowerSeries.X ^ (n + 1) * u i :=
    fun i => Classical.choose_spec (hcond.2 i)
  set w := (jacPS f x)⁻¹.mulVec u with hw
  set hv : ι → K⟦X⟧ := fun j => -(PowerSeries.X ^ (n + 1) * w j) with hhv
  have hx' : (fun j => x j - PowerSeries.X ^ (n + 1) * w j) = x + hv := by
    funext j; simp only [hhv, Pi.add_apply]; ring
  have hhv_dvd : ∀ j, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ hv j := fun j => by
    simp only [hhv]; exact (dvd_mul_right _ _).neg_right
  refine ⟨?_, ?_, ?_⟩
  · intro j
    simp [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_X, hx j]
  · intro j
    simp only [sub_sub_cancel_left]
    exact (dvd_mul_right _ _).neg_right
  · intro i
    rw [hx']
    have ht := taylor_first_order (f i) x hv
    have hJsum : ∑ j, eval x (pderiv j (f i)) * hv j = -(PowerSeries.X ^ (n + 1) * u i) := by
      have hs : ∑ j, eval x (pderiv j (f i)) * w j = ((jacPS f x).mulVec w) i := by
        rw [mulVec_eq_sum]; rfl
      simp only [hhv, mul_neg, Finset.sum_neg_distrib]
      congr 1
      rw [show ∑ j, eval x (pderiv j (f i)) * (PowerSeries.X ^ (n + 1) * w j) =
          PowerSeries.X ^ (n + 1) * ∑ j, eval x (pderiv j (f i)) * w j by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring]
      rw [hs, hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_jacPS hJ hx),
        Matrix.one_mulVec]
    have hr : (PowerSeries.X : K⟦X⟧) ^ (n + 2) ∣
        eval (x + hv) (f i) - eval x (f i) - ∑ j, eval x (pderiv j (f i)) * hv j := by
      have h2 := dvd_sq_of_mem_quadIdeal hhv_dvd ht
      rw [← pow_mul] at h2
      exact Dvd.dvd.trans (pow_dvd_pow _ (by omega : n + 2 ≤ (n + 1) * 2)) h2
    have e : eval (x + hv) (f i) =
        (eval (x + hv) (f i) - eval x (f i) - ∑ j, eval x (pderiv j (f i)) * hv j) +
          (eval x (f i) + ∑ j, eval x (pderiv j (f i)) * hv j) := by ring
    rw [e, hJsum, hu_spec i, add_neg_cancel, add_zero]
    rw [hJsum, hu_spec i] at hr
    exact hr

variable (f x₀)

/-- Newton sequence, beginning at x₀ and improving precision at each step. -/
noncomputable def newtonSeq : ℕ → (ι → K⟦X⟧)
  | 0 => fun j => PowerSeries.C (x₀ j)
  | n + 1 => newtonStep f x₀ n (newtonSeq n)

variable {f x₀}

theorem newtonSeq_spec (hJ : (jacRes f x₀).det ≠ 0)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0) (n : ℕ) :
    Reduces x₀ (newtonSeq f x₀ n) ∧ ∀ i, (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ eval (newtonSeq f x₀ n) (f i) := by
  induction n with
  | zero =>
    refine ⟨fun j => by simp [newtonSeq], fun i => ?_⟩
    rw [pow_one, PowerSeries.X_dvd_iff]
    exact h0 i
  | succ n ih =>
    obtain ⟨h1, _, h3⟩ := newtonStep_spec hJ n ih.1 ih.2
    exact ⟨h1, h3⟩

theorem newtonSeq_succ_sub_dvd (hJ : (jacRes f x₀).det ≠ 0)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0) (n : ℕ) (j : ι) :
    (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ newtonSeq f x₀ (n + 1) j - newtonSeq f x₀ n j :=
  (newtonStep_spec hJ n (newtonSeq_spec hJ h0 n).1 (newtonSeq_spec hJ h0 n).2).2.1 j

/-- Coefficient stabilization: for k≤n, the degree-k coefficient at step n equals that at step k. -/
theorem coeff_newtonSeq_stable (hJ : (jacRes f x₀).det ≠ 0)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0) (k m : ℕ) (j : ι) :
    PowerSeries.coeff k (newtonSeq f x₀ (k + m) j) = PowerSeries.coeff k (newtonSeq f x₀ k j) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hd := newtonSeq_succ_sub_dvd hJ h0 (k + m) j
    have := (PowerSeries.X_pow_dvd_iff.1 hd) k (by omega)
    rw [map_sub, sub_eq_zero] at this
    rw [show k + (m + 1) = k + m + 1 by ring, this, ih]

variable (f x₀)

/-- Limit of Newton iteration, whose degree-k coefficient is that at step k. -/
noncomputable def newtonLimit : ι → K⟦X⟧ :=
  fun j => PowerSeries.mk fun k => PowerSeries.coeff k (newtonSeq f x₀ k j)

variable {f x₀}

theorem newtonLimit_sub_dvd (hJ : (jacRes f x₀).det ≠ 0)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0) (n : ℕ) (j : ι) :
    (PowerSeries.X : K⟦X⟧) ^ (n + 1) ∣ newtonLimit f x₀ j - newtonSeq f x₀ n j := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, newtonLimit, PowerSeries.coeff_mk, sub_eq_zero]
  have := coeff_newtonSeq_stable hJ h0 m (n - m) j
  rw [show m + (n - m) = n by omega] at this
  exact this.symm

theorem newtonLimit_reduces : Reduces x₀ (newtonLimit f x₀) := by
  intro j
  rw [newtonLimit, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp [newtonSeq, PowerSeries.constantCoeff_C]

theorem eval_newtonLimit (hJ : (jacRes f x₀).det ≠ 0)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0) (i : ι) :
    eval (newtonLimit f x₀) (f i) = 0 := by
  apply PowerSeries.ext
  intro k
  have h1 : (PowerSeries.X : K⟦X⟧) ^ (k + 1) ∣ eval (newtonLimit f x₀) (f i) - eval (newtonSeq f x₀ k) (f i) :=
    dvd_eval_sub_eval (fun j => newtonLimit_sub_dvd hJ h0 k j) (f i)
  have h2 := (newtonSeq_spec hJ h0 k).2 i
  have h3 : (PowerSeries.X : K⟦X⟧) ^ (k + 1) ∣ eval (newtonLimit f x₀) (f i) := by
    have := dvd_add h1 h2
    rwa [sub_add_cancel] at this
  rw [map_zero]
  exact (PowerSeries.X_pow_dvd_iff.1 h3) k (by omega)

end Newton

/-- Uniqueness: two roots with the same residue point coincide. -/
theorem hensel_unique (hJ : (jacRes f x₀).det ≠ 0) {x x' : ι → K⟦X⟧} (hx : Reduces x₀ x)
    (hx' : Reduces x₀ x') (hfx : ∀ i, eval x (f i) = 0) (hfx' : ∀ i, eval x' (f i) = 0) :
    x = x' := by
  have key : ∀ m, 1 ≤ m → (∀ j, (PowerSeries.X : K⟦X⟧) ^ m ∣ x' j - x j) →
      ∀ j, (PowerSeries.X : K⟦X⟧) ^ (m + 1) ∣ x' j - x j := by
    intro m hm hd j
    have hJv : ∀ i, (PowerSeries.X : K⟦X⟧) ^ (m * 2) ∣ ((jacPS f x).mulVec (x' - x)) i := by
      intro i
      have ht := taylor_first_order (f i) x (x' - x)
      rw [add_sub_cancel, hfx' i, hfx i, sub_zero, zero_sub] at ht
      have h2 := dvd_sq_of_mem_quadIdeal (fun j => hd j) ht
      rw [← pow_mul] at h2
      rw [mulVec_eq_sum]
      have h3 : (PowerSeries.X : K⟦X⟧) ^ (m * 2) ∣ ∑ j, eval x (pderiv j (f i)) * (x' - x) j :=
        (dvd_neg.1 h2)
      exact h3
    have hinv : x' - x = (jacPS f x)⁻¹.mulVec ((jacPS f x).mulVec (x' - x)) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_jacPS hJ hx),
        Matrix.one_mulVec]
    have h4 : (PowerSeries.X : K⟦X⟧) ^ (m * 2) ∣ (x' - x) j := by
      rw [hinv, mulVec_eq_sum]
      exact Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hJv k) _
    exact Dvd.dvd.trans (pow_dvd_pow _ (by omega)) h4
  have hall : ∀ m, ∀ j, (PowerSeries.X : K⟦X⟧) ^ (m + 1) ∣ x' j - x j := by
    intro m
    induction m with
    | zero =>
      intro j
      rw [pow_one, PowerSeries.X_dvd_iff, map_sub, hx' j, hx j, sub_self]
    | succ m ih => exact key (m + 1) (by omega) ih
  funext j
  rw [← sub_eq_zero, ← neg_sub, neg_eq_zero]
  apply PowerSeries.ext
  intro k
  rw [map_zero]
  exact (PowerSeries.X_pow_dvd_iff.1 (hall k j)) k (by omega)

/--
Multivariate Hensel lemma: if f(x₀)=0 modulo X and the residue Jacobian
determinant is nonzero, there is a unique x:ι→K[[X]] with residue x₀ and f(x)=0.
-/
theorem hensel_lift (f : ι → MvPolynomial ι K⟦X⟧) (x₀ : ι → K)
    (h0 : ∀ i, PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (f i)) = 0)
    (hJ : (Matrix.of fun i j =>
      PowerSeries.constantCoeff (eval (fun j => PowerSeries.C (x₀ j)) (pderiv j (f i)))).det ≠ 0) :
    ∃! x : ι → K⟦X⟧, (∀ j, PowerSeries.constantCoeff (x j) = x₀ j) ∧ ∀ i, eval x (f i) = 0 := by
  have hJ' : (jacRes f x₀).det ≠ 0 := hJ
  refine ⟨newtonLimit f x₀, ⟨newtonLimit_reduces, eval_newtonLimit hJ' h0⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  exact hensel_unique hJ' hy1 newtonLimit_reduces hy2 (eval_newtonLimit hJ' h0)

end BPFixedPoints.BP
