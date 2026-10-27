import BPFixedPoints.Incidence.CechPolynomialBoundary
import BPFixedPoints.Incidence.CechFaceDegree

/-! # Identify the Čech degree-zero component with chart-section families -/

namespace BPFixedPoints.CechProduct

open Finsupp

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem chartFace_injective : Function.Injective (chartFace (V := V)) := by
  intro σ τ h
  funext v
  have he := congrFun h v
  cases hs : σ v <;> cases ht : τ v <;> simp_all [chartFace]

@[simp] theorem faceDegree_chartFace (σ : V → Bool) : faceDegree (chartFace σ) = 0 := by
  simp [faceDegree]

theorem faceDegree_eq_zero_iff (q : V → Fin 3) :
    faceDegree q = 0 ↔ ∃ σ : V → Bool, q = chartFace σ := by
  constructor
  · intro hq
    have hn : ∀ v, q v ≠ 2 := by
      intro v hv
      have hh : (if q v = 2 then 1 else 0) ≤ faceDegree q := by
        change (if q v = 2 then 1 else 0) ≤ ∑ w, (if q w = 2 then 1 else 0)
        exact Finset.single_le_sum (f := fun w : V => if q w = 2 then (1 : ℕ) else 0)
          (fun w _ => Nat.zero_le _) (Finset.mem_univ v)
      simp [hv, hq] at hh
    refine ⟨fun v => decide (q v = 1), ?_⟩
    funext v
    have hf (a : Fin 3) (ha : a ≠ 2) : a = (if decide (a = 1) then 1 else 0) := by
      fin_cases a <;> simp_all
    exact hf (q v) (hn v)
  · rintro ⟨σ, rfl⟩
    exact faceDegree_chartFace σ

@[simp] theorem faceDegree_overlapFace (σ : V → Bool) (v : V) :
    faceDegree (overlapFace σ v) = 1 := by
  unfold faceDegree
  simp only [overlapFace_eq_two_iff]
  simp

theorem faceDegree_eq_one_iff (q : V → Fin 3) :
    faceDegree q = 1 ↔ ∃ (σ : V → Bool) (v : V), q = overlapFace σ v := by
  constructor
  · intro hq
    have hcard : (Finset.univ.filter fun v => q v = 2).card = 1 := by
      simpa only [faceDegree, Finset.card_filter] using hq
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
    have htwo (w : V) : q w = 2 ↔ w = v := by
      have he := congrArg (fun s : Finset V => w ∈ s) hv
      simpa using he
    refine ⟨fun w => decide (q w = 1), v, ?_⟩
    funext w
    by_cases hw : w = v
    · subst w
      rw [(htwo v).mpr rfl, overlapFace_self]
    · rw [overlapFace_ne _ v w hw]
      have hn : q w ≠ 2 := fun hh => hw ((htwo w).mp hh)
      have hf (a : Fin 3) (ha : a ≠ 2) : a = (if decide (a = 1) then 1 else 0) := by
        fin_cases a <;> simp_all
      exact hf (q w) hn
  · rintro ⟨σ, v, rfl⟩
    exact faceDegree_overlapFace σ v

variable (R : Type*) [CommRing R]

@[simp] theorem faceEquiv_zeroCharts_chart (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (σ : V → Bool) : faceEquiv R (zeroCharts R x) (chartFace σ) = x σ := by
  classical
  rw [zeroCharts_apply, map_sum, Finset.sum_apply, Finset.sum_eq_single σ]
  · simp [faceEquiv_chartInsert]
  · intro τ _ hτ
    rw [faceEquiv_chartInsert]
    apply Pi.single_eq_of_ne
    intro hh
    exact hτ (chartFace_injective hh.symm)
  · simp

theorem faceEquiv_zeroCharts_nonchart
    (x : (σ : V → Bool) → FaceRing R (chartFace σ))
    (q : V → Fin 3) (hq : ∀ σ, q ≠ chartFace σ) : faceEquiv R (zeroCharts R x) q = 0 := by
  rw [zeroCharts_apply, map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro σ _
  rw [faceEquiv_chartInsert, Pi.single_eq_of_ne (hq σ)]

theorem zeroCharts_mem_supported (x : (σ : V → Bool) → FaceRing R (chartFace σ)) :
    zeroCharts R x ∈ supported R R {b | (cechDegree b : ℤ) = 0} := by
  rw [mem_supported_iff_faceEquiv]
  intro q hq
  apply faceEquiv_zeroCharts_nonchart
  intro σ hh
  apply hq
  simp [hh]

/-- A Čech degree-zero element is reconstructed from its family of chart components. -/
theorem zeroCharts_reconstruct (x : C R V)
    (hx : x ∈ supported R R {b | (cechDegree b : ℤ) = 0}) :
    zeroCharts R (fun σ => faceEquiv R x (chartFace σ)) = x := by
  apply (faceEquiv R).injective
  funext q
  by_cases hq : faceDegree q = 0
  · obtain ⟨σ, rfl⟩ := (faceDegree_eq_zero_iff q).mp hq
    exact faceEquiv_zeroCharts_chart R _ σ
  · rw [faceEquiv_zeroCharts_nonchart, faceEquiv_eq_zero_of_degree R hx q]
    · exact_mod_cast hq
    · intro σ hh
      exact hq (by simp [hh])

theorem zeroCharts_injective : Function.Injective (zeroCharts R (V := V)) := by
  intro x y h
  funext σ
  have hh := congrArg (fun z => faceEquiv R z (chartFace σ)) h
  simpa only [faceEquiv_zeroCharts_chart] using hh

variable (J : Type*)

@[simp] theorem polynomialFaceEquiv_zeroCharts_chart
    (x : (σ : V → Bool) → MvPolynomial J (FaceRing R (chartFace σ)))
    (σ : V → Bool) :
    polynomialFaceEquiv R J (polynomialZeroCharts R J x) (chartFace σ) = x σ := by
  rw [polynomialFaceEquiv_apply, polynomialZeroCharts_apply, faceEquiv_zeroCharts_chart]
  exact AlgEquiv.apply_symm_apply _ _

theorem polynomialZeroCharts_mem_supported
    (x : (σ : V → Bool) → MvPolynomial J (FaceRing R (chartFace σ))) :
    polynomialZeroCharts R J x ∈ supported (MvPolynomial J R) (MvPolynomial J R)
      {b | (cechDegree b : ℤ) = 0} :=
  zeroCharts_mem_supported (MvPolynomial J R) _

theorem polynomialZeroCharts_reconstruct (x : C (MvPolynomial J R) V)
    (hx : x ∈ supported (MvPolynomial J R) (MvPolynomial J R)
      {b | (cechDegree b : ℤ) = 0}) :
    polynomialZeroCharts R J (fun σ => polynomialFaceEquiv R J x (chartFace σ)) = x := by
  rw [polynomialZeroCharts_apply]
  simp only [polynomialFaceEquiv_apply, AlgEquiv.symm_apply_apply]
  exact zeroCharts_reconstruct (MvPolynomial J R) x hx

theorem polynomialZeroCharts_injective :
    Function.Injective (polynomialZeroCharts R J (V := V)) := by
  intro x y h
  funext σ
  have hh := congrArg (fun z => polynomialFaceEquiv R J z (chartFace σ)) h
  simpa only [polynomialFaceEquiv_zeroCharts_chart] using hh

/-- The image of the Čech differential has no component in any degree-zero chart. -/
theorem polynomialFaceEquiv_contraction_d_chart (d : V → ℕ)
    (x : C (MvPolynomial J R) V) (σ : V → Bool) :
    polynomialFaceEquiv R J ((contraction (MvPolynomial J R) d).d x) (chartFace σ) = 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]
  | single b r =>
    apply polynomialFaceEquiv_eq_zero_of_degree R J
      ((contraction_d_degree (MvPolynomial J R) d).apply_single b r)
    simp only [faceDegree_chartFace, Nat.cast_zero]
    omega

end BPFixedPoints.CechProduct
