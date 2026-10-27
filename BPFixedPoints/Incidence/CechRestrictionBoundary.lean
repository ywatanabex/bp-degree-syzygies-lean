import BPFixedPoints.Incidence.CechRestriction

/-! # Čech degree-zero boundary as a difference of adjacent restrictions -/

namespace BPFixedPoints.CechProduct

open Finsupp

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem overlapFace_eq_two_iff (σ : V → Bool) (v w : V) :
    overlapFace σ v w = 2 ↔ w = v := by
  by_cases hw : w = v
  · subst w; simp
  · simp [overlapFace_ne σ v w hw, chartFace_ne_two, hw]

theorem overlapFace_vertex_eq {σ τ : V → Bool} {v w : V}
    (h : overlapFace σ v = overlapFace τ w) : v = w := by
  apply (overlapFace_eq_two_iff τ w v).mp
  rw [← h, overlapFace_self]

theorem overlapFace_source_eq {σ τ : V → Bool} {v : V}
    (h : overlapFace σ v = overlapFace τ v) : σ = Function.update τ v (σ v) := by
  funext w
  by_cases hw : w = v
  · subst w; simp
  · rw [Function.update_of_ne hw]
    have he := congrFun h w
    rw [overlapFace_ne σ v w hw, overlapFace_ne τ v w hw] at he
    cases hs : σ w <;> cases ht : τ w <;> simp_all [chartFace]

theorem boundaryBasis_eq_embed (σ : V → Bool) (k : V → ℕ) (v : V) :
    boundaryBasis (fun _ => 0) σ k v =
      embedFace (overlapFace σ v) (overlapExponent σ v (σ v) k) := by
  simpa only [Function.update_eq_self] using
    (embedFace_overlapExponent σ v (σ v) k).symm

variable (R : Type*) [CommRing R]

theorem faceEquiv_d_chart_single_adjacent (σ : V → Bool) (v : V) (b : Bool)
    (k : V → ℕ) (r : R) :
    faceEquiv R
      ((contraction R (fun _ : V => 0)).d
        (single (chartBasis (Function.update σ v b) k) r)) (overlapFace σ v) =
      AddMonoidAlgebra.single (overlapExponent σ v b k) (if b then r else -r) := by
  rw [contraction_d_chart_single, map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single v]
  · rw [← embedFace_overlapExponent σ v b k, faceEquiv_single_same]
    simp
  · intro w _ hw
    rw [boundaryBasis_eq_embed]
    apply faceEquiv_single_ne
    intro he
    exact hw (overlapFace_vertex_eq he).symm
  · simp

theorem faceEquiv_d_chart_single_nonadjacent (σ τ : V → Bool) (v : V)
    (h : ∀ b, τ ≠ Function.update σ v b) (k : V → ℕ) (r : R) :
    faceEquiv R ((contraction R (fun _ : V => 0)).d (single (chartBasis τ k) r))
      (overlapFace σ v) = 0 := by
  rw [contraction_d_chart_single, map_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [boundaryBasis_eq_embed]
  apply faceEquiv_single_ne
  intro he
  have hw : v = w := overlapFace_vertex_eq he
  subst w
  exact h (τ v) (overlapFace_source_eq he.symm)

/-- Insert one degree-zero chart into the full Čech module. -/
noncomputable def chartInsert (σ : V → Bool) :
    FaceRing R (chartFace σ) →ₗ[R] C R V := by
  classical
  exact (faceEquiv R).symm.toLinearMap.comp
    (LinearMap.single R (fun q : V → Fin 3 => FaceRing R q) (chartFace σ))

@[simp] theorem faceEquiv_chartInsert (σ : V → Bool) (x : FaceRing R (chartFace σ)) :
    faceEquiv R (chartInsert R σ x) = Pi.single (chartFace σ) x := by
  simp [chartInsert]

@[simp] theorem chartInsert_single (σ : V → Bool) (k : V → ℕ) (r : R) :
    chartInsert R σ (AddMonoidAlgebra.single (chartMonoidEquiv σ k) r) =
      single (chartBasis σ k) r := by
  classical
  apply (faceEquiv R).injective
  rw [faceEquiv_chartInsert, ← embedFace_chartMonoid]
  funext q
  by_cases hq : q = chartFace σ
  · subst q
    rw [Pi.single_eq_same, faceEquiv_single_same]
  · rw [Pi.single_eq_of_ne hq, faceEquiv_single_ne R hq]

theorem faceEquiv_d_chartInsert_adjacent (σ : V → Bool) (v : V) (b : Bool)
    (x : FaceRing R (chartFace (Function.update σ v b))) :
    faceEquiv R ((contraction R (fun _ : V => 0)).d
      (chartInsert R (Function.update σ v b) x)) (overlapFace σ v) =
      if b then chartRestriction R σ v b x else -chartRestriction R σ v b x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]
    cases b <;> simp [neg_add_rev, add_comm]
  | single m r =>
    obtain ⟨k, rfl⟩ := (chartMonoidEquiv (Function.update σ v b)).surjective m
    rw [chartInsert_single, faceEquiv_d_chart_single_adjacent, chartRestriction_single]
    cases b <;> simp [AddMonoidAlgebra.single_neg]

theorem faceEquiv_d_chartInsert_nonadjacent (σ τ : V → Bool) (v : V)
    (h : ∀ b, τ ≠ Function.update σ v b) (x : FaceRing R (chartFace τ)) :
    faceEquiv R ((contraction R (fun _ : V => 0)).d (chartInsert R τ x))
      (overlapFace σ v) = 0 := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy, add_zero]
  | single m r =>
    obtain ⟨k, rfl⟩ := (chartMonoidEquiv τ).surjective m
    exact (chartInsert_single R τ k r) ▸ faceEquiv_d_chart_single_nonadjacent R σ τ v h k r

/-- Insert a family of degree-zero chart sections into the full Čech module. -/
noncomputable def zeroCharts :
    ((σ : V → Bool) → FaceRing R (chartFace σ)) →ₗ[R] C R V :=
  ∑ σ, (chartInsert R σ).comp (LinearMap.proj σ)

@[simp] theorem zeroCharts_apply (x : (σ : V → Bool) → FaceRing R (chartFace σ)) :
    zeroCharts R x = ∑ σ, chartInsert R σ (x σ) := by
  simp [zeroCharts]

theorem faceEquiv_d_zeroCharts (σ : V → Bool) (v : V)
    (x : (τ : V → Bool) → FaceRing R (chartFace τ)) :
    faceEquiv R ((contraction R (fun _ : V => 0)).d (zeroCharts R x)) (overlapFace σ v) =
      chartRestriction R σ v true (x (Function.update σ v true)) -
        chartRestriction R σ v false (x (Function.update σ v false)) := by
  classical
  rw [zeroCharts_apply, map_sum, map_sum, Finset.sum_apply]
  have hne : Function.update σ v true ≠ Function.update σ v false := by
    intro hh
    have he := congrFun hh v
    simp at he
  rw [← Finset.sum_subset (Finset.subset_univ
    ({Function.update σ v false, Function.update σ v true} : Finset (V → Bool))) ?_]
  · rw [Finset.sum_pair hne.symm, faceEquiv_d_chartInsert_adjacent,
      faceEquiv_d_chartInsert_adjacent]
    simp [sub_eq_add_neg, add_comm]
  · intro τ _ hτ
    apply faceEquiv_d_chartInsert_nonadjacent
    intro b
    cases b <;> intro he <;> simp [he] at hτ

end BPFixedPoints.CechProduct
