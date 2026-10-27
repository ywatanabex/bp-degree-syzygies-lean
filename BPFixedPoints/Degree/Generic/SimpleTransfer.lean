import BPFixedPoints.Degree.AuxPolySystem
import BPFixedPoints.Degree.Jacobian
import BPFixedPoints.Degree.AuxSystem

/-!
# Transferring simplicity from auxiliary to BP coordinates

For an admissible BP solution y and auxiliary coordinates (A,F)=(X/a,total field),
let w lie in the BP Jacobian kernel. Set u_γ=w_γ/y_γ,
S_α=Σ_{γ∈in(t(α))∖ᾱ}u_γ and T_i=Σ_{γ∈in(i)}u_γ.
Then v=(A_α S_α,F_i T_i) lies in the auxiliary Jacobian kernel: edge rows are
−A_α S_α f_ᾱ(y)−A_α δf_ᾱ(w), and vertex rows vanish by (5).
Auxiliary invertibility gives v=0, hence S=T=0, u=T−S=0 and w=0.
Thus the BP Jacobian is invertible (`isSimpleSolution_of_isSimpleAuxSolution`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP MvPolynomial

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

theorem mulVec_apply' {ι R : Type*} [Fintype ι] [CommRing R] (M : Matrix ι ι R) (w : ι → R)
    (i : ι) : M.mulVec w i = ∑ j, M i j * w j := by
  simp [Matrix.mulVec, dotProduct]

/-! ### Directional derivatives -/

section DirDeriv

variable {K : Type*} [Field K]

/-- Directional derivative of an auxiliary edge equation: Σ_j ∂_j E_α(x)v_j. -/
theorem auxEdgePoly_dirDeriv {R : Type*} [CommRing R] (s : E → R) (α : Dart E)
    (x v : Var V E → R) :
    ∑ j, eval x (pderiv j (G.auxEdgePoly s α)) * v j =
      v (Sum.inl α) * (1 + s α.1 * x (Sum.inl (rev α))) +
        x (Sum.inl α) * (s α.1 * v (Sum.inl (rev α))) -
        v (Sum.inr (G.tail α)) * (1 + x (Sum.inl (rev α))) -
        x (Sum.inr (G.tail α)) * v (Sum.inl (rev α)) := by
  have hd : ∀ j, eval x (pderiv j (G.auxEdgePoly s α)) =
      (if Sum.inl α = j then 1 else 0) * (1 + s α.1 * x (Sum.inl (rev α))) +
        x (Sum.inl α) * (s α.1 * (if Sum.inl (rev α) = j then 1 else 0)) -
        (if Sum.inr (G.tail α) = j then 1 else 0) * (1 + x (Sum.inl (rev α))) -
        x (Sum.inr (G.tail α)) * (if Sum.inl (rev α) = j then 1 else 0) := by
    intro j
    simp only [auxEdgePoly, map_sub, map_add, pderiv_mul, pderiv_X, pderiv_C, Pi.single_apply,
      Derivation.map_one_eq_zero, map_one, map_zero, eval_add, eval_sub, eval_mul, eval_X, eval_C]
    simp only [apply_ite (eval x), map_one, map_zero]
    ring
  simp only [hd, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

variable (b : V → K) (y : Dart E → K)

/-- Cavity-field derivative in relative coordinates: Σ_γ ∂_γ X_α(y)w_γ=X_α Σ_{γ∈in(t(α))∖ᾱ}w_γ/y_γ. -/
theorem cavity_dirDeriv (hy : ∀ γ, y γ ≠ 0) (α : Dart E) (w : Dart E → K) :
    ∑ γ, eval y (pderiv γ (G.cavityPoly b α)) * w γ =
      G.cavity b y α * ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), w γ / y γ := by
  set s := (G.inDarts (G.tail α)).erase (rev α) with hs
  have hd : ∀ j, eval y (pderiv j (G.cavityPoly b α)) =
      b (G.tail α) * ∑ γ ∈ s.filter (fun γ => γ = j), ∏ δ ∈ s.erase γ, y δ := by
    intro j
    have hP := eval_pderiv_prod_X s (fun γ => γ) y j
    simp only [cavityPoly, pderiv_mul, pderiv_C, zero_mul, zero_add, eval_mul, eval_C]
    rw [← hs, hP]
  simp only [hd]
  calc ∑ j, b (G.tail α) * (∑ γ ∈ s.filter (fun γ => γ = j), ∏ δ ∈ s.erase γ, y δ) * w j
      = ∑ j, ∑ γ ∈ s.filter (fun γ => γ = j),
          b (G.tail α) * (∏ δ ∈ s.erase γ, y δ) * w γ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [(Finset.mem_filter.1 hγ).2]
    _ = ∑ γ ∈ s, b (G.tail α) * (∏ δ ∈ s.erase γ, y δ) * w γ :=
        Finset.sum_fiberwise s (fun γ => γ) _
    _ = G.cavity b y α * ∑ γ ∈ s, w γ / y γ := by
        unfold cavity
        rw [← hs, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro γ hγ
        rw [← Finset.mul_prod_erase s y hγ]
        field_simp
        rw [mul_div_cancel_right₀ _ (hy γ)]

/-- BP polynomial derivative: Σ_γ ∂_γ f_α(y)w_γ=w_α(X_α+a)+(y_α−a)δX_α. -/
theorem bpMvPoly_dirDeriv (a : E → K) (α : Dart E) (w : Dart E → K) :
    ∑ γ, eval y (pderiv γ (G.bpMvPoly a b α)) * w γ =
      w α * (G.cavity b y α + a α.1) +
        (y α - a α.1) * ∑ γ, eval y (pderiv γ (G.cavityPoly b α)) * w γ := by
  have hd : ∀ j, eval y (pderiv j (G.bpMvPoly a b α)) =
      (if α = j then 1 else 0) * (G.cavity b y α + a α.1) +
        (y α - a α.1) * eval y (pderiv j (G.cavityPoly b α)) := by
    intro j
    simp only [bpMvPoly, map_sub, map_add, pderiv_mul, pderiv_X, pderiv_C, Pi.single_apply,
      Derivation.map_one_eq_zero, eval_add, eval_sub, eval_mul, eval_X, eval_C, eval_cavityPoly,
      map_zero, map_one]
    simp only [apply_ite (eval y), map_one, map_zero]
    ring
  simp only [hd, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

end DirDeriv

/-! ### Kernel transfer -/

section Main

variable {K : Type*} [Field K] (a : E → K) (b : V → K) (y : Dart E → K)

/-- The BP Jacobian has zero kernel if the auxiliary Jacobian is invertible. -/
theorem jacobian_mulVec_eq_zero (hG : G.Loopless) (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hy : G.IsAdmissibleSolution a b y)
    (hs : G.IsSimpleAuxSolution (fun e => a e ^ 2) (G.auxBeta a b) (G.auxA a b y)
      (G.totalField b y))
    (w : Dart E → K) (hw : (G.jacobian a b y).mulVec w = 0) : w = 0 := by
  have hy0 : ∀ γ, y γ ≠ 0 := hy.2.1
  set A : Dart E → K := G.auxA a b y with hAdef
  set F : V → K := G.totalField b y with hFdef
  have hA0 : ∀ α, A α ≠ 0 := G.auxA_ne_zero a b y ha hb hy0
  have hF0 : ∀ i, F i ≠ 0 := G.totalField_ne_zero b y hb hy0
  have hcav : ∀ α, G.cavity b y α = a α.1 * A α := by
    intro α
    simp only [hAdef, auxA]
    rw [mul_div_cancel₀ _ (ha _)]
  have hFt : ∀ α, F (G.tail α) = a α.1 * A α * y (rev α) := by
    intro α
    rw [hFdef, G.totalField_tail_eq b y α, hcav]
  -- Relative perturbations.
  set u : Dart E → K := fun γ => w γ / y γ with hudef
  set S : Dart E → K := fun α => ∑ γ ∈ (G.inDarts (G.tail α)).erase (rev α), u γ with hSdef
  set T : V → K := fun i => ∑ γ ∈ G.inDarts i, u γ with hTdef
  have hST : ∀ α, T (G.tail α) = u (rev α) + S α := fun α =>
    (Finset.add_sum_erase _ _ (G.rev_mem_inDarts α)).symm
  have hwu : ∀ γ, w γ = u γ * y γ := by
    intro γ
    simp only [hudef]
    rw [div_mul_cancel₀ _ (hy0 γ)]
  -- BP equations and their linearizations.
  have hf : ∀ α, y α * (a α.1 * A α + a α.1) - (a α.1 * (a α.1 * A α) + 1) = 0 := by
    intro α
    have h := hy.1 α
    unfold bpPoly at h
    rwa [hcav] at h
  have hδf : ∀ α, u α * y α * (a α.1 * A α + a α.1) +
      (y α - a α.1) * (a α.1 * A α * S α) = 0 := by
    intro α
    have h1 := congrFun hw α
    rw [mulVec_apply', Pi.zero_apply] at h1
    have h2 : ∑ j, G.jacobian a b y α j * w j =
        ∑ j, eval y (pderiv j (G.bpMvPoly a b α)) * w j := rfl
    rw [h2, G.bpMvPoly_dirDeriv b y a α w, G.cavity_dirDeriv b y hy0 α w, hcav, hwu α] at h1
    exact h1
  -- Auxiliary-system perturbations.
  set v : Var V E → K := Sum.elim (fun α => A α * S α) (fun i => F i * T i) with hvdef
  have haux := G.isAuxSolution_of_admissible hG a b y ha hb hy
  have hsol := (G.isAuxSolution_iff (fun e => a e ^ 2) (G.auxBeta a b) (Sum.elim A F)).2 haux
  have hv : (G.auxJacobian (fun e => a e ^ 2) (G.auxBeta a b) (Sum.elim A F)).mulVec v = 0 := by
    funext j
    rw [mulVec_apply', Pi.zero_apply]
    cases j with
    | inl α =>
      have h := G.auxEdgePoly_dirDeriv (fun e => a e ^ 2) α (Sum.elim A F) v
      simp only [auxJacobian, Matrix.of_apply, auxSystem]
      rw [h, hvdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [hFt, hST]
      have e1 := hf (rev α)
      have e2 := hδf (rev α)
      have hr : (rev α).1 = α.1 := rfl
      rw [hr] at e1 e2
      linear_combination (-(A α * S α)) * e1 + (-(A α)) * e2
    | inr i =>
      have h := G.vertexPoly_dirDeriv (G.auxBeta a b) i (Sum.elim A F) v
      simp only [auxJacobian, Matrix.of_apply, auxSystem]
      rw [h, hvdef]
      simp only [Sum.elim_inl, Sum.elim_inr]
      set Pr : K := ∏ α ∈ G.inDarts i, A (rev α) with hPrdef
      have hvert : F i * Pr - G.auxBeta a b i * F i ^ G.degree i = 0 := by
        have := hsol.1 (Sum.inr i)
        rw [auxSystem, eval_vertexPoly] at this
        simpa only [Sum.elim_inl, Sum.elim_inr] using this
      have hsum : ∑ α ∈ G.inDarts i, A (rev α) * S (rev α) *
          ∏ δ ∈ (G.inDarts i).erase α, A (rev δ) = Pr * ((G.degree i : K) * T i - T i) := by
        have hterm : ∀ α ∈ G.inDarts i, A (rev α) * S (rev α) *
            ∏ δ ∈ (G.inDarts i).erase α, A (rev δ) = Pr * (T i - u α) := by
          intro α hα
          have hmem : G.head α = i := (Finset.mem_filter.1 hα).2
          have hSα : S (rev α) = T i - u α := by
            simp only [hSdef, hTdef, tail_rev, rev_rev, hmem]
            exact Finset.sum_erase_eq_sub hα
          rw [hSα, mul_right_comm, Finset.mul_prod_erase _ (fun δ => A (rev δ)) hα]
        rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_const, nsmul_eq_mul]
        rfl
      rw [hsum]
      obtain hd0 | hdpos := Nat.eq_zero_or_pos (G.degree i)
      · have hT0 : T i = 0 := by
          simp only [hTdef]
          rw [Finset.card_eq_zero.1 hd0, Finset.sum_empty]
        rw [hT0]
        ring
      · obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hdpos.ne'
        rw [hm] at hvert ⊢
        have hβ : G.auxBeta a b i * F i ^ m = Pr := by
          simp only [Nat.succ_eq_add_one, pow_succ] at hvert
          have h' : (G.auxBeta a b i * F i ^ m) * F i = Pr * F i := by
            linear_combination -hvert
          exact mul_right_cancel₀ (hF0 i) h'
        simp only [Nat.succ_sub_one, Nat.cast_succ]
        push_cast
        linear_combination (-(F i * T i * ((m : K) + 1))) * hβ
  -- The auxiliary Jacobian is injective.
  have hu : IsUnit (G.auxJacobian (fun e => a e ^ 2) (G.auxBeta a b) (Sum.elim A F)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hs)
  have hinj := Matrix.mulVec_injective_iff_isUnit.2 hu
  have hv0 : v = 0 := hinj (by rw [hv, Matrix.mulVec_zero])
  have hS0 : ∀ α, S α = 0 := by
    intro α
    have := congrFun hv0 (Sum.inl α)
    rw [hvdef] at this
    simp only [Sum.elim_inl, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left (hA0 α)
  have hT0 : ∀ i, T i = 0 := by
    intro i
    have := congrFun hv0 (Sum.inr i)
    rw [hvdef] at this
    simp only [Sum.elim_inr, Pi.zero_apply, mul_eq_zero] at this
    exact this.resolve_left (hF0 i)
  have hu0 : ∀ γ, u γ = 0 := by
    intro γ
    have h := hST (rev γ)
    rw [rev_rev, hT0, hS0, add_zero] at h
    exact h.symm
  funext γ
  rw [hwu γ, hu0 γ, zero_mul, Pi.zero_apply]

/-- **Simplicity transfers from auxiliary to BP coordinates.** If the auxiliary Jacobian at (A,F) corresponding to an admissible BP solution y is invertible, so is the BP Jacobian. -/
theorem isSimpleSolution_of_isSimpleAuxSolution (hG : G.Loopless) (ha : ∀ e, a e ≠ 0)
    (hb : ∀ i, b i ≠ 0) (hy : G.IsAdmissibleSolution a b y)
    (hs : G.IsSimpleAuxSolution (fun e => a e ^ 2) (G.auxBeta a b) (G.auxA a b y)
      (G.totalField b y)) :
    G.IsSimpleSolution a b y := by
  have hinj : Function.Injective (G.jacobian a b y).mulVec := by
    intro w w' hww'
    have h0 : (G.jacobian a b y).mulVec (w - w') = 0 := by
      rw [Matrix.mulVec_sub, hww', sub_self]
    exact sub_eq_zero.1 (G.jacobian_mulVec_eq_zero a b y hG ha hb hy hs (w - w') h0)
  have hu := Matrix.mulVec_injective_iff_isUnit.1 hinj
  rw [Matrix.isUnit_iff_isUnit_det] at hu
  exact hu.ne_zero

end Main

end Multigraph

end BPFixedPoints
