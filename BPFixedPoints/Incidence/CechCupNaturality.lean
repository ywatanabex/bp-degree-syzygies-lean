import BPFixedPoints.Incidence.CechCupBasis

/-! # Full Čech chain product and homogeneous monomial actions -/

namespace BPFixedPoints.CechProduct

open Finsupp

theorem lineCupBasis_shift_left (e a b : ℕ) (x y : Basis) :
    lineCupBasis e (shift a b x) y = (lineCupBasis e x y).map (shift a b) := by
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    simp [lineCupBasis, shift, add_assoc, add_comm, add_left_comm]

theorem lineCupBasis_shift_right (e a b : ℕ) (h : a + b ≤ e) (x y : Basis) :
    lineCupBasis (e - (a + b)) x (shift a b y) =
      (lineCupBasis e x y).map (shift a b) := by
  rcases x with x | x | x <;> rcases y with y | y | y <;>
    simp [lineCupBasis, shift, add_assoc, add_comm, add_left_comm]
  omega

theorem finCupBasis_shift_left (n : ℕ) (e a b : Fin n → ℕ) (x y : Fin n → Basis) :
    finCupBasis n e (fun v => shift (a v) (b v) (x v)) y =
      (finCupBasis n e x y).map (fun z v => shift (a v) (b v) (z v)) := by
  induction n with
  | zero => simp only [finCupBasis, Option.map_some, Option.some.injEq]; exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [finCupBasis, lineCupBasis_shift_left]
    rw [show Fin.tail (fun v => shift (a v) (b v) (x v)) =
      (fun v => shift (Fin.tail a v) (Fin.tail b v) (Fin.tail x v)) from rfl, ih]
    cases h₁ : lineCupBasis (e 0) (x 0) (y 0) <;>
      cases h₂ : finCupBasis n (Fin.tail e) (Fin.tail x) (Fin.tail y) <;>
      simp
    funext v
    refine Fin.cases ?_ (fun j => ?_) v <;> rfl

theorem finCupBasis_shift_right (n : ℕ) (e a b : Fin n → ℕ)
    (h : ∀ v, a v + b v ≤ e v) (x y : Fin n → Basis) :
    finCupBasis n (fun v => e v - (a v + b v)) x
        (fun v => shift (a v) (b v) (y v)) =
      (finCupBasis n e x y).map (fun z v => shift (a v) (b v) (z v)) := by
  induction n with
  | zero => simp only [finCupBasis, Option.map_some, Option.some.injEq]; exact Subsingleton.elim _ _
  | succ n ih =>
    simp only [finCupBasis, lineCupBasis_shift_right _ _ _ (h 0)]
    rw [show Fin.tail (fun v => shift (a v) (b v) (y v)) =
      (fun v => shift (Fin.tail a v) (Fin.tail b v) (Fin.tail y v)) from rfl,
      show Fin.tail (fun v => e v - (a v + b v)) =
        (fun v => Fin.tail e v - (Fin.tail a v + Fin.tail b v)) from rfl,
      ih (Fin.tail e) (Fin.tail a) (Fin.tail b) (fun v => h v.succ)]
    cases h₁ : lineCupBasis (e 0) (x 0) (y 0) <;>
      cases h₂ : finCupBasis n (Fin.tail e) (Fin.tail x) (Fin.tail y) <;>
      simp
    funext v
    refine Fin.cases ?_ (fun j => ?_) v <;> rfl

theorem finCupCross_shift_left (n : ℕ) (a b : Fin n → ℕ) (x y : Fin n → Basis) :
    finCupCross n (fun v => shift (a v) (b v) (x v)) y = finCupCross n x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cechDegree (fun v : Fin n => shift (a v.succ) (b v.succ) (x v.succ)) *
      lineDegree (y 0) + finCupCross n (fun v => shift (a v.succ) (b v.succ) (x v.succ))
        (Fin.tail y) = _
    rw [cechDegree_shift, ih]
    rfl

theorem finCupCross_shift_right (n : ℕ) (a b : Fin n → ℕ) (x y : Fin n → Basis) :
    finCupCross n x (fun v => shift (a v) (b v) (y v)) = finCupCross n x y := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change cechDegree (Fin.tail x) * lineDegree (shift (a 0) (b 0) (y 0)) +
      finCupCross n (Fin.tail x) (fun v => shift (a v.succ) (b v.succ) (y v.succ)) = _
    rw [lineDegree_shift, ih]
    rfl

variable (R : Type*) [CommRing R]

theorem finChainPairing_multiply_left (n : ℕ) (d d' e a b : Fin n → ℕ)
    (x y : C R (Fin n)) :
    (finChainPairing R n d' e).mul (multiply R a b x) y =
      multiply R a b ((finChainPairing R n d e).mul x y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single x r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single y s =>
      rw [multiply_single, finChainPairing_mul_single, finChainPairing_mul_single,
        finCupBasis_shift_left, finCupCross_shift_left]
      cases finCupBasis n e x y <;>
        simp only [Option.map_none, Option.map_some, Option.elim, map_zero, multiply_single]

theorem finChainPairing_multiply_right (n : ℕ) (d e a b : Fin n → ℕ)
    (h : ∀ v, a v + b v ≤ e v) (x y : C R (Fin n)) :
    (finChainPairing R n d (fun v => e v - (a v + b v))).mul x (multiply R a b y) =
      multiply R a b ((finChainPairing R n d e).mul x y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single x r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single y s =>
      rw [multiply_single, finChainPairing_mul_single, finChainPairing_mul_single,
        finCupBasis_shift_right _ _ _ _ h, finCupCross_shift_right]
      cases finCupBasis n e x y <;>
        simp only [Option.map_none, Option.map_some, Option.elim, map_zero, multiply_single]

section Reindex

variable {V : Type*} [Fintype V]

noncomputable def vertexReindex : C R (Fin (Fintype.card V)) ≃ₗ[R] C R V :=
  Finsupp.mapDomain.linearEquiv R R
    ((Fintype.equivFin V).symm.arrowCongr (Equiv.refl Basis))

theorem chainCup_reindex (d e : V → ℕ) (x y : C R (Fin (Fintype.card V))) :
    chainCup R d e (vertexReindex R x) (vertexReindex R y) =
      vertexReindex R ((finChainPairing R (Fintype.card V)
        (d ∘ (Fintype.equivFin V).symm) (e ∘ (Fintype.equivFin V).symm)).mul x y) := by
  unfold chainCup chainPairing
  rw [GradedContraction.ChainPairing.congr_mul_apply]
  simp only [vertexReindex, LinearEquiv.symm_apply_apply]
  rfl

theorem multiply_vertexReindex (a b : V → ℕ) (x : C R (Fin (Fintype.card V))) :
    multiply R a b (vertexReindex R x) = vertexReindex R
      (multiply R (a ∘ (Fintype.equivFin V).symm) (b ∘ (Fintype.equivFin V).symm) x) :=
  LinearMap.congr_fun (multiply_reindex R (Fintype.equivFin V).symm a b) x

theorem chainCup_multiply_left (d d' e a b : V → ℕ) (x y : C R V) :
    chainCup R d' e (multiply R a b x) y = multiply R a b (chainCup R d e x y) := by
  obtain ⟨x, rfl⟩ := (vertexReindex R (V := V)).surjective x
  obtain ⟨y, rfl⟩ := (vertexReindex R (V := V)).surjective y
  rw [multiply_vertexReindex, chainCup_reindex, chainCup_reindex,
    finChainPairing_multiply_left, multiply_vertexReindex]

theorem chainCup_multiply_right (d e a b : V → ℕ) (h : ∀ v, a v + b v ≤ e v)
    (x y : C R V) :
    chainCup R d (fun v => e v - (a v + b v)) x (multiply R a b y) =
      multiply R a b (chainCup R d e x y) := by
  obtain ⟨x, rfl⟩ := (vertexReindex R (V := V)).surjective x
  obtain ⟨y, rfl⟩ := (vertexReindex R (V := V)).surjective y
  rw [multiply_vertexReindex, chainCup_reindex, chainCup_reindex,
    multiply_vertexReindex]
  congr 1
  exact finChainPairing_multiply_right R _ _ _ _ _
    (fun v => h ((Fintype.equivFin V).symm v)) x y

theorem chainCup_twist_left (d d' e : V → ℕ) (x y : C R V) :
    chainCup R d' e x y = chainCup R d e x y := by
  simpa only [multiply_zero, LinearMap.id_apply] using
    chainCup_multiply_left R d d' e 0 0 x y

theorem contraction_sign_twist (d e : V → ℕ) :
    (contraction R d).sign = (contraction R e).sign := by
  apply Finsupp.lhom_ext
  intro b r
  rw [contraction_sign_single, contraction_sign_single]

end Reindex
end BPFixedPoints.CechProduct
