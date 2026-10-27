import BPFixedPoints.Incidence.CechCubicalCellDiagonal

/-! # Original coefficients of the finite cubical diagonal

The allowed face pairs and each Koszul sign are specified independently.
The actual tensor diagonal has exactly these original coefficients.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp GradedContraction CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1500000
variable (R : Type*) [CommRing R]

/-- Original pairs in the interval Alexander--Whitney diagonal. -/
def intervalDiagonalShape (s p q : Fin 3) : Prop :=
  if s = 0 then p = 0 ∧ q = 0 else if s = 1 then p = 1 ∧ q = 1
  else (p = 0 ∧ q = 2) ∨ (p = 2 ∧ q = 1)

/-- Original allowed face pairs, coordinate by coordinate. -/
def DiagonalShape {V : Type*} (s p q : V → Fin 3) : Prop :=
  ∀ v, intervalDiagonalShape (s v) (p v) (q v)

noncomputable instance {V : Type*} [Fintype V] (s p q : V → Fin 3) : Decidable (DiagonalShape s p q) := by
  classical
  unfold DiagonalShape intervalDiagonalShape
  infer_instance

/-- The crossing of each right head edge with the left tail, in the original order. -/
def finDiagonalCross : (n : ℕ) → (Fin n → Fin 3) → (Fin n → Fin 3) → ℕ
  | 0, _, _ => 0
  | n+1, p, q => faceDegree (Fin.tail p)*(if q 0 = 2 then 1 else 0) +
      finDiagonalCross n (Fin.tail p) (Fin.tail q)

/-- The original tensor pair coordinates. -/
noncomputable abbrev pairCoordinates (V : Type*) :
    (Cells R V ⊗[R] Cells R V) ≃ₗ[R] ((V → Fin 3) × (V → Fin 3)) →₀ R :=
  finsuppTensorFinsupp' R _ _

private theorem consCoefficient {n : ℕ} (k i : Fin 3) (p : Fin n → Fin 3) (x : Cells R (Fin n)) :
    consEquiv R (fun _ : Fin (n+1) => Fin 3) (single k 1 ⊗ₜ[R] x) (Fin.cons i p) =
      if k = i then x p else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,Finsupp.add_apply,hx,hy]; split_ifs <;> simp
  | single q r =>
    rw [consEquiv_single_tmul_single,one_mul]
    by_cases h : k = i
    · subst i
      simp [Finsupp.single_apply,Fin.cons_inj]
    · simp [Finsupp.single_apply,Fin.cons_inj,h]

/-- Original parity at a cell reads precisely the original overlap count. -/
theorem finContraction_sign_coefficient (n : ℕ) (b : Fin n → Fin 2) (x : Cells R (Fin n)) (p : Fin n → Fin 3) :
    (finContraction R n b).sign x p = (-1 : R)^faceDegree p*x p := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy,mul_add]
  | single q r =>
    rw [finContraction_sign_single]
    by_cases h : q = p
    · subst q
      simp
    · simp [Finsupp.single_apply,h]

/-- Head coefficient including the crossing parity of the original left tail. -/
noncomputable def headDiagonalWeight (k i j : Fin 3) (n : ℕ) : R :=
  if k = 0 then (if i = 0 ∧ j = 0 then 1 else 0)
  else if k = 1 then (if i = 1 ∧ j = 1 then 1 else 0)
  else (if i = 0 ∧ j = 2 then (-1 : R)^n else 0) + (if i = 2 ∧ j = 1 then 1 else 0)

private theorem headDiagonal_coefficient (n : ℕ) (k i j : Fin 3)
    (p q : Fin n → Fin 3) (z : Cells R (Fin n) ⊗[R] Cells R (Fin n)) :
    pairCoordinates R (Fin (n+1))
      (TensorProduct.map (consEquiv R (fun _ : Fin (n+1) => Fin 3)).toLinearMap
        (consEquiv R (fun _ : Fin (n+1) => Fin 3)).toLinearMap
          (headDiagonalTerm (finContraction R n (fun _ => 0)) k z)) (Fin.cons i p,Fin.cons j q) =
      headDiagonalWeight R k i j (faceDegree p) * pairCoordinates R (Fin n) z (p,q) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy,mul_add]
  | tmul x y =>
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [headDiagonalTerm,headDiagonalWeight,TensorProduct.map_tmul,headCell,
        pairCoordinates,finsuppTensorFinsupp'_apply_apply,consCoefficient,finContraction_sign_coefficient] <;> ring

@[simp] theorem diagonalShape_cons {n : ℕ} (k i j : Fin 3) (s p q : Fin n → Fin 3) :
    DiagonalShape (Fin.cons k s) (Fin.cons i p) (Fin.cons j q) ↔
      intervalDiagonalShape k i j ∧ DiagonalShape s p q := by
  simp [DiagonalShape,Fin.forall_fin_succ]

/-- Every coefficient of the specified original diagonal, including the full Koszul crossing sign. -/
theorem finDiagonal_coefficient (n : ℕ) (s p q : Fin n → Fin 3) (r : R) :
    pairCoordinates R (Fin n) ((finDiagonal R n).map (single s r)) (p,q) =
      if DiagonalShape s p q then (-1 : R)^finDiagonalCross n p q*r else 0 := by
  classical
  induction n with
  | zero =>
    have hp : p = s := Subsingleton.elim _ _
    have hq : q = s := Subsingleton.elim _ _
    subst p; subst q
    simp [finDiagonal,emptyDiagonal_single,pairCoordinates,Finsupp.single_apply,DiagonalShape,finDiagonalCross]
  | succ n ih =>
    rw [← Fin.cons_self_tail s,finDiagonal_single_cons,← Fin.cons_self_tail p,← Fin.cons_self_tail q,
      headDiagonal_coefficient,ih]
    simp only [diagonalShape_cons]
    simp only [finDiagonalCross,Fin.tail_cons,Fin.cons_zero]
    generalize s 0 = k
    generalize p 0 = i
    generalize q 0 = j
    fin_cases k <;> fin_cases i <;> fin_cases j <;>
      simp [headDiagonalWeight,intervalDiagonalShape,pow_add,mul_assoc]

/-- The full crossing count in the original fixed labelled enumeration. -/
noncomputable def diagonalCross {V : Type*} [Fintype V] (p q : V → Fin 3) : ℕ :=
  finDiagonalCross (Fintype.card V) (p ∘ (Fintype.equivFin V).symm) (q ∘ (Fintype.equivFin V).symm)

private theorem pairCoordinates_reindex {A B : Type*} (e : A ≃ B)
    (z : (A →₀ R) ⊗[R] (A →₀ R)) (p q : A) :
    finsuppTensorFinsupp' R B B
      (TensorProduct.map (Finsupp.mapDomain.linearEquiv R R e).toLinearMap
        (Finsupp.mapDomain.linearEquiv R R e).toLinearMap z) (e p,e q) =
      finsuppTensorFinsupp' R A A z (p,q) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]
  | tmul x y =>
    simp only [TensorProduct.map_tmul,finsuppTensorFinsupp'_apply_apply]
    change mapDomain e x (e p)*mapDomain e y (e q) = x p*y q
    simp only [Finsupp.mapDomain_apply_of_injective e.injective]

/-- Relabelling retains exactly the original coordinatewise interval face pairs. -/
theorem diagonalShape_reindex {A B : Type*} (e : A ≃ B) (s p q : A → Fin 3) :
    DiagonalShape (e.arrowCongr (Equiv.refl (Fin 3)) s)
      (e.arrowCongr (Equiv.refl (Fin 3)) p) (e.arrowCongr (Equiv.refl (Fin 3)) q) ↔ DiagonalShape s p q := by
  constructor
  · intro h v
    simpa using h (e v)
  · intro h v
    exact h (e.symm v)

/-- Every original labelled coefficient, with its original finite-enumeration Koszul sign. -/
theorem diagonal_coefficient {V : Type*} [Fintype V] (s p q : V → Fin 3) (r : R) :
    pairCoordinates R V ((diagonal R V).map (single s r)) (p,q) =
      if DiagonalShape s p q then (-1 : R)^diagonalCross p q*r else 0 := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  rw [diagonal,Diagonal.congr_map,Finsupp.mapDomain.linearEquiv_symm]
  change finsuppTensorFinsupp' R _ _
    (TensorProduct.map (Finsupp.mapDomain.linearEquiv R R ep).toLinearMap
      (Finsupp.mapDomain.linearEquiv R R ep).toLinearMap
        ((finDiagonal R (Fintype.card V)).map (mapDomain ep.symm (single s r)))) (p,q) = _
  rw [mapDomain_single]
  have h := pairCoordinates_reindex R ep
    ((finDiagonal R (Fintype.card V)).map (single (ep.symm s) r)) (ep.symm p) (ep.symm q)
  rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at h
  rw [h,finDiagonal_coefficient]
  have hs : DiagonalShape (ep.symm s) (ep.symm p) (ep.symm q) ↔ DiagonalShape s p q :=
    diagonalShape_reindex e.symm s p q
  simp only [hs]
  rfl

end BPFixedPoints.CechCubicalCell
