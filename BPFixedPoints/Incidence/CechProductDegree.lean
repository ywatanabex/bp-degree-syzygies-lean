import BPFixedPoints.Incidence.CechProductSign
import BPFixedPoints.Incidence.ResolutionHomogeneous

/-!
# Integer grading of the product Čech contraction

The differential raises Čech degree by one and the homotopy lowers it by one.
Inclusion and projection preserve each state's unique cohomological degree.
-/

namespace BPFixedPoints.CechProduct

open Finsupp ResolutionTools
open scoped TensorProduct

variable (R : Type*) [CommRing R]

def lineCohomologyDegree (d : ℕ) : ℕ := if d = 0 then 0 else 1

def cohomologyDegree {V : Type*} [Fintype V] (d : V → ℕ) : ℕ :=
  ∑ v, lineCohomologyDegree (d v)

@[simp] theorem cohomologyDegree_cons {n : ℕ} (d : Fin (n + 1) → ℕ) :
    cohomologyDegree d = lineCohomologyDegree (d 0) + cohomologyDegree (Fin.tail d) := by
  simp [cohomologyDegree, Fin.sum_univ_succ, Fin.tail]

theorem cohomologyDegree_eq_card {V : Type*} [Fintype V] (d : V → ℕ) :
    cohomologyDegree d = (Finset.univ.filter fun v => 0 < d v).card := by
  classical
  simp only [cohomologyDegree, lineCohomologyDegree, Finset.card_eq_sum_ones,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  split_ifs <;> omega

@[simp] theorem lineBasisEquiv_symm_left_apply (x : LineC R) (k : ℕ) :
    (lineBasisEquiv R).symm x (Sum.inl k) = x.1.1 k := rfl

@[simp] theorem lineBasisEquiv_symm_right_apply (x : LineC R) (k : ℕ) :
    (lineBasisEquiv R).symm x (Sum.inr (Sum.inl k)) = x.1.2 k := rfl

@[simp] theorem lineBasisEquiv_symm_overlap_apply (x : LineC R) (k : ℤ) :
    (lineBasisEquiv R).symm x (Sum.inr (Sum.inr k)) = x.2 k := rfl

theorem lineBasisEquiv_symm_zero_degree (x : CechLine.C0 R) :
    (lineBasisEquiv R).symm (x, 0) ∈
      supported R R {b | (lineDegree b : ℤ) = 0} := by
  apply (mem_supported' R _).mpr
  rintro (k | k | k) hk
  · exact (hk rfl).elim
  · exact (hk rfl).elim
  · simp

theorem lineBasisEquiv_symm_one_degree (x : CechLine.C1 R) :
    (lineBasisEquiv R).symm (0, x) ∈
      supported R R {b | (lineDegree b : ℤ) = 1} := by
  apply (mem_supported' R _).mpr
  rintro (k | k | k) hk
  · simp
  · simp
  · exact (hk rfl).elim

theorem lineFree_d_degree (d : ℕ) :
    HasDegree (fun b => (lineDegree b : ℤ)) (fun b => (lineDegree b : ℤ)) 1
      (lineFree R d).d := by
  apply HasDegree.of_single
  rintro (k | k | k) r
  · rw [lineFree_d_left]
    exact Submodule.neg_mem _ (single_mem_supported R r rfl)
  · rw [lineFree_d_right]
    exact single_mem_supported R r rfl
  · rw [lineFree_d_overlap]
    exact Submodule.zero_mem _

theorem lineFree_h_degree (d : ℕ) :
    HasDegree (fun b => (lineDegree b : ℤ)) (fun b => (lineDegree b : ℤ)) (-1)
      (lineFree R d).h := by
  apply HasDegree.of_single
  rintro (k | k | k) r
  · have hz : (lineFree R d).h (single (Sum.inl k) r) = 0 := by
      apply (lineBasisEquiv R).injective
      simp [lineFree, line, lineH]
    rw [hz]
    exact Submodule.zero_mem _
  · have hz : (lineFree R d).h (single (Sum.inr (Sum.inl k)) r) = 0 := by
      apply (lineBasisEquiv R).injective
      simp [lineFree, line, lineH]
    rw [hz]
    exact Submodule.zero_mem _
  · change (lineBasisEquiv R).symm
        (lineH R d (lineBasisEquiv R (single (Sum.inr (Sum.inr k)) r))) ∈ _
    rw [lineBasisEquiv_overlap, lineH_apply]
    exact lineBasisEquiv_symm_zero_degree R _

theorem lineFree_i_mem_degree (d : ℕ) (x : Fin (phi d) →₀ R) :
    (lineFree R d).i x ∈
      supported R R {b | (lineDegree b : ℤ) = (lineCohomologyDegree d : ℤ)} := by
  change (lineBasisEquiv R).symm (lineI R d ((lineHBasisEquiv R d).symm x)) ∈ _
  rw [lineI_apply]
  by_cases hd : d = 0
  · subst d
    have hz : ((lineHBasisEquiv R 0).symm x).2 = 0 := by
      ext j
      exact Fin.elim0 j
    rw [hz, map_zero]
    exact lineBasisEquiv_symm_zero_degree R _
  · have hz : ((lineHBasisEquiv R d).symm x).1 = 0 := by
      have : IsEmpty (CechLine.H0Index d) := by
        dsimp [CechLine.H0Index]
        rw [ite_eq_right hd]
        infer_instance
      exact Subsingleton.elim _ _
    rw [hz, map_zero]
    simpa only [lineCohomologyDegree, ite_eq_right hd, Nat.cast_one] using
      lineBasisEquiv_symm_one_degree R (CechLine.inclusionOne R d
        ((lineHBasisEquiv R d).symm x).2)

theorem lineFree_i_degree (d : ℕ) :
    HasDegree (fun _ : Fin (phi d) => (lineCohomologyDegree d : ℤ))
      (fun b => (lineDegree b : ℤ)) 0 (lineFree R d).i := by
  apply HasDegree.of_single
  intro a r
  simpa only [add_zero] using lineFree_i_mem_degree R d (single a r)

theorem lineFree_p_degree (d : ℕ) :
    HasDegree (fun b => (lineDegree b : ℤ))
      (fun _ : Fin (phi d) => (lineCohomologyDegree d : ℤ)) 0
      (lineFree R d).p := by
  apply HasDegree.of_single
  intro a r
  by_cases hdeg : (lineDegree a : ℤ) = (lineCohomologyDegree d : ℤ)
  · exact (mem_supported' R _).mpr fun b hb => (hb (by simp [hdeg])).elim
  · have hz : (lineFree R d).p (single a r) = 0 := by
      change lineHBasisEquiv R d (lineP R d (lineBasisEquiv R (single a r))) = 0
      by_cases hd : d = 0
      · subst d
        rcases a with k | k | k
        · exact (hdeg rfl).elim
        · exact (hdeg rfl).elim
        · have hz : CechLine.projectionOne R 0 (single k r) = 0 := by
            ext j
            exact Fin.elim0 j
          rw [lineBasisEquiv_overlap, lineP_apply]
          change lineHBasisEquiv R 0
            (CechLine.projectionZero R 0 (0 : CechLine.C0 R),
              CechLine.projectionOne R 0 (single k r)) = 0
          rw [map_zero, hz]
          exact (lineHBasisEquiv R 0).map_zero
      · have hz : CechLine.projectionZero R d = 0 := by
          simp [CechLine.projectionZero, hd]
        rcases a with k | k | k
        · simp only [lineBasisEquiv_left, lineP_apply, hz, LinearMap.zero_apply, map_zero]
          exact map_zero _
        · simp only [lineBasisEquiv_right, lineP_apply, hz, LinearMap.zero_apply, map_zero]
          exact map_zero _
        · exact (hdeg (by simp [lineDegree, lineCohomologyDegree, hd])).elim
    rw [hz]
    exact Submodule.zero_mem _

theorem lineFree_sign_degree (d : ℕ) :
    HasDegree (fun b => (lineDegree b : ℤ)) (fun b => (lineDegree b : ℤ)) 0
      (lineFree R d).sign := by
  apply HasDegree.of_single
  intro a r
  rw [lineFree_sign_single]
  exact Submodule.smul_mem _ _ (single_mem_supported R r (by simp))

/-- Degrees of the four strong-contraction maps and the parity action. -/
structure ContractionDegrees {A B : Type*}
    (c : GradedContraction R (A →₀ R) (B →₀ R)) (da : A → ℤ) (db : B → ℤ) : Prop where
  d : HasDegree da da 1 c.d
  h : HasDegree da da (-1) c.h
  i : HasDegree db da 0 c.i
  p : HasDegree da db 0 c.p
  sign : HasDegree da da 0 c.sign

theorem lineFree_degrees (d : ℕ) :
    ContractionDegrees R (lineFree R d) (fun b => (lineDegree b : ℤ))
      (fun _ => (lineCohomologyDegree d : ℤ)) :=
  ⟨lineFree_d_degree R d, lineFree_h_degree R d, lineFree_i_degree R d,
    lineFree_p_degree R d, lineFree_sign_degree R d⟩

section TensorAccessors

variable {R} {C H D K : Type*} [AddCommGroup C] [Module R C]
  [AddCommGroup H] [Module R H] [AddCommGroup D] [Module R D]
  [AddCommGroup K] [Module R K]
  (c : GradedContraction R C H) (e : GradedContraction R D K)

theorem tensor_d_apply (x : C ⊗[R] D) :
    (c.tensor e).d x = TensorProduct.map c.d 1 x + TensorProduct.map c.sign e.d x := rfl

theorem tensor_h_apply (x : C ⊗[R] D) :
    (c.tensor e).h x = TensorProduct.map c.h 1 x +
      TensorProduct.map (c.projection * c.sign) e.h x := rfl

theorem tensor_i_apply (x : H ⊗[R] K) :
    (c.tensor e).i x = TensorProduct.map c.i e.i x := rfl

theorem tensor_p_apply (x : C ⊗[R] D) :
    (c.tensor e).p x = TensorProduct.map c.p e.p x := rfl

theorem tensor_sign_apply (x : C ⊗[R] D) :
    (c.tensor e).sign x = TensorProduct.map c.sign e.sign x := rfl

end TensorAccessors

namespace ContractionDegrees

variable {R} {A B C D A' B' : Type*}
  {c : GradedContraction R (A →₀ R) (B →₀ R)}
  {e : GradedContraction R (C →₀ R) (D →₀ R)}
  {da : A → ℤ} {db : B → ℤ} {dc : C → ℤ} {dd : D → ℤ}

theorem congr (hc : ContractionDegrees R c da db)
    (eA : A ≃ A') (eB : B ≃ B') (da' : A' → ℤ) (db' : B' → ℤ)
    (hA : ∀ a, da' (eA a) = da a) (hB : ∀ b, db' (eB b) = db b) :
    ContractionDegrees R
      (c.congr (Finsupp.mapDomain.linearEquiv R R eA)
        (Finsupp.mapDomain.linearEquiv R R eB)) da' db' where
  d := hc.d.congr_mapDomain eA eA da' da' hA hA
  h := hc.h.congr_mapDomain eA eA da' da' hA hA
  i := hc.i.congr_mapDomain eB eA db' da' hB hA
  p := hc.p.congr_mapDomain eA eB da' db' hA hB
  sign := hc.sign.congr_mapDomain eA eA da' da' hA hA

theorem tensor_congr (hc : ContractionDegrees R c da db)
    (he : ContractionDegrees R e dc dd)
    (eA : A × C ≃ A') (eB : B × D ≃ B') (da' : A' → ℤ) (db' : B' → ℤ)
    (hA : ∀ a, da' (eA a) = da a.1 + dc a.2)
    (hB : ∀ b, db' (eB b) = db b.1 + dd b.2) :
    ContractionDegrees R
      ((c.tensor e).congr
        ((finsuppTensorFinsupp' R A C).trans (Finsupp.mapDomain.linearEquiv R R eA))
        ((finsuppTensorFinsupp' R B D).trans (Finsupp.mapDomain.linearEquiv R R eB)))
      da' db' := by
  let EC := (finsuppTensorFinsupp' R A C).trans (Finsupp.mapDomain.linearEquiv R R eA)
  let EH := (finsuppTensorFinsupp' R B D).trans (Finsupp.mapDomain.linearEquiv R R eB)
  constructor
  · intro n x hx
    rw [GradedContraction.congr_d_apply, tensor_d_apply, map_add]
    have h₁ := (hc.d.tensor_congr (HasDegree.id dc) eA eA da' da' hA hA) n x hx
    have h₂ := (hc.sign.tensor_congr he.d eA eA da' da' hA hA) n x hx
    exact Submodule.add_mem _ h₁ h₂
  · intro n x hx
    rw [GradedContraction.congr_h_apply, tensor_h_apply, map_add]
    have hps : HasDegree da da 0 (c.projection * c.sign) := by
      simpa only [zero_add, GradedContraction.projection, Module.End.mul_eq_comp] using
        (hc.i.comp hc.p).comp hc.sign
    have h₁ := (hc.h.tensor_congr (HasDegree.id dc) eA eA da' da' hA hA) n x hx
    have h₂ := (hps.tensor_congr he.h eA eA da' da' hA hA) n x hx
    exact Submodule.add_mem _ h₁ h₂
  · intro n x hx
    rw [GradedContraction.congr_i_apply, tensor_i_apply]
    exact (hc.i.tensor_congr he.i eB eA db' da' hB hA) n x hx
  · intro n x hx
    rw [GradedContraction.congr_p_apply, tensor_p_apply]
    exact (hc.p.tensor_congr he.p eA eB da' db' hA hB) n x hx
  · intro n x hx
    rw [GradedContraction.congr_sign_apply, tensor_sign_apply]
    exact (hc.sign.tensor_congr he.sign eA eA da' da' hA hA) n x hx

end ContractionDegrees

theorem finProduct_degrees (n : ℕ) (d : Fin n → ℕ) :
    ContractionDegrees R (finProduct R n d)
      (fun b => (cechDegree b : ℤ)) (fun _ => (cohomologyDegree d : ℤ)) := by
  induction n with
  | zero =>
    constructor
    · exact HasDegree.zero _ _ _
    · exact HasDegree.zero _ _ _
    · simpa only [finProduct, cechDegree, cohomologyDegree, Fin.sum_univ_zero, Nat.cast_zero] using
        HasDegree.constant (empty R d).i 0
    · simpa only [finProduct, cechDegree, cohomologyDegree, Fin.sum_univ_zero, Nat.cast_zero] using
        HasDegree.constant (empty R d).p 0
    · exact HasDegree.id _
  | succ n ih =>
    rw [finProduct]
    exact (lineFree_degrees R (d 0)).tensor_congr (ih (Fin.tail d))
      (Fin.consEquiv fun _ : Fin (n + 1) => Basis)
      (Fin.consEquiv fun i => Fin (phi (d i)))
      (fun b => (cechDegree b : ℤ)) (fun _ => (cohomologyDegree d : ℤ))
      (fun ⟨a, b⟩ => by
        change (cechDegree (Fin.cons a b) : ℤ) = _
        rw [cechDegree_cons, Nat.cast_add])
      (fun _ => by rw [cohomologyDegree_cons, Nat.cast_add])

theorem contraction_degrees {V : Type*} [Fintype V] (d : V → ℕ) :
    ContractionDegrees R (contraction R d)
      (fun b => (cechDegree b : ℤ)) (fun _ => (cohomologyDegree d : ℤ)) := by
  classical
  let e := (Fintype.equivFin V).symm
  exact (finProduct_degrees R (Fintype.card V) (fun i => d (e i))).congr
    (e.arrowCongr (Equiv.refl Basis))
    (Equiv.piCongrLeft (fun v => Fin (phi (d v))) e)
    (fun b => (cechDegree b : ℤ)) (fun _ => (cohomologyDegree d : ℤ))
    (fun b => congrArg (fun n : ℕ => (n : ℤ)) (cechDegree_arrowCongr e b))
    (fun _ => congrArg (fun n : ℕ => (n : ℤ))
      (show cohomologyDegree d = cohomologyDegree (fun i => d (e i)) from
        (e.sum_comp (fun v => lineCohomologyDegree (d v))).symm))

theorem contraction_d_degree {V : Type*} [Fintype V] (d : V → ℕ) :
    HasDegree (fun b => (cechDegree b : ℤ)) (fun b => (cechDegree b : ℤ)) 1
      (contraction R d).d := (contraction_degrees R d).d

theorem contraction_h_degree {V : Type*} [Fintype V] (d : V → ℕ) :
    HasDegree (fun b => (cechDegree b : ℤ)) (fun b => (cechDegree b : ℤ)) (-1)
      (contraction R d).h := (contraction_degrees R d).h

theorem contraction_i_degree {V : Type*} [Fintype V] (d : V → ℕ) :
    HasDegree (fun _ => (cohomologyDegree d : ℤ)) (fun b => (cechDegree b : ℤ)) 0
      (contraction R d).i := (contraction_degrees R d).i

theorem contraction_p_degree {V : Type*} [Fintype V] (d : V → ℕ) :
    HasDegree (fun b => (cechDegree b : ℤ)) (fun _ => (cohomologyDegree d : ℤ)) 0
      (contraction R d).p := (contraction_degrees R d).p

theorem cechDegree_le_card {V : Type*} [Fintype V] (b : V → Basis) :
    cechDegree b ≤ Fintype.card V := by
  calc
    cechDegree b ≤ ∑ _ : V, (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro v hv
      rcases b v with k | k | k <;> simp [lineDegree]
    _ = Fintype.card V := by simp

end BPFixedPoints.CechProduct
