import BPFixedPoints.Incidence.CechCubicalCellProduct

/-! # The original cell augmentation, base vertex and recursive prism

The original component projection sums degree-zero vertex coefficients and
kills every cell with an overlap. The homotopy is the specified tensor prism.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1400000
variable (R : Type*) [CommRing R]

/-- Every original endpoint augments to one; the original overlap edge augments to zero. -/
theorem interval_p_single (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).p (single k r) = if k = 2 then 0 else single 0 r := by
  fin_cases k <;> simp [interval]

/-- The component inclusion is the originally specified base endpoint. -/
theorem interval_i_single (b : Fin 2) (k : Fin 1) (r : R) :
    (interval R b).i (single k r) = single b.castSucc r := by
  fin_cases k
  simp [interval]

/-- A uniform coefficient for the specified interval prism. -/
def prismCoefficient (b : Fin 2) (k : Fin 3) : R :=
  if b = 0 then (if k = 1 then -1 else 0) else (if k = 0 then 1 else 0)

/-- The original interval prism changes only the differing endpoint. -/
theorem interval_h_single (b : Fin 2) (k : Fin 3) (r : R) :
    (interval R b).h (single k r) = single 2 (prismCoefficient R b k*r) := by
  fin_cases b <;> fin_cases k <;> simp [interval,prismCoefficient]

/-- The original projected parity replaces each endpoint by the basepoint and kills overlaps. -/
theorem interval_projection_sign_single (b : Fin 2) (k : Fin 3) (r : R) :
    ((interval R b).projection * (interval R b).sign) (single k r) =
      if k = 2 then 0 else single b.castSucc r := by
  fin_cases k <;> simp [GradedContraction.projection,interval]

/-- The empty original component retains its original coefficient. -/
theorem empty_p_single (p : Fin 0 → Fin 3) (r : R) :
    (empty R).p (single p r) = single (fun _ => 0) r := by
  change mapDomain (Equiv.ofUnique _ _) (single p r) = _
  rw [mapDomain_single]
  congr 1
  exact Subsingleton.elim _ _

/-- The specified original augmentation kills exactly the positive-dimensional cell generators. -/
theorem finContraction_p_single (n : ℕ) (b : Fin n → Fin 2) (p : Fin n → Fin 3) (r : R) :
    (finContraction R n b).p (single p r) =
      if ∃ v, p v = 2 then 0 else single (fun _ => 0) r := by
  induction n with
  | zero => simpa [finContraction] using empty_p_single R p r
  | succ n ih =>
    rw [finContraction,GradedContraction.congr_p_apply,consEquiv_symm_single]
    change consEquiv R (fun _ => Fin 1)
      (TensorProduct.map (interval R (b 0)).p (finContraction R n (Fin.tail b)).p
        (single (p 0) 1 ⊗ₜ[R] single (Fin.tail p) r)) = _
    rw [TensorProduct.map_tmul,interval_p_single,ih]
    by_cases h₀ : p 0 = 2
    · rw [ite_eq_left h₀,TensorProduct.zero_tmul,map_zero,ite_eq_left ⟨0,h₀⟩]
    · by_cases ht : ∃ v, (Fin.tail p) v = 2
      · have he : ∃ v, p v = 2 := by obtain ⟨v,hv⟩ := ht; exact ⟨v.succ,hv⟩
        rw [ite_eq_right h₀,ite_eq_left ht,TensorProduct.tmul_zero,map_zero,ite_eq_left he]
      · simp only [h₀,ite_false,ht,consEquiv_single_tmul_single,one_mul]
        rw [if_neg (by simpa only [Fin.exists_fin_succ,Fin.tail] using not_or.mpr ⟨h₀,ht⟩)]
        congr 1
        exact Subsingleton.elim _ _

/-- The original component augmentation is independent of the endpoint used for the prism. -/
theorem finContraction_p_eq (n : ℕ) (b c : Fin n → Fin 2) :
    (finContraction R n b).p = (finContraction R n c).p := by
  apply Finsupp.lhom_ext
  intro p r
  rw [finContraction_p_single,finContraction_p_single]

/-- Relabelling retains the independence of the original augmentation from the base vertex. -/
theorem contraction_p_eq {V : Type*} [Fintype V] (b c : V → Fin 2) :
    (contraction R b).p = (contraction R c).p := by
  apply LinearMap.ext
  intro x
  let e := (Fintype.equivFin V).symm
  change (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 1))))
    ((finContraction R (Fintype.card V) (fun i => b (e i))).p _) =
      (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl (Fin 1))))
        ((finContraction R (Fintype.card V) (fun i => c (e i))).p _)
  rw [finContraction_p_eq R _ (fun i => b (e i)) (fun i => c (e i))]

/-- The component inclusion is exactly the original specified base vertex. -/
theorem finContraction_i_single (n : ℕ) (b : Fin n → Fin 2) (p : Fin n → Fin 1) (r : R) :
    (finContraction R n b).i (single p r) = single (fun v => (b v).castSucc) r := by
  induction n with
  | zero =>
    change mapDomain (Equiv.ofUnique _ _).symm (single p r) = _
    rw [mapDomain_single]
    congr 1
    exact Subsingleton.elim _ _
  | succ n ih =>
    rw [finContraction,GradedContraction.congr_i_apply,consEquiv_symm_single]
    change consEquiv R (fun _ => Fin 3)
      (TensorProduct.map (interval R (b 0)).i (finContraction R n (Fin.tail b)).i
        (single (p 0) 1 ⊗ₜ[R] single (Fin.tail p) r)) = _
    rw [TensorProduct.map_tmul,interval_i_single,ih,consEquiv_single_tmul_single,one_mul]
    congr 1
    funext v
    refine Fin.cases ?_ (fun j => ?_) v <;> rfl

/-- The labelled component inclusion retains exactly the originally specified base vertex. -/
theorem contraction_i_single {V : Type*} [Fintype V]
    (b : V → Fin 2) (p : V → Fin 1) (r : R) :
    (contraction R b).i (single p r) = single (fun v => (b v).castSucc) r := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  let eh := e.arrowCongr (Equiv.refl (Fin 1))
  change (Finsupp.mapDomain.linearEquiv R R ep)
    ((finContraction R (Fintype.card V) (fun i => b (e i))).i
      ((Finsupp.mapDomain.linearEquiv R R eh).symm (single p r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain ep ((finContraction R (Fintype.card V) (fun i => b (e i))).i
    (mapDomain eh.symm (single p r))) = _
  rw [mapDomain_single,finContraction_i_single,mapDomain_single]
  congr 1
  funext v
  simp [ep]

/-- The original tensor-coordinate insertion retains every tail cell and coefficient. -/
theorem consEquiv_single_tmul {n : ℕ} (k : Fin 3) (r : R) (x : Cells R (Fin n)) :
    consEquiv R (fun _ : Fin (n+1) => Fin 3) (single k r ⊗ₜ[R] x) =
      mapDomain (Fin.cons k) (r • x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [TensorProduct.tmul_add,map_add,hx,hy,smul_add,Finsupp.mapDomain_add]
  | single p s =>
    simp only [consEquiv_single_tmul_single,Finsupp.smul_single,smul_eq_mul,mapDomain_single]

/-- The specified tensor prism on a generator, without changing any cell or tensor enumeration. -/
theorem finContraction_h_single (n : ℕ) (b : Fin (n+1) → Fin 2)
    (p : Fin (n+1) → Fin 3) (r : R) :
    (finContraction R (n+1) b).h (single p r) =
      single (Fin.cons 2 (Fin.tail p)) (prismCoefficient R (b 0) (p 0)*r) +
        (if p 0 = 2 then 0 else
          mapDomain (Fin.cons (b 0).castSucc) ((finContraction R n (Fin.tail b)).h (single (Fin.tail p) r))) := by
  rw [finContraction,GradedContraction.congr_h_apply,consEquiv_symm_single]
  change consEquiv R (fun _ => Fin 3)
    (TensorProduct.map (interval R (b 0)).h (1 : Module.End R (Cells R (Fin n)))
        (single (p 0) 1 ⊗ₜ[R] single (Fin.tail p) r) +
      TensorProduct.map ((interval R (b 0)).projection * (interval R (b 0)).sign)
        (finContraction R n (Fin.tail b)).h (single (p 0) 1 ⊗ₜ[R] single (Fin.tail p) r)) = _
  rw [TensorProduct.map_tmul,TensorProduct.map_tmul,Module.End.one_apply,interval_h_single,
    interval_projection_sign_single,map_add,consEquiv_single_tmul_single,mul_one]
  by_cases hp : p 0 = 2
  · simp [hp]
  · rw [if_neg hp,if_neg hp,consEquiv_single_tmul,one_smul]

end BPFixedPoints.CechCubicalCell
