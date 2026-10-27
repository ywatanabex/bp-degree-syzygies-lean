import BPFixedPoints.Incidence.CechLineProjectionCoefficients

/-! # Original finite-tensor state projections read original mixed monomial coefficients -/

namespace BPFixedPoints.CechProduct
open Finsupp
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R]

/-- Read the original factor monomial prescribed by each original state coordinate. -/
def stateProjectionMonomial {V : Type} (d : V → ℕ) (κ : HBasis d) : V → Basis :=
  fun v => lineProjectionMonomial (d v) (κ v)

/-- The original finite tensor coordinate map evaluates by the product of the original coefficients. -/
theorem consEquiv_tmul_coefficient {n : ℕ} (B : Fin (n+1) → Type)
    (x : B 0 →₀ R) (y : ((i : Fin n) → B i.succ) →₀ R) (b : (i : Fin (n+1)) → B i) :
    consEquiv R B (x ⊗ₜ[R] y) b = x (b 0) * y (Fin.tail b) := by
  change mapDomain (Fin.consEquiv B) (finsuppTensorFinsupp' R _ _ (x ⊗ₜ[R] y)) b = _
  rw [mapDomain_equiv_apply]
  exact finsuppTensorFinsupp'_apply_apply R _ _ x y (b 0) (Fin.tail b)

/-- The original ordered tensor projection reads precisely the original mixed state monomial. -/
theorem finProduct_p_coefficient (n : ℕ) (d : Fin n → ℕ) (x : C R (Fin n)) (κ : HBasis d) :
    (finProduct R n d).p x κ = x (stateProjectionMonomial d κ) := by
  induction n with
  | zero =>
    change mapDomain (Equiv.ofUnique (Fin 0 → Basis) (HBasis d)) x κ = _
    rw [mapDomain_equiv_apply]
    congr 1
    funext v
    exact Fin.elim0 v
  | succ n ih =>
    induction x using Finsupp.induction_linear with
    | zero => rw [map_zero]; rfl
    | add x y hx hy => rw [map_add,Finsupp.add_apply,hx,hy]; rfl
    | single b r =>
      rw [finProduct,GradedContraction.congr_p_apply,consEquiv_symm_single]
      change consEquiv R (fun i => Fin (phi (d i)))
        (TensorProduct.map (lineFree R (d 0)).p (finProduct R n (Fin.tail d)).p
          (single (b 0) 1 ⊗ₜ[R] single (Fin.tail b) r)) κ = _
      rw [TensorProduct.map_tmul,consEquiv_tmul_coefficient,lineFree_p_coefficient]
      have he : consEquiv R (fun _ : Fin (n+1) => Basis)
          (single (b 0) 1 ⊗ₜ[R] single (Fin.tail b) r) = single b r := by
        rw [consEquiv_single_tmul_single,one_mul]
        congr 1
        funext v
        exact Fin.cases rfl (fun _ => rfl) v
      calc
        _ = (single (b 0) (1 : R)) (lineProjectionMonomial (d 0) (κ 0)) *
            (single (Fin.tail b) r) (stateProjectionMonomial (Fin.tail d) (Fin.tail κ)) :=
          congrArg (fun z : R => (single (b 0) (1 : R)) (lineProjectionMonomial (d 0) (κ 0)) * z)
            (ih (Fin.tail d) (single (Fin.tail b) r) (Fin.tail κ))
        _ = consEquiv R (fun _ : Fin (n+1) => Basis)
            (single (b 0) 1 ⊗ₜ[R] single (Fin.tail b) r) (stateProjectionMonomial d κ) :=
          (consEquiv_tmul_coefficient R (fun _ : Fin (n+1) => Basis)
            (single (b 0) 1) (single (Fin.tail b) r) (stateProjectionMonomial d κ)).symm
        _ = _ := congrArg (fun f : C R (Fin (n+1)) => f (stateProjectionMonomial d κ)) he

/-- The original projection for any finite vertex enumeration reads its original mixed monomial coefficient. -/
theorem contraction_p_coefficient {V : Type} [Fintype V] (d : V → ℕ) (x : C R V) (κ : HBasis d) :
    (contraction R d).p x κ = x (stateProjectionMonomial d κ) := by
  classical
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  let eh := Equiv.piCongrLeft (fun v => Fin (phi (d v))) e
  change mapDomain eh ((finProduct R (Fintype.card V) (fun i => d (e i))).p (mapDomain eb.symm x)) κ = _
  rw [mapDomain_equiv_apply,finProduct_p_coefficient,mapDomain_equiv_apply]
  congr 1
  funext v
  simp [eb,eh,stateProjectionMonomial]
  rw [e.apply_symm_apply]

end BPFixedPoints.CechProduct
