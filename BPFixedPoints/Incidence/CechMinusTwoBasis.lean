import BPFixedPoints.Incidence.CechTwoTopState

/-! # Original Laurent gap representatives for the all-minus-two state -/

namespace BPFixedPoints.CechProduct
open Finsupp
open scoped TensorProduct
variable (R : Type) [CommRing R]
set_option maxHeartbeats 200000

/-- The original one-factor twist-minus-two state has exactly one basis index. -/
theorem phi_two : phi 2 = 1 := rfl

/-- The original unique one-factor state index for twist minus two. -/
abbrev gapZero : Fin (phi 2) := ⟨0, by decide⟩

/-- The original one-factor inclusion uses the Laurent monomial of exponent minus one. -/
theorem lineFree_two_i_single (r : R) :
    (lineFree R 2).i (single gapZero r) =
      single (Sum.inr (Sum.inr (-1 : ℤ))) r := by
  apply (lineBasisEquiv R).injective
  rw [lineBasisEquiv_overlap]
  rw [lineFree, GradedContraction.congr_i_apply, LinearEquiv.apply_symm_apply]
  change lineI R 2 ((lineHBasisEquiv R 2).symm (single gapZero r)) = _
  have hh : (lineHBasisEquiv R 2).symm (single gapZero r) =
      (0,single (0 : CechLine.H1Index 2) r) := by
    apply (lineHBasisEquiv R 2).injective
    rw [LinearEquiv.apply_symm_apply]
    change single gapZero r = mapDomain _ ((0 : Fin 0 →₀ R).sumElim (single (0 : Fin 1) r))
    rw [sumElim_zero_single,mapDomain_single]
    rfl
  rw [hh,lineI_apply,CechLine.inclusionOne_single]
  rfl

/-- The original ordered tensor inclusion retains the product Laurent gap monomial. -/
theorem finProduct_two_i_single (n : ℕ) (r : R) :
    (finProduct R n (fun _ => 2)).i (single (fun _ => gapZero) r) =
      single (fun _ => Sum.inr (Sum.inr (-1 : ℤ))) r := by
  induction n with
  | zero =>
    change mapDomain _ (single _ r) = _
    rw [mapDomain_single]
    congr 1
    funext v
    exact Fin.elim0 v
  | succ n ih =>
    rw [finProduct, GradedContraction.congr_i_apply, consEquiv_symm_single]
    change consEquiv R (fun _ => Basis)
      (TensorProduct.map (lineFree R 2).i (finProduct R n (fun _ => 2)).i
        (single gapZero 1 ⊗ₜ[R] single (fun _ => gapZero) r)) = _
    rw [TensorProduct.map_tmul,lineFree_two_i_single,ih,consEquiv_single_tmul_single,one_mul]
    congr 1
    funext v
    exact Fin.cases rfl (fun _ => rfl) v

/-- The original finite enumeration retains the same constant gap exponent in every coordinate. -/
theorem contraction_two_i_single {V : Type} [Fintype V] (r : R) :
    (contraction R (fun _ : V => 2)).i (single (fun _ => gapZero) r) =
      single (fun _ => Sum.inr (Sum.inr (-1 : ℤ))) r := by
  classical
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  let eh := Equiv.piCongrLeft (fun _ : V => Fin (phi 2)) e
  change mapDomain eb
    ((finProduct R (Fintype.card V) (fun _ => 2)).i
      (mapDomain eh.symm (single (fun _ => gapZero) r))) = _
  rw [mapDomain_single]
  have hh : eh.symm (fun _ => gapZero) = fun _ => gapZero := by rfl
  rw [hh,finProduct_two_i_single,mapDomain_single]
  rfl

/-- The two original overlap coordinates both have Laurent exponent minus one. -/
def twoGapExponent : FaceMonoid twoTopFace := by
  refine Fin.cons (show FaceExponent (twoTopFace 0) from (-1 : ℤ)) ?_
  refine Fin.cons (show FaceExponent (twoTopFace 1) from (-1 : ℤ)) ?_
  exact fun i => Fin.elim0 i

/-- The specified coefficient monomial is the original two-factor gap monomial. -/
theorem embedFace_twoGapExponent :
    embedFace twoTopFace twoGapExponent = fun _ => Sum.inr (Sum.inr (-1 : ℤ)) := by
  funext v
  fin_cases v <;> rfl

/-- The original projection sends every scalar multiple of the gap monomial to its original state. -/
theorem twoTopStateProjection_gap (r : R) :
    twoTopStateProjection R (fun _ => 2) (AddMonoidAlgebra.single twoGapExponent r) =
      single (fun _ => gapZero) r := by
  have hf : faceEquiv R (single (fun _ : Fin 2 => Sum.inr (Sum.inr (-1 : ℤ))) r) twoTopFace =
      AddMonoidAlgebra.single twoGapExponent r := by
    rw [← embedFace_twoGapExponent,faceEquiv_single_same]
  rw [← hf,twoTopStateProjection_top R (fun _ => 2) (by intro v; decide),
    ← contraction_two_i_single R r]
  exact LinearMap.congr_fun (contraction R (fun _ : Fin 2 => 2)).p_i _

end BPFixedPoints.CechProduct
