import BPFixedPoints.Incidence.CechCubicalCellDiagonalComplex
import BPFixedPoints.Incidence.CechZeroDegrees

/-! # The specified diagonal retains the original degree-zero augmentation

Original degree-zero generators go to the same original vertex pair.
Both tensor factors then use the existing original component projection.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp GradedContraction CechProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable (R : Type*) [CommRing R] {V : Type*} [Fintype V]

/-- Original endpoint families retain their original component coefficient. -/
theorem contraction_p_vertex (s : V → Fin 3) (hs : ∀ v, s v ≠ 2) (r : R) :
    (contraction R (fun _ : V => 0)).p (single s r) = single (fun _ => 0) r := by
  classical
  let e := (Fintype.equivFin V).symm
  let ep := e.arrowCongr (Equiv.refl (Fin 3))
  let eh := e.arrowCongr (Equiv.refl (Fin 1))
  change (Finsupp.mapDomain.linearEquiv R R eh)
    ((finContraction R (Fintype.card V) (fun _ => 0)).p
      ((Finsupp.mapDomain.linearEquiv R R ep).symm (single s r))) = _
  rw [Finsupp.mapDomain.linearEquiv_symm]
  change mapDomain eh ((finContraction R (Fintype.card V) (fun _ => 0)).p
    (mapDomain ep.symm (single s r))) = _
  rw [mapDomain_single,finContraction_p_single,ite_eq_right (by
    rintro ⟨v,hv⟩
    exact hs (e v) hv),mapDomain_single]
  congr 1

/-- The original single component is repeated with its coefficient once. -/
noncomputable def componentDiagonal : Components R V →ₗ[R] Components R V ⊗[R] Components R V :=
  Finsupp.llift _ R R _ fun s => single s 1 ⊗ₜ[R] single s 1

/-- The original diagonal commutes with the original degree-zero component augmentations. -/
theorem diagonal_augmentation (x : Cells R V)
    (hx : x ∈ supported R R {s | cellDegree s = 0}) :
    TensorProduct.map (contraction R (fun _ : V => 0)).p (contraction R (fun _ : V => 0)).p
      ((diagonal R V).map x) = componentDiagonal R ((contraction R (fun _ : V => 0)).p x) := by
  classical
  rw [← x.sum_single]
  simp only [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : faceDegree s = 0 := by
    have h := hx hs
    change -(faceDegree s : ℤ) = 0 at h
    omega
  obtain ⟨σ,hσ⟩ := (faceDegree_eq_zero_iff s).mp hd
  have he : ∀ v, s v ≠ 2 := by
    rw [hσ]
    intro v
    cases hv : σ v <;> simp [chartFace,hv]
  dsimp only
  rw [diagonal_vertex R s he,TensorProduct.map_tmul,contraction_p_vertex R s he,
    contraction_p_vertex R s he]
  simp [componentDiagonal,Finsupp.llift_apply,TensorProduct.smul_tmul']
  have heq : (single (fun _ : V => (0 : Fin 1)) (x s) : Components R V) =
      (x s) • single (fun _ => 0) 1 := by simp
  rw [heq,TensorProduct.tmul_smul,← TensorProduct.smul_tmul']

end BPFixedPoints.CechCubicalCell
