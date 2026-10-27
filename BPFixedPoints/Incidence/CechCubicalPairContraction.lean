import BPFixedPoints.Incidence.CechCubicalCellDiagonalComplex
import BPFixedPoints.Incidence.CechCubicalCellSubface

/-! # The original tensor cell contraction in the original pair coordinates -/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct GradedContraction
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable (R : Type*) [CommRing R] (V : Type) [Fintype V]

/-- The original tensor component coordinates; each factor is the original single component. -/
abbrev componentPairCoordinates :
    (Components R V ⊗[R] Components R V) ≃ₗ[R] ((V → Fin 1) × (V → Fin 1)) →₀ R :=
  finsuppTensorFinsupp' R _ _

/-- The original homological degree is the sum of the original two cell degrees. -/
def pairCellDegree (z : (V → Fin 3) × (V → Fin 3)) : ℤ := cellDegree z.1+cellDegree z.2

/-- The original tensor contraction retains the original full cell-pair and component-pair coordinates. -/
def pairContraction (b : V → Fin 2) :
    GradedContraction R (CellPairs R V) (((V → Fin 1) × (V → Fin 1)) →₀ R) :=
  ((contraction R b).tensor (contraction R b)).congr (pairCoordinates R V) (componentPairCoordinates R V)

private theorem mapDomain_refl (A : Type*) :
    Finsupp.mapDomain.linearEquiv R R (Equiv.refl A) = LinearEquiv.refl R (A →₀ R) := by
  ext x a
  change Finsupp.mapDomain id x a=x a
  rw [Finsupp.mapDomain_id]

/-- The existing tensor degree theorem gives precisely the original summed cell degree and degree-zero components. -/
theorem pairContraction_degrees (b : V → Fin 2) :
    ContractionDegrees R (pairContraction R V b) (pairCellDegree V) (fun _ => 0) := by
  simpa only [pairContraction,pairCoordinates,componentPairCoordinates,mapDomain_refl,LinearEquiv.trans_refl] using
    (contraction_degrees R b).tensor_congr (contraction_degrees R b)
      (Equiv.refl _) (Equiv.refl _) (pairCellDegree V) (fun _ => 0) (fun _ => rfl) (fun _ => by simp)

variable [DecidableEq V]

/-- Only the prism depends on the original tensor basepoint; its boundary is the original fixed pair boundary. -/
theorem pairContraction_d (b : V → Fin 2) : (pairContraction R V b).d=pairBoundary R V := by
  have hs : (contraction R b).sign=(contraction R (fun _ : V => 0)).sign := by
    apply Finsupp.lhom_ext
    intro p r
    rw [contraction_sign_single,contraction_sign_single]
  apply LinearMap.ext
  intro x
  simp only [pairContraction,GradedContraction.congr_d_apply,pairBoundary_apply,tensor_d_apply,
    hs,contraction_d_eq R b (fun _ => 0)]

/-- The original component projection is independent of the original tensor prism basepoint. -/
theorem pairContraction_p (b c : V → Fin 2) : (pairContraction R V b).p=(pairContraction R V c).p := by
  apply LinearMap.ext
  intro x
  simp only [pairContraction,GradedContraction.congr_p_apply,tensor_p_apply,contraction_p_eq R b c]

/-- Every original positive tensor cell cycle has its specified original tensor-prism primitive. -/
theorem pairContraction_positive_primitive (b : V → Fin 2) (n : ℕ) (hn : 0<n) (x : CellPairs R V)
    (hx : x ∈ supported R R {z | pairCellDegree V z=-(n : ℤ)}) (hd : pairBoundary R V x=0) :
    (pairContraction R V b).h x ∈ supported R R {z | pairCellDegree V z=-((n+1 : ℕ) : ℤ)} ∧
      pairBoundary R V ((pairContraction R V b).h x)=x := by
  constructor
  · have h := (pairContraction_degrees R V b).h (-(n : ℤ)) x hx
    simpa only [show -(n : ℤ)+(-1)=-((n+1 : ℕ) : ℤ) by omega] using h
  · have hp : (pairContraction R V b).p x=0 :=
      (pairContraction_degrees R V b).p.eq_zero_of_const hx (by omega)
    have hd' : (pairContraction R V b).d x=0 := by rw [pairContraction_d,hd]
    have h := LinearMap.congr_fun (pairContraction R V b).homotopy x
    rw [← pairContraction_d R V b]
    simpa only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.comp_apply,Module.End.one_apply,
      hp,hd',map_zero,add_zero] using h

end
end BPFixedPoints.CechCubicalCell
