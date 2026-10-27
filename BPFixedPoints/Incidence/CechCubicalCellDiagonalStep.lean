import BPFixedPoints.Incidence.CechCubicalCellInterval
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # The specified interval diagonal with the original tensor boundary

The original edge has diagonal left tensor edge plus edge tensor right.
The right head edge crosses the left tail with the original tail parity.
No division by two or strict commutativity of cochains is used.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp GradedContraction
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable {R D K : Type*} [CommRing R] [AddCommGroup D] [Module R D]
  [AddCommGroup K] [Module R K]

@[reducible] noncomputable local instance : AddCommGroup (Interval R ⊗[R] D) :=
  TensorProduct.addCommGroup
@[reducible] noncomputable local instance : AddCommGroup (Point R ⊗[R] K) :=
  TensorProduct.addCommGroup

/-- A specified diagonal preserving the original boundary and parity. -/
structure Diagonal (a : GradedContraction R D K) where
  map : D →ₗ[R] D ⊗[R] D
  boundary : ∀ x, (a.tensor a).d (map x) = map (a.d x)
  parity : ∀ x, (a.tensor a).sign (map x) = map (a.sign x)

variable (a : GradedContraction R D K)

/-- Insert the original head cell with coefficient one. -/
noncomputable def headCell (k : Fin 3) : D →ₗ[R] Interval R ⊗[R] D :=
  TensorProduct.mk R (Interval R) D (single k 1)

/-- The specified Alexander--Whitney summands, with the original crossing parity. -/
noncomputable def headDiagonalTerm (k : Fin 3) :
    (D ⊗[R] D) →ₗ[R] (Interval R ⊗[R] D) ⊗[R] (Interval R ⊗[R] D) :=
  if k = 0 then TensorProduct.map (headCell (R := R) 0) (headCell 0)
  else if k = 1 then TensorProduct.map (headCell (R := R) 1) (headCell 1)
  else TensorProduct.map ((headCell 0).comp a.sign) (headCell 2) +
    TensorProduct.map (headCell (R := R) 2) (headCell 1)

/-- Tensor the original interval diagonal with the specified tail diagonal. -/
noncomputable def diagonalStepMap (f : Diagonal a) :
    (Interval R ⊗[R] D) →ₗ[R] (Interval R ⊗[R] D) ⊗[R] (Interval R ⊗[R] D) :=
  TensorProduct.lift (Finsupp.llift _ R R _ fun k => (headDiagonalTerm a k).comp f.map)

@[simp] theorem diagonalStepMap_head (f : Diagonal a) (k : Fin 3) (x : D) :
    diagonalStepMap a f (single k 1 ⊗ₜ[R] x) = headDiagonalTerm a k (f.map x) := by
  simp [diagonalStepMap,headCell,Finsupp.llift_apply]

private theorem sign_sign (x : D) : a.sign (a.sign x) = x :=
  LinearMap.congr_fun a.sign_sq x
private theorem d_sign (x : D) : a.d (a.sign x) = -a.sign (a.d x) := by
  have h := LinearMap.congr_fun a.sign_d x
  change a.sign (a.d x) = -a.d (a.sign x) at h
  simpa only [neg_neg] using congrArg Neg.neg h.symm

private theorem headTerm_boundary (k : Fin 3) (z : D ⊗[R] D) :
    (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).d (headDiagonalTerm a k z) =
      (if k = 2 then headDiagonalTerm a 0 z-headDiagonalTerm a 1 z else 0) +
        (if k = 2 then -headDiagonalTerm a k ((a.tensor a).d z)
          else headDiagonalTerm a k ((a.tensor a).d z)) := by
  have h :
      (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).d.comp (headDiagonalTerm a k) =
        (if k = 2 then headDiagonalTerm a 0-headDiagonalTerm a 1 else 0) +
          (if k = 2 then -(headDiagonalTerm a k).comp (a.tensor a).d
            else (headDiagonalTerm a k).comp (a.tensor a).d) := by
    apply TensorProduct.ext'
    intro x y
    fin_cases k <;>
      simp [headDiagonalTerm,headCell,GradedContraction.tensor,tensorD,
        interval_d_single,interval_sign_single,TensorProduct.add_tmul,TensorProduct.sub_tmul,
        TensorProduct.neg_tmul,TensorProduct.tmul_add,TensorProduct.tmul_sub,
        TensorProduct.tmul_neg,d_sign,sign_sign] <;> abel
  by_cases hk : k = 2 <;> simpa only [hk,ite_true,ite_false,LinearMap.comp_apply,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.zero_apply] using
      LinearMap.congr_fun h z

private theorem headTerm_parity (k : Fin 3) (z : D ⊗[R] D) :
    (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).sign (headDiagonalTerm a k z) =
      if k = 2 then -headDiagonalTerm a k ((a.tensor a).sign z)
        else headDiagonalTerm a k ((a.tensor a).sign z) := by
  have h :
      (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).sign.comp (headDiagonalTerm a k) =
        if k = 2 then -(headDiagonalTerm a k).comp (a.tensor a).sign
          else (headDiagonalTerm a k).comp (a.tensor a).sign := by
    apply TensorProduct.ext'
    intro x y
    fin_cases k <;> simp [headDiagonalTerm,headCell,GradedContraction.tensor,interval_sign_single,TensorProduct.tmul_sub,TensorProduct.sub_tmul,
      TensorProduct.tmul_neg,TensorProduct.neg_tmul,sign_sign] <;> abel
  by_cases hk : k = 2 <;> simpa only [hk,ite_true,ite_false,LinearMap.comp_apply,
    LinearMap.add_apply,LinearMap.sub_apply,LinearMap.neg_apply,LinearMap.zero_apply] using
      LinearMap.congr_fun h z

/-- The head step is a chain map for the original left-minus-right tensor differential. -/
theorem diagonalStepMap_boundary (f : Diagonal a) (x : Interval R ⊗[R] D) :
    (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).d (diagonalStepMap a f x) =
      diagonalStepMap a f (((interval R 0).tensor a).d x) := by
  have h :
      (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).d.comp (diagonalStepMap a f) =
        (diagonalStepMap a f).comp ((interval R 0).tensor a).d := by
    apply TensorProduct.ext'
    intro u x
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [TensorProduct.add_tmul,map_add,LinearMap.comp_apply] at *; rw [hu,hv]
    | single k r =>
      have hs : single k r = r • (single k 1 : Interval R) := by simp
      rw [hs,← TensorProduct.smul_tmul']
      simp only [LinearMap.comp_apply,map_smul]
      congr 1
      change _ = diagonalStepMap a f
        ((interval R 0).d (single k 1) ⊗ₜ[R] x + (interval R 0).sign (single k 1) ⊗ₜ[R] a.d x)
      rw [show diagonalStepMap a f ((single k 1) ⊗ₜ[R] x) = headDiagonalTerm a k (f.map x) from
        diagonalStepMap_head a f k x,headTerm_boundary,f.boundary]
      fin_cases k <;> simp [interval_d_single,interval_sign_single,diagonalStepMap_head,
        TensorProduct.sub_tmul,TensorProduct.neg_tmul]
  exact LinearMap.congr_fun h x

/-- The head step retains the original tensor parity. -/
theorem diagonalStepMap_parity (f : Diagonal a) (x : Interval R ⊗[R] D) :
    (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).sign (diagonalStepMap a f x) =
      diagonalStepMap a f (((interval R 0).tensor a).sign x) := by
  have h :
      (((interval R 0).tensor a).tensor ((interval R 0).tensor a)).sign.comp (diagonalStepMap a f) =
        (diagonalStepMap a f).comp ((interval R 0).tensor a).sign := by
    apply TensorProduct.ext'
    intro u x
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp only [TensorProduct.add_tmul,map_add,LinearMap.comp_apply] at *; rw [hu,hv]
    | single k r =>
      have hs : single k r = r • (single k 1 : Interval R) := by simp
      rw [hs,← TensorProduct.smul_tmul']
      simp only [LinearMap.comp_apply,map_smul]
      congr 1
      change _ = diagonalStepMap a f ((interval R 0).sign (single k 1) ⊗ₜ[R] a.sign x)
      rw [show diagonalStepMap a f ((single k 1) ⊗ₜ[R] x) = headDiagonalTerm a k (f.map x) from
        diagonalStepMap_head a f k x,headTerm_parity,f.parity]
      fin_cases k <;> simp [interval_sign_single,diagonalStepMap_head,
        TensorProduct.neg_tmul]
  exact LinearMap.congr_fun h x

/-- The specified original diagonal on the interval tensor the specified tail. -/
noncomputable def diagonalStep (f : Diagonal a) : Diagonal ((interval R 0).tensor a) where
  map := diagonalStepMap a f
  boundary := diagonalStepMap_boundary a f
  parity := diagonalStepMap_parity a f

end BPFixedPoints.CechCubicalCell
