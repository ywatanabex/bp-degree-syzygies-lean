import BPFixedPoints.Incidence.CechCupCohomology
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Čech cocycle products by signed tensor products

Tensor the products of chosen cocycle representatives from local cup products.
Prove closedness for the actual tensor differential and that contraction
projection gives the tensor of local cohomology products. Comparison with the
derived Tor product is a separate assertion.
-/

namespace BPFixedPoints

open scoped TensorProduct

namespace CupTools

variable {R A B C D E F : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Tensor two bilinear maps, interchanging the middle factors. -/
noncomputable def tensorBilinear (f : A →ₗ[R] B →ₗ[R] C) (g : D →ₗ[R] E →ₗ[R] F) :
    (A ⊗[R] D) →ₗ[R] (B ⊗[R] E) →ₗ[R] (C ⊗[R] F) :=
  TensorProduct.curry ((TensorProduct.map (TensorProduct.lift f) (TensorProduct.lift g)).comp
    (TensorProduct.tensorTensorTensorComm R A D B E).toLinearMap)

@[simp] theorem tensorBilinear_tmul (f : A →ₗ[R] B →ₗ[R] C)
    (g : D →ₗ[R] E →ₗ[R] F) (a : A) (b : B) (d : D) (e : E) :
    tensorBilinear f g (a ⊗ₜ[R] d) (b ⊗ₜ[R] e) = f a b ⊗ₜ[R] g d e := rfl

end CupTools

namespace GradedContraction

variable {R C H A B : Type*} [CommRing R]
  [AddCommGroup C] [Module R C] [AddCommGroup H] [Module R H]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Bilinear map from two cohomology modules to actual target cocycles. -/
structure CyclePairing (c : GradedContraction R C H) (A B : Type*)
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] where
  representative : A →ₗ[R] B →ₗ[R] C
  closed : ∀ x y, c.d (representative x y) = 0

namespace CyclePairing

variable {c : GradedContraction R C H} (f : CyclePairing c A B)

/-- Project a cocycle product to cohomology using the actual contraction. -/
noncomputable def cup : A →ₗ[R] B →ₗ[R] H := f.representative.compr₂ c.p

@[simp] theorem cup_apply (x : A) (y : B) : f.cup x y = c.p (f.representative x y) := rfl

section Tensor

variable {D K A' B' : Type*}
  [AddCommGroup D] [Module R D] [AddCommGroup K] [Module R K]
  [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
  {e : GradedContraction R D K} (g : CyclePairing e A' B')

/-- Tensor product with the Koszul sign for interchanging homogeneous inputs made explicit. -/
noncomputable def tensor (s : R) : CyclePairing (c.tensor e) (A ⊗[R] A') (B ⊗[R] B') where
  representative := s • CupTools.tensorBilinear f.representative g.representative
  closed := by
    have heq : ((s • CupTools.tensorBilinear f.representative g.representative).compr₂
        (c.tensor e).d) = 0 := by
      apply TensorProduct.ext'
      intro a a'
      apply TensorProduct.ext'
      intro b b'
      simp [LinearMap.compr₂_apply, LinearMap.smul_apply, CupTools.tensorBilinear_tmul,
        GradedContraction.tensor, tensorD, f.closed, g.closed]
    intro x y
    exact LinearMap.congr_fun (LinearMap.congr_fun heq x) y

@[simp] theorem tensor_representative_tmul (s : R) (a : A) (a' : A') (b : B) (b' : B') :
    (f.tensor g s).representative (a ⊗ₜ[R] a') (b ⊗ₜ[R] b') =
      s • (f.representative a b ⊗ₜ[R] g.representative a' b') := rfl

/-- The projected product is the signed tensor of local cohomology products. -/
theorem tensor_cup_tmul (s : R) (a : A) (a' : A') (b : B) (b' : B') :
    (f.tensor g s).cup (a ⊗ₜ[R] a') (b ⊗ₜ[R] b') =
      s • (f.cup a b ⊗ₜ[R] g.cup a' b') := by
  simp [cup, tensor, GradedContraction.tensor, tensorP]

end Tensor

section Congr

variable {C' H' A' B' : Type*}
  [AddCommGroup C'] [Module R C'] [AddCommGroup H'] [Module R H']
  [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']

/-- Transfer to the existing free-basis presentation. -/
noncomputable def congr (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (u : C ≃ₗ[R] C') (v : H ≃ₗ[R] H') : CyclePairing (c.congr u v) A' B' where
  representative := (f.representative.compl₁₂ a.symm.toLinearMap b.symm.toLinearMap).compr₂
    u.toLinearMap
  closed x y := by
    change (c.congr u v).d (u (f.representative (a.symm x) (b.symm y))) = 0
    rw [GradedContraction.congr_d_apply, LinearEquiv.symm_apply_apply, f.closed, map_zero]

@[simp] theorem congr_representative_apply (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (u : C ≃ₗ[R] C') (v : H ≃ₗ[R] H') (x : A') (y : B') :
    (f.congr a b u v).representative x y = u (f.representative (a.symm x) (b.symm y)) := rfl

theorem congr_cup_apply (a : A ≃ₗ[R] A') (b : B ≃ₗ[R] B')
    (u : C ≃ₗ[R] C') (v : H ≃ₗ[R] H') (x : A') (y : B') :
    (f.congr a b u v).cup x y = v (f.cup (a.symm x) (b.symm y)) := by
  simp [cup, congr, GradedContraction.congr_p_apply]

end Congr

end CyclePairing
end GradedContraction

namespace CechLine

open CechProduct

variable {R : Type*} [CommRing R]

/-- The existing one-vertex cup product and its chosen cocycle representatives. -/
noncomputable def cyclePairing (d e : ℕ) :
    GradedContraction.CyclePairing (line R (d + e)) (LineH R d) (LineH R e) where
  representative := (cupLinear d e).compl₁₂ (lineI R d) (lineI R e)
  closed x y := cup_cycles d e (lineD_lineI d x) (lineD_lineI e y)

@[simp] theorem cyclePairing_cup (d e : ℕ) (x : LineH R d) (y : LineH R e) :
    (cyclePairing d e).cup x y = cohomologyCup d e x y := rfl

end CechLine
end BPFixedPoints
