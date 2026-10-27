import BPFixedPoints.Incidence.CechChainPairing

namespace BPFixedPoints.GradedContraction

open scoped TensorProduct

variable {R A A' B H H' K : Type*} [CommRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup H] [Module R H]
  [AddCommGroup H'] [Module R H'] [AddCommGroup K] [Module R K]
  (a : GradedContraction R A H) (b : GradedContraction R B K)
  (u : A ≃ₗ[R] A') (v : H ≃ₗ[R] H')

theorem tensor_congr_left_d :
    ((a.congr u v).tensor b).d =
      ((a.tensor b).congr (TensorProduct.congr u (.refl R B))
        (TensorProduct.congr v (.refl R K))).d := by
  apply TensorProduct.ext'
  intro x y
  simp [tensor, tensorD, congr_d_apply, congr_sign_apply]

theorem tensor_congr_left_sign :
    ((a.congr u v).tensor b).sign =
      ((a.tensor b).congr (TensorProduct.congr u (.refl R B))
        (TensorProduct.congr v (.refl R K))).sign := by
  apply TensorProduct.ext'
  intro x y
  simp [tensor, congr_sign_apply]

end BPFixedPoints.GradedContraction
