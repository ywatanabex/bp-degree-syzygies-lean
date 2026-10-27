import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Nondegeneracy in implicit-function coordinates

Suppose F(β(x),ψ(x))=0 and a differentiable left inverse satisfies
r(β(x),ψ(x))=x. If the derivative of F in its second variable is injective,
then so is the derivative of β. This chain-rule lemma transfers BP polynomial
nondegeneracy to the vertex map.
-/

namespace BPFixedPoints

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X B Y : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem fderiv_injective_of_implicit_leftInverse
    {β : X → B} {ψ : X → Y} {F : B × Y → Y} {r : B × Y → X} {x : X}
    (hβ : DifferentiableAt 𝕜 β x) (hψ : DifferentiableAt 𝕜 ψ x)
    (hF : DifferentiableAt 𝕜 F (β x, ψ x))
    (hr : DifferentiableAt 𝕜 r (β x, ψ x))
    (hzero : ∀ z, F (β z, ψ z) = 0)
    (hleft : ∀ z, r (β z, ψ z) = z)
    (hinj : Function.Injective (fderiv 𝕜 (fun y => F (β x, y)) (ψ x))) :
    Function.Injective (fderiv 𝕜 β x) := by
  have hFD : (fderiv 𝕜 F (β x, ψ x)).comp
      ((fderiv 𝕜 β x).prod (fderiv 𝕜 ψ x)) = 0 := by
    have h := hF.hasFDerivAt.comp x (hβ.hasFDerivAt.prodMk hψ.hasFDerivAt)
    have heq : (fun z => F (β z, ψ z)) = fun _ => (0 : Y) := funext hzero
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.unique (hasFDerivAt_const _ _)
  have hrD : (fderiv 𝕜 r (β x, ψ x)).comp
      ((fderiv 𝕜 β x).prod (fderiv 𝕜 ψ x)) = ContinuousLinearMap.id 𝕜 X := by
    have h := hr.hasFDerivAt.comp x (hβ.hasFDerivAt.prodMk hψ.hasFDerivAt)
    have heq : (fun z => r (β z, ψ z)) = id := funext hleft
    simp only [Function.comp_def] at h
    rw [heq] at h
    exact h.unique (hasFDerivAt_id x)
  have hpartial : fderiv 𝕜 (fun y => F (β x, y)) (ψ x) =
      (fderiv 𝕜 F (β x, ψ x)).comp (ContinuousLinearMap.inr 𝕜 B Y) :=
    (hF.hasFDerivAt.comp (ψ x) (hasFDerivAt_prodMk_right (β x) (ψ x))).fderiv
  intro v w hvw
  have hβ0 : fderiv 𝕜 β x (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hψ0 : fderiv 𝕜 ψ x (v - w) = 0 := by
    apply hinj
    rw [map_zero, hpartial]
    have h := congrArg (fun L : X →L[𝕜] Y => L (v - w)) hFD
    simpa [ContinuousLinearMap.comp_apply, hβ0] using h
  have h := congrArg (fun L : X →L[𝕜] X => L (v - w)) hrD
  have hsub : v - w = 0 := by
    have h0 : fderiv 𝕜 r (β x, ψ x) (0 : B × Y) = v - w := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
        hβ0, hψ0, Prod.mk_zero_zero, ContinuousLinearMap.id_apply] using h
    exact h0.symm.trans (map_zero _)
  exact sub_eq_zero.mp hsub

end BPFixedPoints
