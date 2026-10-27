import BPFixedPoints.Incidence.CoefficientBaseChangeResolution

/-! # Minimality under coefficient base change preserving the residue map -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {S A k M N : Type*} [CommRing S] [CommRing A] [CommRing k]
  [Algebra S A] [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
  (e : S →+* k) (e' : A →+* k) (he : e'.comp (algebraMap S A) = e)

include he in
/-- A base change compatible with the origin preserves the augmentation-ideal condition. -/
theorem baseChange_minimal (d : M →ₗ[S] N)
    (hd : LinearMap.range d ≤ RingHom.ker e • (⊤ : Submodule S N)) :
    LinearMap.range (d.baseChange A) ≤
      RingHom.ker e' • (⊤ : Submodule A (A ⊗[S] N)) := by
  rintro _ ⟨x, rfl⟩
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | tmul a m =>
    change a ⊗ₜ[S] d m ∈ _
    have h : d m ∈ RingHom.ker e • (⊤ : Submodule S N) := hd ⟨m, rfl⟩
    refine Submodule.smul_induction_on h (fun r hr n hn => ?_) (fun x y hx hy => ?_)
    ·
      have hr' : algebraMap S A r ∈ RingHom.ker e' := by
        change e' (algebraMap S A r) = 0
        rw [← RingHom.comp_apply, he]
        exact hr
      rw [← TensorProduct.smul_tmul, Algebra.smul_def]
      exact Submodule.smul_mem_smul hr' (Submodule.mem_top : a ⊗ₜ[S] n ∈ ⊤)
    ·
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hx hy

end BPFixedPoints.ResolutionTools
