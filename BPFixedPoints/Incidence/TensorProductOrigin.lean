import Mathlib.RingTheory.TensorProduct.Maps

/-! # Compatible residue maps on a tensor product of coefficient algebras -/

namespace BPFixedPoints.ResolutionTools

open scoped TensorProduct

variable {T S B k : Type*} [CommRing T] [CommRing S] [CommRing B] [CommRing k]
  [Algebra T S] [Algebra T B]
  (eT : T →+* k) (eS : S →+* k) (eB : B →+* k)
  (hS : eS.comp (algebraMap T S) = eT) (hB : eB.comp (algebraMap T B) = eT)

noncomputable def tensorProductOrigin : S ⊗[T] B →+* k := by
  letI := eT.toAlgebra
  let f : S →ₐ[T] k := { toRingHom := eS, commutes' := fun t => DFunLike.congr_fun hS t }
  let g : B →ₐ[T] k := { toRingHom := eB, commutes' := fun t => DFunLike.congr_fun hB t }
  exact (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom

@[simp] theorem tensorProductOrigin_tmul (s : S) (b : B) :
    tensorProductOrigin eT eS eB hS hB (s ⊗ₜ[T] b) = eS s * eB b := rfl

theorem tensorProductOrigin_compatible :
    (tensorProductOrigin eT eS eB hS hB).comp (algebraMap S (S ⊗[T] B)) = eS := by
  apply RingHom.ext
  intro s
  simp [Algebra.TensorProduct.algebraMap_apply]

end BPFixedPoints.ResolutionTools
