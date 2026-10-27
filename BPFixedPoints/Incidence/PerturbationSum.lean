import BPFixedPoints.Incidence.Perturbation
import Mathlib.LinearAlgebra.Finsupp.SumProd
import Mathlib.LinearAlgebra.Finsupp.Defs

/-! # Products of strong contractions and changes of basis -/

namespace BPFixedPoints.IncidencePerturbation

variable {R : Type*} [CommRing R]

def piMap {I : Type*} {M N : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) : (∀ i, M i) →ₗ[R] (∀ i, N i) where
  toFun x i := f i (x i)
  map_add' x y := by ext i; exact map_add (f i) _ _
  map_smul' a x := by ext i; exact map_smul (f i) a (x i)

@[simp] theorem piMap_apply {I : Type*} {M N : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) (x : ∀ i, M i) (i : I) : piMap f x i = f i (x i) := rfl

namespace Contraction

noncomputable def pi {I : Type*} {M H : I → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
    (C : ∀ i, Contraction R (M i) (H i)) :
    Contraction R (∀ i, M i) (∀ i, H i) where
  d := piMap fun i => (C i).d
  i := piMap fun i => (C i).i
  p := piMap fun i => (C i).p
  h := piMap fun i => (C i).h
  d_sq := by ext x i; exact LinearMap.congr_fun (C i).d_sq (x i)
  d_i := by ext x i; exact LinearMap.congr_fun (C i).d_i (x i)
  p_d := by ext x i; exact LinearMap.congr_fun (C i).p_d (x i)
  p_i := by ext x i; exact LinearMap.congr_fun (C i).p_i (x i)
  homotopy := by ext x i; exact LinearMap.congr_fun (C i).homotopy (x i)
  h_sq := by ext x i; exact LinearMap.congr_fun (C i).h_sq (x i)
  h_i := by ext x i; exact LinearMap.congr_fun (C i).h_i (x i)
  p_h := by ext x i; exact LinearMap.congr_fun (C i).p_h (x i)

variable {M H M' H' : Type*}
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  [AddCommGroup M'] [Module R M'] [AddCommGroup H'] [Module R H']

/-- Transfer a contraction by a linear isomorphism. -/
noncomputable def congr (C : Contraction R M H) (e : M ≃ₗ[R] M') (f : H ≃ₗ[R] H') :
    Contraction R M' H' where
  d := e.toLinearMap.comp (C.d.comp e.symm.toLinearMap)
  i := e.toLinearMap.comp (C.i.comp f.symm.toLinearMap)
  p := f.toLinearMap.comp (C.p.comp e.symm.toLinearMap)
  h := e.toLinearMap.comp (C.h.comp e.symm.toLinearMap)
  d_sq := by
    ext x
    change e (C.d (e.symm (e (C.d (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.d_sq (e.symm x)
    change C.d (C.d (e.symm x)) = 0 at hd
    rw [hd, map_zero]
  d_i := by
    ext x
    change e (C.d (e.symm (e (C.i (f.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.d_i (f.symm x)
    change C.d (C.i (f.symm x)) = 0 at hd
    rw [hd, map_zero]
  p_d := by
    ext x
    change f (C.p (e.symm (e (C.d (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.p_d (e.symm x)
    change C.p (C.d (e.symm x)) = 0 at hd
    rw [hd, map_zero]
  p_i := by
    ext x
    change f (C.p (e.symm (e (C.i (f.symm x))))) = x
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.p_i (f.symm x)
    change C.p (C.i (f.symm x)) = f.symm x at hd
    rw [hd, f.apply_symm_apply]
  homotopy := by
    ext x
    change e (C.d (e.symm (e (C.h (e.symm x))))) +
      e (C.h (e.symm (e (C.d (e.symm x))))) +
      e (C.i (f.symm (f (C.p (e.symm x))))) = x
    simp only [e.symm_apply_apply, f.symm_apply_apply]
    rw [← map_add, ← map_add]
    have hd := LinearMap.congr_fun C.homotopy (e.symm x)
    change C.d (C.h (e.symm x)) + C.h (C.d (e.symm x)) + C.i (C.p (e.symm x)) =
      e.symm x at hd
    rw [hd, e.apply_symm_apply]
  h_sq := by
    ext x
    change e (C.h (e.symm (e (C.h (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.h_sq (e.symm x)
    change C.h (C.h (e.symm x)) = 0 at hd
    rw [hd, map_zero]
  h_i := by
    ext x
    change e (C.h (e.symm (e (C.i (f.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.h_i (f.symm x)
    change C.h (C.i (f.symm x)) = 0 at hd
    rw [hd, map_zero]
  p_h := by
    ext x
    change f (C.p (e.symm (e (C.h (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have hd := LinearMap.congr_fun C.p_h (e.symm x)
    change C.p (C.h (e.symm x)) = 0 at hd
    rw [hd, map_zero]

@[simp] theorem congr_d_apply (C : Contraction R M H) (e : M ≃ₗ[R] M')
    (f : H ≃ₗ[R] H') (x : M') :
    (C.congr e f).d x = e (C.d (e.symm x)) := rfl

@[simp] theorem congr_h_apply (C : Contraction R M H) (e : M ≃ₗ[R] M')
    (f : H ≃ₗ[R] H') (x : M') :
    (C.congr e f).h x = e (C.h (e.symm x)) := rfl

@[simp] theorem congr_i_apply (C : Contraction R M H) (e : M ≃ₗ[R] M')
    (f : H ≃ₗ[R] H') (x : H') :
    (C.congr e f).i x = e (C.i (f.symm x)) := rfl

@[simp] theorem congr_p_apply (C : Contraction R M H) (e : M ≃ₗ[R] M')
    (f : H ≃ₗ[R] H') (x : M') :
    (C.congr e f).p x = f (C.p (e.symm x)) := rfl

/-- Direct sum of finitely many based strong contractions. -/
noncomputable def sigma {I : Type*} [Fintype I] {B K : I → Type*}
    (C : ∀ i, Contraction R (B i →₀ R) (K i →₀ R)) :
    Contraction R ((Σ i, B i) →₀ R) ((Σ i, K i) →₀ R) :=
  (pi C).congr (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm

/-- Assemble finitely many contractions with a common source in finitely supported state coordinates. -/
noncomputable def finsupp {I : Type*} [Fintype I] {M : Type*} {K : I → Type*}
    [AddCommGroup M] [Module R M]
    (C : ∀ i, Contraction R M (K i →₀ R)) :
    Contraction R (I →₀ M) ((Σ i, K i) →₀ R) :=
  (pi C).congr (Finsupp.linearEquivFunOnFinite R M I).symm
    (Finsupp.sigmaFinsuppLEquivPiFinsupp R).symm

@[simp] theorem finsupp_d_apply {I : Type*} [Fintype I] {M : Type*} {K : I → Type*}
    [AddCommGroup M] [Module R M]
    (C : ∀ i, Contraction R M (K i →₀ R)) (x : I →₀ M) (i : I) :
    (finsupp C).d x i = (C i).d (x i) := rfl

@[simp] theorem finsupp_h_apply {I : Type*} [Fintype I] {M : Type*} {K : I → Type*}
    [AddCommGroup M] [Module R M]
    (C : ∀ i, Contraction R M (K i →₀ R)) (x : I →₀ M) (i : I) :
    (finsupp C).h x i = (C i).h (x i) := rfl

@[simp] theorem finsupp_p_apply {I : Type*} [Fintype I] {M : Type*} {K : I → Type*}
    [AddCommGroup M] [Module R M]
    (C : ∀ i, Contraction R M (K i →₀ R)) (x : I →₀ M) (i : I) (k : K i) :
    (finsupp C).p x ⟨i, k⟩ = (C i).p (x i) k := rfl

end Contraction

end BPFixedPoints.IncidencePerturbation
