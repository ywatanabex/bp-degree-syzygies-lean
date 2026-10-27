import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# Degree-shifting linear maps on finitely supported modules

Extend basiswise degree conditions to arbitrary homogeneous elements, preserving
them under sums, composition, basis permutations and tensor products.
-/

namespace BPFixedPoints.ResolutionTools

open Finsupp
open scoped TensorProduct

section Basic

variable {R A B C M N P : Type*} [Semiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  [AddCommMonoid P] [Module R P]

/-- Linear map shifting homogeneous degree by a specified integer. -/
def HasDegree (da : A → ℤ) (db : B → ℤ) (k : ℤ)
    (f : (A →₀ M) →ₗ[R] (B →₀ N)) : Prop :=
  ∀ n x, x ∈ supported M R {a | da a = n} →
    f x ∈ supported N R {b | db b = n + k}

namespace HasDegree

variable {da : A → ℤ} {db : B → ℤ} {dc : C → ℤ} {k l : ℤ}
  {f : (A →₀ M) →ₗ[R] (B →₀ N)} {g : (B →₀ N) →ₗ[R] (C →₀ P)}

theorem of_single
    (hf : ∀ a m, f (single a m) ∈ supported N R {b | db b = da a + k}) :
    HasDegree da db k f := by
  intro n x hx
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro a ha
  have hda : da a = n := (mem_supported R x).mp hx ha
  simpa only [hda] using hf a (x a)

theorem apply_single (hf : HasDegree da db k f) (a : A) (m : M) :
    f (single a m) ∈ supported N R {b | db b = da a + k} :=
  hf (da a) _ (single_mem_supported R m rfl)

theorem zero (da : A → ℤ) (db : B → ℤ) (k : ℤ) :
    HasDegree da db k (0 : (A →₀ M) →ₗ[R] (B →₀ N)) := by
  intro n x hx
  exact Submodule.zero_mem _

theorem id (da : A → ℤ) : HasDegree da da 0 (LinearMap.id : (A →₀ M) →ₗ[R] _) := by
  intro n x hx
  simpa only [LinearMap.id_apply, add_zero] using hx

theorem add {f' : (A →₀ M) →ₗ[R] (B →₀ N)}
    (hf : HasDegree da db k f) (hf' : HasDegree da db k f') :
    HasDegree da db k (f + f') := by
  intro n x hx
  exact Submodule.add_mem _ (hf n x hx) (hf' n x hx)

theorem sum {ι : Type*} (s : Finset ι)
    (f : ι → (A →₀ M) →ₗ[R] (B →₀ N)) (hf : ∀ i ∈ s, HasDegree da db k (f i)) :
    HasDegree da db k (∑ i ∈ s, f i) := by
  intro n x hx
  rw [LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i hi => hf i hi n x hx

theorem comp (hg : HasDegree db dc l g) (hf : HasDegree da db k f) :
    HasDegree da dc (k + l) (g.comp f) := by
  intro n x hx
  simpa only [LinearMap.comp_apply, add_assoc] using hg (n + k) (f x) (hf n x hx)

theorem pow_zero {f : Module.End R (A →₀ M)}
    (hf : HasDegree da da 0 f) (n : ℕ) : HasDegree da da 0 (f ^ n) := by
  induction n with
  | zero => exact HasDegree.id da
  | succ n ih =>
    rw [pow_succ]
    exact ih.comp hf

theorem mapDomain (e : A ≃ B) (da : A → ℤ) (db : B → ℤ)
    (he : ∀ a, db (e a) = da a) :
    HasDegree da db 0 (Finsupp.lmapDomain M R e) := by
  apply of_single
  intro a m
  change Finsupp.mapDomain e (single a m) ∈ _
  rw [mapDomain_single]
  exact single_mem_supported R m (by
    change db (e a) = da a + 0
    simpa only [add_zero] using he a)

theorem mapRange (f : M →ₗ[R] N) (da : A → ℤ) :
    HasDegree da da 0 (Finsupp.mapRange.linearMap f) := by
  apply of_single
  intro a m
  simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]
  exact single_mem_supported R _ (by simp)

theorem constant (f : (A →₀ M) →ₗ[R] (B →₀ N)) (n : ℤ) :
    HasDegree (fun _ => n) (fun _ => n) 0 f := by
  apply of_single
  intro a m
  apply (mem_supported' R _).mpr
  intro b hb
  exact (hb (by simp)).elim

theorem congr_mapDomain {A' B' : Type*} (eA : A ≃ A') (eB : B ≃ B')
    (da' : A' → ℤ) (db' : B' → ℤ)
    (hA : ∀ a, da' (eA a) = da a) (hB : ∀ b, db' (eB b) = db b)
    (hf : HasDegree da db k f) :
    HasDegree da' db' k
      ((Finsupp.mapDomain.linearEquiv N R eB).toLinearMap.comp
        (f.comp (Finsupp.mapDomain.linearEquiv M R eA).symm.toLinearMap)) := by
  have hi : HasDegree da' da 0 (Finsupp.lmapDomain M R eA.symm) :=
    mapDomain eA.symm da' da (fun a' => by simpa only [Equiv.apply_symm_apply] using
      (hA (eA.symm a')).symm)
  have ho : HasDegree db db' 0 (Finsupp.lmapDomain N R eB) := mapDomain eB db db' hB
  simpa only [zero_add, add_zero, Finsupp.mapDomain.linearEquiv_symm,
    Finsupp.mapDomain.toLinearMap_linearEquiv] using ho.comp (hf.comp hi)

theorem eq_zero_of_const (hf : HasDegree da (fun _ : B => l) k f)
    {n : ℤ} {x : A →₀ M} (hx : x ∈ supported M R {a | da a = n})
    (hne : l ≠ n + k) : f x = 0 := by
  have h := hf n x hx
  apply Finsupp.ext
  intro b
  exact (mem_supported' R (f x)).mp h b hne

end HasDegree

end Basic

section AddGroup

variable {R A B M N : Type*} [Semiring R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

theorem HasDegree.neg {da : A → ℤ} {db : B → ℤ} {k : ℤ}
    {f : (A →₀ M) →ₗ[R] (B →₀ N)} (hf : HasDegree da db k f) :
    HasDegree da db k (-f) := by
  intro n x hx
  apply (mem_supported' R _).mpr
  intro b hb
  change -(f x b) = 0
  rw [(mem_supported' R _).mp (hf n x hx) b hb, neg_zero]

theorem HasDegree.sub {da : A → ℤ} {db : B → ℤ} {k : ℤ}
    {f g : (A →₀ M) →ₗ[R] (B →₀ N)}
    (hf : HasDegree da db k f) (hg : HasDegree da db k g) :
    HasDegree da db k (f - g) := by
  intro n x hx
  apply (mem_supported' R _).mpr
  intro b hb
  change f x b - g x b = 0
  rw [(mem_supported' R _).mp (hf n x hx) b hb,
    (mem_supported' R _).mp (hg n x hx) b hb, sub_zero]

end AddGroup

section Tensor

variable {R A B C D : Type*} [CommRing R]

/-- Tensor-product linear map returned to free-basis coordinates. -/
noncomputable def freeTensorMap
    (f : (A →₀ R) →ₗ[R] (C →₀ R)) (g : (B →₀ R) →ₗ[R] (D →₀ R)) :
    (A × B →₀ R) →ₗ[R] (C × D →₀ R) :=
  (finsuppTensorFinsupp' R C D).toLinearMap.comp
    ((TensorProduct.map f g).comp (finsuppTensorFinsupp' R A B).symm.toLinearMap)

theorem freeTensorMap_single_apply
    (f : (A →₀ R) →ₗ[R] (C →₀ R)) (g : (B →₀ R) →ₗ[R] (D →₀ R))
    (a : A) (b : B) (r : R) (c : C) (d : D) :
    freeTensorMap f g (single (a, b) r) (c, d) =
      f (single a 1) c * g (single b r) d := by
  simp only [freeTensorMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    finsuppTensorFinsupp'_symm_single_eq_single_one_tmul, TensorProduct.map_tmul,
    finsuppTensorFinsupp'_apply_apply]

theorem HasDegree.freeTensorMap
    {da : A → ℤ} {db : B → ℤ} {dc : C → ℤ} {dd : D → ℤ} {k l : ℤ}
    {f : (A →₀ R) →ₗ[R] (C →₀ R)} {g : (B →₀ R) →ₗ[R] (D →₀ R)}
    (hf : HasDegree da dc k f) (hg : HasDegree db dd l g) :
    HasDegree (fun a : A × B => da a.1 + db a.2)
      (fun c : C × D => dc c.1 + dd c.2) (k + l) (freeTensorMap f g) := by
  apply HasDegree.of_single
  rintro ⟨a, b⟩ r
  apply (mem_supported' R _).mpr
  rintro ⟨c, d⟩ hne
  rw [freeTensorMap_single_apply]
  by_cases hc : dc c = da a + k
  · have hd : dd d ≠ db b + l := by
      intro hd
      apply hne
      change dc c + dd d = (da a + db b) + (k + l)
      omega
    rw [(mem_supported' R _).mp (hg.apply_single b r) d hd, mul_zero]
  · rw [(mem_supported' R _).mp (hf.apply_single a 1) c hc, zero_mul]

theorem HasDegree.tensor_congr {A' C' : Type*}
    {da : A → ℤ} {db : B → ℤ} {dc : C → ℤ} {dd : D → ℤ} {k l : ℤ}
    {f : (A →₀ R) →ₗ[R] (C →₀ R)} {g : (B →₀ R) →ₗ[R] (D →₀ R)}
    (hf : HasDegree da dc k f) (hg : HasDegree db dd l g)
    (eA : A × B ≃ A') (eC : C × D ≃ C') (da' : A' → ℤ) (dc' : C' → ℤ)
    (hA : ∀ a, da' (eA a) = da a.1 + db a.2)
    (hC : ∀ c, dc' (eC c) = dc c.1 + dd c.2) :
    HasDegree da' dc' (k + l)
      (((finsuppTensorFinsupp' R C D).trans
        (Finsupp.mapDomain.linearEquiv R R eC)).toLinearMap.comp
        ((TensorProduct.map f g).comp
          ((finsuppTensorFinsupp' R A B).trans
            (Finsupp.mapDomain.linearEquiv R R eA)).symm.toLinearMap)) := by
  have ht := (hf.freeTensorMap hg).congr_mapDomain eA eC da' dc' hA hC
  convert ht using 1
  ext x
  rfl

end Tensor

end BPFixedPoints.ResolutionTools
