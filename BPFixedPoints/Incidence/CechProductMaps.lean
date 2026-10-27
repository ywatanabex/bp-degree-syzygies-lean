import BPFixedPoints.Incidence.CechProductBasis
import BPFixedPoints.Incidence.CechProductSign
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Homogeneous monomial action on the product Čech complex

At one vertex shift the left-chart exponent by a and the right-chart exponent
by b. The finite product preserves Čech degree and is a chain map from degree
vector d to d−(a+b).
-/

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

variable (R : Type*) [CommRing R]

noncomputable def lineMultiply (a b : ℕ) : Module.End R (Basis →₀ R) :=
  lmapDomain R R (shift a b)

@[simp] theorem lineMultiply_single (a b : ℕ) (x : Basis) (r : R) :
    lineMultiply R a b (single x r) = single (shift a b x) r := by
  simp [lineMultiply]

theorem lineMultiply_chainMap (d a b : ℕ) (hab : a + b ≤ d) :
    (lineMultiply R a b).comp (lineFree R d).d =
      (lineFree R (d - (a + b))).d.comp (lineMultiply R a b) := by
  apply Finsupp.lhom_ext
  intro x r
  rcases x with k | k | k
  · simp [shift]
  · simp only [LinearMap.comp_apply, lineFree_d_right, lineMultiply_single, shift]
    congr 3
    omega
  · simp [shift]

theorem lineMultiply_sign (d d' a b : ℕ) :
    (lineMultiply R a b).comp (lineFree R d).sign =
      (lineFree R d').sign.comp (lineMultiply R a b) := by
  apply Finsupp.lhom_ext
  intro x r
  rcases x with k | k | k <;> simp [shift]

/-- Multiply by a homogeneous monomial vertexwise. -/
noncomputable def multiply {V : Type*} (a b : V → ℕ) : Module.End R (C R V) :=
  lmapDomain R R (fun f v => shift (a v) (b v) (f v))

@[simp] theorem multiply_single {V : Type*} (a b : V → ℕ) (f : V → Basis) (r : R) :
    multiply R a b (single f r) = single (fun v => shift (a v) (b v) (f v)) r := by
  simp [multiply]

theorem multiply_comp {V : Type*} (a b a' b' : V → ℕ) :
    (multiply R a b).comp (multiply R a' b') =
      multiply R (a + a') (b + b') := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, multiply_single]
  congr 1
  funext v
  exact shift_comp (a v) (b v) (a' v) (b' v) (f v)

theorem multiply_commute {V : Type*} (a b a' b' : V → ℕ) :
    (multiply R a b).comp (multiply R a' b') =
      (multiply R a' b').comp (multiply R a b) := by
  rw [multiply_comp, multiply_comp, add_comm a a', add_comm b b']

@[simp] theorem multiply_zero {V : Type*} :
    multiply R (0 : V → ℕ) 0 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro f r
  simp

@[simp] theorem cechDegree_shift {V : Type*} [Fintype V]
    (a b : V → ℕ) (f : V → Basis) :
    cechDegree (fun v => shift (a v) (b v) (f v)) = cechDegree f := by
  simp [cechDegree]

theorem multiply_supported {V : Type*} [Fintype V] (a b : V → ℕ) (n : ℕ)
    {x : C R V} (hx : x ∈ supported R R {f | cechDegree f = n}) :
    multiply R a b x ∈ supported R R {f | cechDegree f = n} := by
  let f : (V → Basis) → (V → Basis) := fun q v => shift (a v) (b v) (q v)
  have hx' : x ∈ supported R R (f ⁻¹' {q | cechDegree q = n}) := by
    simpa only [f, Set.preimage_ofPred_eq, cechDegree_shift] using hx
  exact (supported_comap_lmapDomain R R f {q | cechDegree q = n}) hx'

theorem multiply_cons {n : ℕ} (a b : Fin (n + 1) → ℕ) :
    (multiply R a b).comp (consEquiv R fun _ : Fin (n + 1) => Basis).toLinearMap =
      (consEquiv R fun _ : Fin (n + 1) => Basis).toLinearMap.comp
        (TensorProduct.map (lineMultiply R (a 0) (b 0))
          (multiply R (fun i : Fin n => a i.succ) (fun i => b i.succ))) := by
  apply TensorProduct.ext
  apply Finsupp.lhom_ext
  intro x r
  apply Finsupp.lhom_ext
  intro f s
  change multiply R a b (consEquiv R _ (single x r ⊗ₜ[R] single f s)) =
    consEquiv R _ (TensorProduct.map _ _ (single x r ⊗ₜ[R] single f s))
  rw [consEquiv_single_tmul_single, multiply_single, TensorProduct.map_tmul,
    lineMultiply_single, multiply_single, consEquiv_single_tmul_single]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

private theorem tensor_chainMap
    {A B A' B' : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (d s : Module.End R A) (e : Module.End R B)
    (d' s' : Module.End R A') (e' : Module.End R B')
    (f : A →ₗ[R] A') (g : B →ₗ[R] B')
    (hf : f.comp d = d'.comp f) (hg : g.comp e = e'.comp g)
    (hs : f.comp s = s'.comp f) :
    (TensorProduct.map f g).comp (TensorProduct.map d 1 + TensorProduct.map s e) =
      (TensorProduct.map d' 1 + TensorProduct.map s' e').comp (TensorProduct.map f g) := by
  simp only [LinearMap.comp_add, LinearMap.add_comp, ← TensorProduct.map_comp,
    Module.End.one_eq_id, LinearMap.comp_id, LinearMap.id_comp, hf, hg, hs]

private theorem transported_chainMap
    {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (e : A ≃ₗ[R] B) (d d' g : Module.End R A) (f : Module.End R B)
    (hf : f.comp e.toLinearMap = e.toLinearMap.comp g)
    (hg : g.comp d = d'.comp g) :
    f.comp (e.toLinearMap.comp (d.comp e.symm.toLinearMap)) =
      (e.toLinearMap.comp (d'.comp e.symm.toLinearMap)).comp f := by
  ext x
  obtain ⟨x, rfl⟩ := e.surjective x
  have hfy (y : A) : f (e y) = e (g y) := LinearMap.congr_fun hf y
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hfy, hfy, LinearEquiv.symm_apply_apply]
  exact congrArg e (LinearMap.congr_fun hg x)

private theorem tensor_contraction_chainMap
    {A B H K H' K' : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]
    [AddCommGroup H'] [Module R H'] [AddCommGroup K'] [Module R K']
    (c : GradedContraction R A H) (e : GradedContraction R B K)
    (c' : GradedContraction R A H') (e' : GradedContraction R B K')
    (f : Module.End R A) (g : Module.End R B)
    (hf : f.comp c.d = c'.d.comp f) (hg : g.comp e.d = e'.d.comp g)
    (hs : f.comp c.sign = c'.sign.comp f) :
    (TensorProduct.map f g).comp (c.tensor e).d =
      (c'.tensor e').d.comp (TensorProduct.map f g) :=
  tensor_chainMap R c.d c.sign e.d c'.d c'.sign e'.d f g hf hg hs

private theorem congr_d_eq
    {A B H K : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup H] [Module R H] [AddCommGroup K] [Module R K]
    (c : GradedContraction R A H) (e : A ≃ₗ[R] B) (f : H ≃ₗ[R] K) :
    (c.congr e f).d = e.toLinearMap.comp (c.d.comp e.symm.toLinearMap) := rfl

theorem finProduct_multiply_chainMap : ∀ (n : ℕ) (d a b : Fin n → ℕ),
    (∀ i, a i + b i ≤ d i) →
    (multiply R a b).comp (finProduct R n d).d =
      (finProduct R n (fun i => d i - (a i + b i))).d.comp (multiply R a b)
  | 0, d, a, b, hab => by simp [finProduct, empty]
  | n + 1, d, a, b, hab => by
    let c := lineFree R (d 0)
    let c' := lineFree R (d 0 - (a 0 + b 0))
    let k := finProduct R n (fun i => d i.succ)
    let k' := finProduct R n (fun i => d i.succ - (a i.succ + b i.succ))
    let e := consEquiv R fun _ : Fin (n + 1) => Basis
    let t :=
      (TensorProduct.map (lineMultiply R (a 0) (b 0))
        (multiply R (fun i : Fin n => a i.succ) (fun i => b i.succ)))
    have ht := tensor_contraction_chainMap R c k c' k'
        (lineMultiply R (a 0) (b 0))
        (multiply R (fun i : Fin n => a i.succ) (fun i => b i.succ))
        (lineMultiply_chainMap R (d 0) (a 0) (b 0) (hab 0))
        (finProduct_multiply_chainMap n (fun i => d i.succ)
          (fun i => a i.succ) (fun i => b i.succ) (fun i => hab i.succ))
        (lineMultiply_sign R (d 0) (d 0 - (a 0 + b 0)) (a 0) (b 0))
    have he (y) : multiply R a b (e y) = e (t y) :=
      LinearMap.congr_fun (multiply_cons R a b) y
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, finProduct, GradedContraction.congr_d_apply]
    change multiply R a b (e ((c.tensor k).d (e.symm x))) =
      e ((c'.tensor k').d (e.symm (multiply R a b x)))
    rw [he]
    have he' : e.symm (multiply R a b x) = t (e.symm x) := by
      apply e.injective
      simpa only [LinearEquiv.apply_symm_apply] using he (e.symm x)
    rw [he']
    exact congrArg e (LinearMap.congr_fun ht (e.symm x))

theorem multiply_reindex {V W : Type*} (e : V ≃ W) (a b : W → ℕ) :
    (multiply R a b).comp
        (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl Basis))).toLinearMap =
      (Finsupp.mapDomain.linearEquiv R R (e.arrowCongr (Equiv.refl Basis))).toLinearMap.comp
        (multiply R (fun v => a (e v)) (fun v => b (e v))) := by
  apply Finsupp.lhom_ext
  intro f r
  change multiply R a b (mapDomain (e.arrowCongr (Equiv.refl Basis)) (single f r)) =
    mapDomain (e.arrowCongr (Equiv.refl Basis))
      (multiply R (fun v => a (e v)) (fun v => b (e v)) (single f r))
  rw [mapDomain_single, multiply_single, multiply_single, mapDomain_single]
  congr 1
  ext v
  simp

/-- Homogeneous monomial multiplication gives a Čech chain map decreasing the line-bundle twist. -/
theorem multiply_chainMap {V : Type*} [Fintype V] (d a b : V → ℕ)
    (hab : ∀ v, a v + b v ≤ d v) :
    (multiply R a b).comp (contraction R d).d =
      (contraction R (fun v => d v - (a v + b v))).d.comp (multiply R a b) := by
  apply transported_chainMap R
    (Finsupp.mapDomain.linearEquiv R R
      ((Fintype.equivFin V).symm.arrowCongr (Equiv.refl Basis)))
    _ _ _ _ (multiply_reindex R (Fintype.equivFin V).symm a b)
  exact finProduct_multiply_chainMap R _ _ _ _ (fun i => hab ((Fintype.equivFin V).symm i))

theorem multiply_sign {V : Type*} [Fintype V] (d d' a b : V → ℕ) :
    (multiply R a b).comp (contraction R d).sign =
      (contraction R d').sign.comp (multiply R a b) := by
  apply Finsupp.lhom_ext
  intro f r
  simp only [LinearMap.comp_apply, contraction_sign_single, map_smul,
    multiply_single, cechDegree_shift]

end BPFixedPoints.CechProduct
