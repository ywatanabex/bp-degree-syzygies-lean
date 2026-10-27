import BPFixedPoints.Incidence.CechLineTensorChain
import BPFixedPoints.Incidence.CechTensorTransport
import BPFixedPoints.Incidence.CechProductCup

/-!
# Cup product on the full multi-vertex Čech complex

Construct the signed tensor of local Alexander–Whitney products on all chains.
Prove Leibniz for the existing differential and independence from arbitrary
cocycle representatives. Edge exterior products and comparison with standard
Tor multiplication are separate steps.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

section Tensor

variable {A B D H K L : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  {a : GradedContraction R A H} {b : GradedContraction R B K}
  {c : GradedContraction R D L} (f : ChainPairing a b c)

/-- Return local factors to the existing free-basis presentation. -/
noncomputable def lineFreeTensorChainPairing (d e : ℕ) :
    ChainPairing ((lineFree R d).tensor a) ((lineFree R e).tensor b)
      ((lineFree R (d + e)).tensor c) :=
  ((CechLine.tensorChainPairing f d e).congr
    (A' := (Basis →₀ R) ⊗[R] A) (B' := (Basis →₀ R) ⊗[R] B)
    (C' := (Basis →₀ R) ⊗[R] D)
    (H' := (Fin (phi d) →₀ R) ⊗[R] H) (K' := (Fin (phi e) →₀ R) ⊗[R] K)
    (L' := (Fin (phi (d + e)) →₀ R) ⊗[R] L)
    (TensorProduct.congr (lineBasisEquiv R).symm (.refl R A))
    (TensorProduct.congr (lineBasisEquiv R).symm (.refl R B))
    (TensorProduct.congr (lineBasisEquiv R).symm (.refl R D))
    (TensorProduct.congr (lineHBasisEquiv R d) (.refl R H))
    (TensorProduct.congr (lineHBasisEquiv R e) (.refl R K))
    (TensorProduct.congr (lineHBasisEquiv R (d + e)) (.refl R L))).rebase
      _ _ _ (by exact tensor_congr_left_d (line R d) a (lineBasisEquiv R).symm (lineHBasisEquiv R d))
      (by exact tensor_congr_left_d (line R e) b (lineBasisEquiv R).symm (lineHBasisEquiv R e))
      (by exact tensor_congr_left_d (line R (d + e)) c (lineBasisEquiv R).symm (lineHBasisEquiv R (d + e)))
      (by exact tensor_congr_left_sign (line R d) a (lineBasisEquiv R).symm (lineHBasisEquiv R d))
      (by exact tensor_congr_left_sign (line R e) b (lineBasisEquiv R).symm (lineHBasisEquiv R e))
      (by exact tensor_congr_left_sign (line R (d + e)) c (lineBasisEquiv R).symm (lineHBasisEquiv R (d + e)))

end Tensor

/-- On the empty vertex set the total Čech product is coefficient multiplication. -/
noncomputable def emptyChainMul : C R (Fin 0) →ₗ[R] C R (Fin 0) →ₗ[R] C R (Fin 0) :=
  Finsupp.llift _ R R _ fun _ =>
    Finsupp.llift _ R R _ fun _ => single (fun i => Fin.elim0 i) 1

noncomputable def emptyChainPairing (d e : Fin 0 → ℕ) :
    ChainPairing (empty R d) (empty R e) (empty R (d + e)) where
  mul := emptyChainMul R
  leibniz x y := by simp [empty]
  sign_mul x y := by simp [empty]

noncomputable def finChainPairing : (n : ℕ) → (d e : Fin n → ℕ) →
    ChainPairing (finProduct R n d) (finProduct R n e) (finProduct R n (d + e))
  | 0, d, e => emptyChainPairing R d e
  | n + 1, d, e =>
    (lineFreeTensorChainPairing R (finChainPairing n (Fin.tail d) (Fin.tail e))
      (d 0) (e 0)).congr
      (consEquiv R fun _ => Basis) (consEquiv R fun _ => Basis) (consEquiv R fun _ => Basis)
      (consEquiv R fun i => Fin (phi (d i))) (consEquiv R fun i => Fin (phi (e i)))
      (consEquiv R fun i => Fin (phi ((d + e) i)))

noncomputable def chainPairing {V : Type*} [Fintype V] (d e : V → ℕ) :
    ChainPairing (contraction R d) (contraction R e) (contraction R (d + e)) :=
  let v := (Fintype.equivFin V).symm
  let u := Finsupp.mapDomain.linearEquiv R R (v.arrowCongr (Equiv.refl Basis))
  (finChainPairing R (Fintype.card V) (fun i => d (v i)) (fun i => e (v i))).congr u u u
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi (d i))) v))
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi (e i))) v))
    (Finsupp.mapDomain.linearEquiv R R (Equiv.piCongrLeft (fun i => Fin (phi ((d + e) i))) v))

/-- Product on all chains of the actual multi-vertex Čech complex. -/
noncomputable def chainCup {V : Type*} [Fintype V] (d e : V → ℕ) :
    C R V →ₗ[R] C R V →ₗ[R] C R V := (chainPairing R d e).mul

theorem chainCup_leibniz {V : Type*} [Fintype V] (d e : V → ℕ) (x y : C R V) :
    (contraction R (d + e)).d (chainCup R d e x y) =
      chainCup R d e ((contraction R d).d x) y +
      chainCup R d e ((contraction R d).sign x) ((contraction R e).d y) :=
  (chainPairing R d e).leibniz x y

theorem chainCup_sign {V : Type*} [Fintype V] (d e : V → ℕ) (x y : C R V) :
    (contraction R (d + e)).sign (chainCup R d e x y) =
      chainCup R d e ((contraction R d).sign x) ((contraction R e).sign y) :=
  (chainPairing R d e).sign_mul x y

theorem chainCup_cycles {V : Type*} [Fintype V] (d e : V → ℕ) {x y : C R V}
    (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0) :
    (contraction R (d + e)).d (chainCup R d e x y) = 0 :=
  (chainPairing R d e).mul_cycles hx hy

/-- Descent formula for arbitrary cocycles. -/
theorem chainPairing_cup_projection {V : Type*} [Fintype V] (d e : V → ℕ) {x y : C R V}
    (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0) :
    (chainPairing R d e).cup ((contraction R d).p x) ((contraction R e).p y) =
      (contraction R (d + e)).p (chainCup R d e x y) :=
  (chainPairing R d e).cup_projection hx hy

theorem chainCup_projection_eq_of_same_class {V : Type*} [Fintype V] (d e : V → ℕ)
    {x x' y y' : C R V}
    (hx : (contraction R d).d x = 0) (hx' : (contraction R d).d x' = 0)
    (hy : (contraction R e).d y = 0) (hy' : (contraction R e).d y' = 0)
    (hxx : (contraction R d).p x = (contraction R d).p x')
    (hyy : (contraction R e).p y = (contraction R e).p y') :
    (contraction R (d + e)).p (chainCup R d e x y) =
      (contraction R (d + e)).p (chainCup R d e x' y') :=
  (chainPairing R d e).projection_eq_of_same_class hx hx' hy hy' hxx hyy

end BPFixedPoints.CechProduct
