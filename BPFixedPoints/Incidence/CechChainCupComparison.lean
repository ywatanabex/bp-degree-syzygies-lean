import BPFixedPoints.Incidence.CechProductChainCup

/-! # Comparing the full chain product with the chosen Čech cocycle product -/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

theorem finProduct_sign_of_supported (n : ℕ) (d : Fin n → ℕ) (q : ℕ)
    (x : C R (Fin n)) (hx : x ∈ supported R R {b | cechDegree b = q}) :
    (finProduct R n d).sign x = (-1 : R) ^ q • x := by
  classical
  rw [← x.sum_single, map_finsuppSum]
  change (∑ b ∈ x.support, _) = (-1 : R) ^ q • ∑ b ∈ x.support, single b (x b)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  rw [finProduct_sign_single, (mem_supported R x).mp hx hb]

theorem finProduct_sign_i (n : ℕ) (d : Fin n → ℕ) (x : H R d) :
    (finProduct R n d).sign ((finProduct R n d).i x) =
      (-1 : R) ^ cohomologyDegree d • (finProduct R n d).i x := by
  apply finProduct_sign_of_supported
  have h := (finProduct_degrees R n d).i (cohomologyDegree d) x
    ((mem_supported R x).mpr (by intro b hb; rfl))
  simpa only [add_zero, Nat.cast_inj] using h

theorem evenPart_lineI (d : ℕ) (x : LineH R d) :
    CechLine.evenPart (lineI R d x) = if d = 0 then lineI R d x else 0 := by
  by_cases hd : d = 0
  · subst d
    have hx : x.2 = 0 := by ext i; exact Fin.elim0 i
    simp [hx]
  · have hx : x.1 = 0 := by
      ext i
      have hi := i.isLt
      simp [hd] at hi
    simp [hd, hx]

theorem oddPart_lineI (d : ℕ) (x : LineH R d) :
    CechLine.oddPart (lineI R d x) = if d = 0 then 0 else lineI R d x := by
  by_cases hd : d = 0
  · subst d
    have hx : x.2 = 0 := by ext i; exact Fin.elim0 i
    simp [hx]
  · have hx : x.1 = 0 := by
      ext i
      have hi := i.isLt
      simp [hd] at hi
    simp [hd, hx]

section Tensor

theorem lineFree_i_apply (d : ℕ) (x : Fin (phi d) →₀ R) :
    (lineFree R d).i x = (lineBasisEquiv R).symm (lineI R d ((lineHBasisEquiv R d).symm x)) := rfl

theorem lineFree_p_apply (d : ℕ) (x : Basis →₀ R) :
    (lineFree R d).p x = lineHBasisEquiv R d (lineP R d (lineBasisEquiv R x)) := rfl

variable {A B D H K L : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  [AddCommGroup D] [Module R D] [AddCommGroup H] [Module R H]
  [AddCommGroup K] [Module R K] [AddCommGroup L] [Module R L]
  {a : GradedContraction R A H} {b : GradedContraction R B K}
  {c : GradedContraction R D L} (f : ChainPairing a b c)

theorem lineFreeTensorChainPairing_cup (d e : ℕ) (q : ℕ)
    (x : Fin (phi d) →₀ R) (y : Fin (phi e) →₀ R) (u : H) (v : K)
    (hu : a.sign (a.i u) = (-1 : R) ^ q • a.i u) :
    (lineFreeTensorChainPairing R f d e).cup (x ⊗ₜ[R] u) (y ⊗ₜ[R] v) =
      (-1 : R) ^ (q * lineCohomologyDegree e) •
        ((lineCyclePairing R d e).cup x y ⊗ₜ[R] f.cup u v) := by
  change (TensorProduct.map (lineFree R (d + e)).p c.p)
    ((TensorProduct.congr (lineBasisEquiv R).symm (.refl R D))
      (CechLine.tensorChainMul f d e
        ((TensorProduct.congr (lineBasisEquiv R).symm (.refl R A)).symm
          ((TensorProduct.map (lineFree R d).i a.i) (x ⊗ₜ[R] u)))
        ((TensorProduct.congr (lineBasisEquiv R).symm (.refl R B)).symm
          ((TensorProduct.map (lineFree R e).i b.i) (y ⊗ₜ[R] v))))) = _
  simp only [TensorProduct.map_tmul, TensorProduct.congr_symm,
    TensorProduct.congr_tmul, LinearEquiv.symm_symm, LinearEquiv.refl_symm, LinearEquiv.refl_apply,
    lineFree_i_apply, LinearEquiv.apply_symm_apply]
  rw [CechLine.tensorChainMul_tmul, evenPart_lineI, oddPart_lineI]
  rw [lineCyclePairing, CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup]
  by_cases he : e = 0
  · subst e
    simp only [↓reduceIte, CechLine.cup_zero_right, TensorProduct.zero_tmul,
      add_zero, lineCohomologyDegree, Nat.mul_zero, pow_zero, one_smul,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.map_tmul,
      lineFree_p_apply, LinearEquiv.apply_symm_apply]
    rfl
  · simp only [he, ↓reduceIte, CechLine.cup_zero_right, TensorProduct.zero_tmul,
      zero_add, hu, map_smul, LinearMap.smul_apply, TensorProduct.tmul_smul,
      lineCohomologyDegree, Nat.mul_one, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply, TensorProduct.map_tmul, lineFree_p_apply,
      LinearEquiv.apply_symm_apply]
    rfl

end Tensor

theorem finChainPairing_cup_eq (n : ℕ) (d e : Fin n → ℕ) :
    (finChainPairing R n d e).cup = (finCyclePairing R n d e).cup := by
  induction n with
  | zero =>
    apply Finsupp.lhom_ext
    intro x r
    apply Finsupp.lhom_ext
    intro y s
    simp only [finChainPairing, finCyclePairing]
    simp [finProduct, emptyChainPairing, emptyCyclePairing,
      ChainPairing.cup, ChainPairing.cycles, CyclePairing.cup, empty, emptyChainMul,
      emptyCohomologyCup, Finsupp.llift]
    simp only [← Finsupp.single_mul, Finsupp.mapDomain_single]
  | succ n ih =>
    apply (LinearMap.compl₁₂_inj
      (consEquiv R (fun i => Fin (phi (d i)))).surjective
      (consEquiv R (fun i => Fin (phi (e i)))).surjective).mp
    apply TensorProduct.ext'
    intro x u
    apply TensorProduct.ext'
    intro y v
    change (finChainPairing R (n + 1) d e).cup
      (consEquiv R _ (x ⊗ₜ[R] u)) (consEquiv R _ (y ⊗ₜ[R] v)) = _
    dsimp only [finChainPairing]
    rw [ChainPairing.congr_cup_apply]
    erw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    erw [lineFreeTensorChainPairing_cup R (finChainPairing R n (Fin.tail d) (Fin.tail e))
      (d 0) (e 0) (cohomologyDegree (Fin.tail d)) x y u v (finProduct_sign_i R n (Fin.tail d) u)]
    rw [ih]
    exact (finCyclePairing_cup_cons R d e x u y v).symm

/-- The existing product on chosen representatives agrees with descent of the full Čech chain product. -/
theorem chainPairing_cup_eq {V : Type*} [Fintype V] (d e : V → ℕ) :
    (chainPairing R d e).cup = cohomologyCup R d e := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  unfold chainPairing cohomologyCup cyclePairing
  rw [ChainPairing.congr_cup_apply, CyclePairing.congr_cup_apply, finChainPairing_cup_eq]

/-- Formula for the existing multi-vertex cohomology cup product using arbitrary cocycle representatives. -/
theorem cohomologyCup_chain_projection {V : Type*} [Fintype V] (d e : V → ℕ)
    {x y : C R V} (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0) :
    cohomologyCup R d e ((contraction R d).p x) ((contraction R e).p y) =
      (contraction R (d + e)).p (chainCup R d e x y) := by
  rw [← chainPairing_cup_eq]
  exact chainPairing_cup_projection R d e hx hy

theorem chainCup_projection_eq_zero_of_overlap {V : Type*} [Fintype V] (d e : V → ℕ)
    (v : V) (hd : 0 < d v) (he : 0 < e v) {x y : C R V}
    (hx : (contraction R d).d x = 0) (hy : (contraction R e).d y = 0) :
    (contraction R (d + e)).p (chainCup R d e x y) = 0 := by
  rw [← cohomologyCup_chain_projection R d e hx hy,
    cohomologyCup_eq_zero_of_overlap R d e v hd he]
  rfl

end BPFixedPoints.CechProduct
