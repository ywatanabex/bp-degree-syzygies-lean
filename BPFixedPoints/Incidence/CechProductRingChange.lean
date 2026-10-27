import BPFixedPoints.Incidence.CechProductCupLaws
import BPFixedPoints.Incidence.CechProductProjectionCoefficients

/-!
# Ring change for the product Čech state machinery

Every structure map of the product Čech contraction and the Čech chain product
has integer monomial coefficients. Hence coefficientwise application of a ring
homomorphism `f : R →+* R'` (`Finsupp.mapRange`) commutes with the inclusion,
the projection, the chain product and the cohomology cup product. The inclusion
is described monomial by monomial: a degree-zero state includes as the constant
section on both charts, a degree-one state as one Laurent gap monomial.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000

namespace BPFixedPoints.CechProduct

open Finsupp
open scoped TensorProduct

section Inclusion

variable (R : Type) [CommRing R]

/-- Monomials occurring with coefficient one in the inclusion of a one-vertex state: both
chart constants for a degree-zero state, one Laurent gap monomial for a degree-one state. -/
def lineInclusionMonomials (d : ℕ) (k : Fin (phi d)) : Finset Basis :=
  match (lineStateIndexEquiv d).symm k with
  | Sum.inl _ => {Sum.inl 0, Sum.inr (Sum.inl 0)}
  | Sum.inr j => {Sum.inr (Sum.inr (-(j : ℤ) - 1))}

/-- The one-vertex inclusion of a state basis vector is the sum of its inclusion monomials. -/
theorem lineFree_i_single (d : ℕ) (k : Fin (phi d)) (r : R) :
    (lineFree R d).i (single k r) = ∑ a ∈ lineInclusionMonomials d k, single a r := by
  rw [lineFree_i_apply]
  have hk : k = lineStateIndexEquiv d ((lineStateIndexEquiv d).symm k) := by simp
  unfold lineInclusionMonomials
  generalize (lineStateIndexEquiv d).symm k = s at hk
  subst hk
  rcases s with j | j
  · have hy : (lineHBasisEquiv R d).symm (single (lineStateIndexEquiv d (Sum.inl j)) r) =
        (single j r, 0) := by
      apply (lineHBasisEquiv R d).symm_apply_eq.mpr
      ext k
      rw [lineHBasisEquiv_apply]
      obtain ⟨t, rfl⟩ := (lineStateIndexEquiv d).surjective k
      rw [Equiv.symm_apply_apply, Finsupp.single_apply]
      simp only [(lineStateIndexEquiv d).injective.eq_iff]
      rcases t with t | t <;> simp [Finsupp.single_apply]
    dsimp only
    rw [hy]
    apply (lineBasisEquiv R).injective
    rw [LinearEquiv.apply_symm_apply, Finset.sum_pair (by simp), map_add, lineBasisEquiv_left,
      lineBasisEquiv_right]
    simp
  · have hy : (lineHBasisEquiv R d).symm (single (lineStateIndexEquiv d (Sum.inr j)) r) =
        (0, single j r) := by
      apply (lineHBasisEquiv R d).symm_apply_eq.mpr
      ext k
      rw [lineHBasisEquiv_apply]
      obtain ⟨t, rfl⟩ := (lineStateIndexEquiv d).surjective k
      rw [Equiv.symm_apply_apply, Finsupp.single_apply]
      simp only [(lineStateIndexEquiv d).injective.eq_iff]
      rcases t with t | t <;> simp [Finsupp.single_apply]
    dsimp only
    rw [hy]
    apply (lineBasisEquiv R).injective
    rw [LinearEquiv.apply_symm_apply, Finset.sum_singleton, lineBasisEquiv_overlap]
    simp only [lineI_apply, map_zero, CechLine.inclusionOne_single]
    rfl

/-- Coefficient of a monomial in the one-vertex inclusion of a state basis vector. -/
theorem lineFree_i_single_apply (d : ℕ) (k : Fin (phi d)) (r : R) (a : Basis) :
    (lineFree R d).i (single k r) a = if a ∈ lineInclusionMonomials d k then r else 0 := by
  rw [lineFree_i_single, Finset.sum_apply']
  simp only [Finsupp.single_apply, Finset.sum_ite_eq']

/-- Coefficient of a product monomial in the ordered finite-product inclusion of a state basis
vector: the coefficient is present exactly when every factor is an inclusion monomial. -/
theorem finProduct_i_single_apply (n : ℕ) (d : Fin n → ℕ) (κ : HBasis d) (r : R)
    (b : Fin n → Basis) :
    (finProduct R n d).i (single κ r) b =
      if ∀ i, b i ∈ lineInclusionMonomials (d i) (κ i) then r else 0 := by
  induction n with
  | zero =>
    change mapDomain (Equiv.ofUnique (Fin 0 → Basis) (HBasis d)).symm (single κ r) b = _
    rw [mapDomain_single, ite_eq_left (fun i => Fin.elim0 i)]
    have hb : (Equiv.ofUnique (Fin 0 → Basis) (HBasis d)).symm κ = b :=
      Subsingleton.elim _ _
    rw [hb, Finsupp.single_eq_same]
  | succ n ih =>
    rw [finProduct, GradedContraction.congr_i_apply, consEquiv_symm_single]
    change consEquiv R (fun _ : Fin (n + 1) => Basis)
      (TensorProduct.map (lineFree R (d 0)).i (finProduct R n (Fin.tail d)).i
        (single (κ 0) 1 ⊗ₜ[R] single (Fin.tail κ) r)) b = _
    rw [TensorProduct.map_tmul, consEquiv_tmul_coefficient, lineFree_i_single_apply, ih]
    simp only [Fin.forall_fin_succ, Fin.tail]
    split_ifs <;> simp_all

/-- Coefficient of a monomial in the product inclusion of a state basis vector. -/
theorem contraction_i_single_apply {V : Type} [Fintype V] (d : V → ℕ) (κ : HBasis d) (r : R)
    (b : V → Basis) :
    (contraction R d).i (single κ r) b =
      if ∀ v, b v ∈ lineInclusionMonomials (d v) (κ v) then r else 0 := by
  classical
  let e := (Fintype.equivFin V).symm
  let eb := e.arrowCongr (Equiv.refl Basis)
  let eh := Equiv.piCongrLeft (fun v => Fin (phi (d v))) e
  change mapDomain eb ((finProduct R (Fintype.card V) (fun i => d (e i))).i
    (mapDomain eh.symm (single κ r))) b = _
  rw [mapDomain_equiv_apply, mapDomain_single, finProduct_i_single_apply]
  have hiff : (∀ i, eb.symm b i ∈ lineInclusionMonomials (d (e i)) (eh.symm κ i)) ↔
      ∀ v, b v ∈ lineInclusionMonomials (d v) (κ v) := by
    change (∀ i, b (e i) ∈ lineInclusionMonomials (d (e i)) (eh.symm κ i)) ↔ _
    simp only [eh, Equiv.piCongrLeft_symm_apply]
    exact e.forall_congr_right (q := fun v => b v ∈ lineInclusionMonomials (d v) (κ v))
  exact if_congr hiff rfl rfl

/-- Coefficient formula for the product inclusion, the analogue of
`contraction_p_coefficient`: the coefficient of a monomial collects the state coordinates
whose inclusion contains it. -/
theorem contraction_i_coefficient {V : Type} [Fintype V] (d : V → ℕ) (x : H R d)
    (b : V → Basis) :
    (contraction R d).i x b =
      x.sum fun κ r => if ∀ v, b v ∈ lineInclusionMonomials (d v) (κ v) then r else 0 := by
  induction x using Finsupp.induction_linear with
  | zero => rw [map_zero, Finsupp.sum_zero_index]; rfl
  | add x y hx hy =>
    rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.sum_add_index']
    · intro κ
      exact ite_self 0
    · intro κ r s
      split_ifs <;> simp
  | single κ r =>
    rw [contraction_i_single_apply, Finsupp.sum_single_index (by exact ite_self 0)]

end Inclusion

section RingChange

variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {V : Type} [Fintype V]

/-- Coefficientwise ring change commutes with the product inclusion of states. -/
theorem contraction_i_mapRange (d : V → ℕ) (x : H R d) :
    (contraction R' d).i (mapRange f (map_zero f) x) =
      mapRange f (map_zero f) ((contraction R d).i x) := by
  ext b
  rw [contraction_i_coefficient, mapRange_apply, contraction_i_coefficient,
    Finsupp.sum_mapRange_index (by intro κ; exact ite_self 0), map_finsuppSum]
  apply Finsupp.sum_congr
  intro κ _
  rw [apply_ite f, map_zero]

/-- Coefficientwise ring change commutes with the product projection to states. -/
theorem contraction_p_mapRange (d : V → ℕ) (x : C R V) :
    (contraction R' d).p (mapRange f (map_zero f) x) =
      mapRange f (map_zero f) ((contraction R d).p x) := by
  ext κ
  rw [contraction_p_coefficient, mapRange_apply, mapRange_apply, contraction_p_coefficient]

/-- Coefficientwise ring change commutes with the full Čech chain product. -/
theorem chainCup_mapRange (d e : V → ℕ) (x y : C R V) :
    chainCup R' d e (mapRange f (map_zero f) x) (mapRange f (map_zero f) y) =
      mapRange f (map_zero f) (chainCup R d e x y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp only [mapRange_zero, map_zero, LinearMap.zero_apply]
  | add x x' hx hx' =>
    rw [mapRange_add (map_add f), map_add, LinearMap.add_apply, hx, hx', map_add,
      LinearMap.add_apply, mapRange_add (map_add f)]
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp only [mapRange_zero, map_zero]
    | add y y' hy hy' =>
      rw [mapRange_add (map_add f), map_add, hy, hy', map_add, mapRange_add (map_add f)]
    | single b s =>
      rw [mapRange_single, mapRange_single, chainCup_single, chainCup_single]
      cases cupBasis e a b with
      | none => simp only [Option.elim, mapRange_zero]
      | some z => simp only [Option.elim, mapRange_single, map_mul, map_pow, map_neg, map_one]

/-- Coefficientwise ring change commutes with the multi-vertex cohomology cup product. -/
theorem cohomologyCup_mapRange (d e : V → ℕ) (x : H R d) (y : H R e) :
    cohomologyCup R' d e (mapRange f (map_zero f) x) (mapRange f (map_zero f) y) =
      mapRange f (map_zero f) (cohomologyCup R d e x y) := by
  have hR := cohomologyCup_chain_projection R d e (contraction_d_i R d x)
    (contraction_d_i R e y)
  rw [contraction_p_i, contraction_p_i] at hR
  have hR' := cohomologyCup_chain_projection R' d e
    (contraction_d_i R' d (mapRange f (map_zero f) x))
    (contraction_d_i R' e (mapRange f (map_zero f) y))
  rw [contraction_p_i, contraction_p_i] at hR'
  rw [hR', hR, contraction_i_mapRange, contraction_i_mapRange, chainCup_mapRange,
    contraction_p_mapRange]

end RingChange

end BPFixedPoints.CechProduct
