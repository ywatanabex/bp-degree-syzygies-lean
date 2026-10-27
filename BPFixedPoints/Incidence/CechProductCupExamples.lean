import BPFixedPoints.Incidence.CechProductCup
import BPFixedPoints.Incidence.VertexProjectiveTwistThreeAcceptance

/-!
# Acceptance examples for the multi-vertex Čech state cup, with signs

The examples use twist vectors whose entries are zero or two, so every state module is free
of rank one. For two such twists that are never both positive at a vertex, the state cup of
basis states is the basis state of the sum with sign `(-1)^cupCrossings d e`. Here
`cupCrossings d e` counts vertex pairs `v, w` with the right twist positive at `v`, the left
twist positive at `w`, and `v` enumerated before `w`.

`cohomologyCup` orders the vertices by `Fintype.equivFin V`, which is chosen noncomputably.
Hence the absolute signs on `Fin 2` and `Fin 3` are stated with the enumeration sign
`twoVertexEnumerationSign` or `(-1)^threeVertexInversions`. The products for the fixed vertex
order of `Fin n` (`finCyclePairing`) give plus signs. Results independent of the enumeration:
the two orders on `Fin 2` differ by exactly −1, both bracketings on `Fin 3` agree, and the
zero-twist state is a two-sided unit. Twist sums are transported to the constant twist two by
`stateTwistCast`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace BPFixedPoints.CechProduct

open Finsupp GradedContraction
open scoped TensorProduct

variable (R : Type*) [CommRing R]

section Local

/-- A one-vertex state basis with one element has all its indices equal. -/
theorem cupExample_fin_eq_of_phi {k : ℕ} (hk : phi k = 1) (a b : Fin (phi k)) : a = b :=
  Fin.ext (by have ha := lt_of_lt_of_eq a.isLt hk; have hb := lt_of_lt_of_eq b.isLt hk; omega)

/-- The one-vertex cohomology unit is the constant state with coefficient one. -/
theorem cupExample_cohomologyCupUnit_eq :
    (CechLine.cohomologyCupUnit : LineH R 0) = (single ⟨0, by simp⟩ 1, 0) := by
  change (CechLine.projectionZero R 0 (single 0 1, single 0 1), CechLine.projectionOne R 0 0) = _
  rw [CechLine.projectionZero_zero_apply, single_eq_same, map_zero]

/-- In the free state basis, every twist-zero state is a multiple of the cohomology unit. -/
theorem cupExample_lineHBasisEquiv_zero_symm (a : Fin (phi 0)) (r : R) :
    (lineHBasisEquiv R 0).symm (single a r) = r • CechLine.cohomologyCupUnit := by
  apply (lineHBasisEquiv R 0).injective
  rw [LinearEquiv.apply_symm_apply, map_smul, cupExample_cohomologyCupUnit_eq]
  change single a r = r • mapDomain _ ((single _ 1 : CechLine.H0 R 0).sumElim 0)
  rw [sumElim_single_zero, mapDomain_single, smul_single, smul_eq_mul, mul_one]
  congr 1
  exact cupExample_fin_eq_of_phi rfl _ _

/-- The free basis vector of the one-vertex twist-zero state module is the cohomology unit. -/
theorem cupExample_lineHBasisEquiv_unit (a : Fin (phi 0)) :
    lineHBasisEquiv R 0 CechLine.cohomologyCupUnit = single a 1 := by
  rw [← one_smul R (CechLine.cohomologyCupUnit : LineH R 0),
    ← cupExample_lineHBasisEquiv_zero_symm, LinearEquiv.apply_symm_apply]

/-- Local products of basis states when at most one twist is nonzero and twists lie in {0,2}. -/
theorem cupExample_lineCup_single_one (d e : ℕ)
    (h : (d = 0 ∧ e = 0) ∨ (d = 2 ∧ e = 0) ∨ (d = 0 ∧ e = 2))
    (a : Fin (phi d)) (b : Fin (phi e)) (c : Fin (phi (d + e))) :
    (lineCyclePairing R d e).cup (single a 1) (single b 1) = single c 1 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rw [lineCyclePairing, CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup,
      cupExample_lineHBasisEquiv_zero_symm, cupExample_lineHBasisEquiv_zero_symm, one_smul,
      CechLine.cohomologyCup_unit_right]
    exact cupExample_lineHBasisEquiv_unit R c
  · rw [lineCyclePairing, CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup,
      cupExample_lineHBasisEquiv_zero_symm, one_smul, CechLine.cohomologyCup_unit_right]
    change lineHBasisEquiv R 2 ((lineHBasisEquiv R 2).symm (single a 1)) = single c 1
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    exact cupExample_fin_eq_of_phi rfl _ _
  · rw [lineCyclePairing, CyclePairing.congr_cup_apply, CechLine.cyclePairing_cup,
      cupExample_lineHBasisEquiv_zero_symm, one_smul,
      eq_of_heq (CechLine.cohomologyCup_unit_left 2 ((lineHBasisEquiv R 2).symm (single b 1)))]
    change lineHBasisEquiv R 2 ((lineHBasisEquiv R 2).symm (single b 1)) = single c 1
    rw [LinearEquiv.apply_symm_apply]
    congr 1
    exact cupExample_fin_eq_of_phi rfl _ _

/-- Local products of scaled basis states in the same twist pattern. -/
theorem cupExample_lineCup_single (d e : ℕ)
    (h : (d = 0 ∧ e = 0) ∨ (d = 2 ∧ e = 0) ∨ (d = 0 ∧ e = 2))
    (a : Fin (phi d)) (b : Fin (phi e)) (c : Fin (phi (d + e))) (r s : R) :
    (lineCyclePairing R d e).cup (single a r) (single b s) = single c (r * s) := by
  have ha : single a r = r • single a (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
  have hb : single b s = s • single b (1 : R) := by rw [smul_single, smul_eq_mul, mul_one]
  rw [ha, hb, map_smul, LinearMap.map_smul₂, cupExample_lineCup_single_one R d e h a b c,
    smul_single, smul_single, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]

end Local

section Crossings

/-- Koszul crossings in the vertex order of `Fin n`: pairs `i < j` whose right factor has
positive degree at `i` and whose left factor has positive degree at `j`. -/
def finCupCrossings (n : ℕ) (d e : Fin n → ℕ) : ℕ :=
  ∑ i, ∑ j, if i < j then lineCohomologyDegree (e i) * lineCohomologyDegree (d j) else 0

/-- No vertices, no crossings. -/
theorem finCupCrossings_zero (d e : Fin 0 → ℕ) : finCupCrossings 0 d e = 0 := by
  simp [finCupCrossings]

/-- The crossing count follows the head-and-tail recursion of `finCyclePairing`. -/
theorem finCupCrossings_succ (n : ℕ) (d e : Fin (n + 1) → ℕ) :
    finCupCrossings (n + 1) d e =
      cohomologyDegree (Fin.tail d) * lineCohomologyDegree (e 0) +
        finCupCrossings n (Fin.tail d) (Fin.tail e) := by
  simp only [finCupCrossings, Fin.sum_univ_succ, ite_false, zero_add,
    Fin.succ_pos, ite_true, Fin.not_lt_zero, Fin.succ_lt_succ_iff, cohomologyDegree,
    Finset.sum_mul, Fin.tail]
  congr 1
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- Koszul crossings for the enumeration `Fintype.equivFin V` that `cohomologyCup` uses. -/
noncomputable def cupCrossings {V : Type*} [Fintype V] (d e : V → ℕ) : ℕ :=
  ∑ v, ∑ w, if Fintype.equivFin V v < Fintype.equivFin V w then
    lineCohomologyDegree (e v) * lineCohomologyDegree (d w) else 0

/-- The enumerated crossing count is the `Fin` crossing count of the enumerated twists. -/
theorem cupCrossings_eq_fin {V : Type*} [Fintype V] (d e : V → ℕ) :
    cupCrossings d e = finCupCrossings (Fintype.card V)
      (fun i => d ((Fintype.equivFin V).symm i)) (fun i => e ((Fintype.equivFin V).symm i)) := by
  unfold cupCrossings finCupCrossings
  rw [← (Fintype.equivFin V).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← (Fintype.equivFin V).symm.sum_comp]
  simp only [Equiv.apply_symm_apply]

end Crossings

section Product

/-- The empty-vertex product of two scaled states is the product of the scalars. -/
theorem cupExample_emptyCup_single (d e : Fin 0 → ℕ) (a : HBasis d) (b : HBasis e)
    (c : HBasis (d + e)) (r s : R) :
    (finCyclePairing R 0 d e).cup (single a r) (single b s) = single c (r * s) := by
  change (empty R (d + e)).p ((empty R (d + e)).i
    (emptyCohomologyCup R d e (single a r) (single b s))) = _
  have hpi := LinearMap.congr_fun (empty R (d + e)).p_i
    (emptyCohomologyCup R d e (single a r) (single b s))
  rw [LinearMap.comp_apply, LinearMap.id_apply] at hpi
  rw [hpi]
  simp only [emptyCohomologyCup, Finsupp.llift_apply, Finsupp.lift_apply,
    sum_single_index, zero_smul, smul_single, smul_eq_mul, mul_one, LinearMap.smul_apply]
  rw [sum_single_index (single_zero _), smul_single, smul_eq_mul]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Product of basis states in the vertex order of `Fin n`, when every vertex carries the twist
pair (0,0), (2,0) or (0,2): the result is the basis state with the Koszul crossing sign. -/
theorem finCyclePairing_cup_single_of_zeroTwo (n : ℕ) (d e : Fin n → ℕ)
    (h : ∀ i, (d i = 0 ∧ e i = 0) ∨ (d i = 2 ∧ e i = 0) ∨ (d i = 0 ∧ e i = 2))
    (a : HBasis d) (b : HBasis e) (c : HBasis (d + e)) (r s : R) :
    (finCyclePairing R n d e).cup (single a r) (single b s) =
      single c ((-1) ^ finCupCrossings n d e * (r * s)) := by
  induction n with
  | zero =>
    rw [finCupCrossings_zero, pow_zero, one_mul]
    exact cupExample_emptyCup_single R d e a b c r s
  | succ n ih =>
    have ha : single a r = consEquiv R (fun i => Fin (phi (d i)))
        (single (a 0) 1 ⊗ₜ[R] single (Fin.tail a) r) := by
      rw [consEquiv_single_tmul_single, one_mul, Fin.cons_self_tail]
    have hb : single b s = consEquiv R (fun i => Fin (phi (e i)))
        (single (b 0) 1 ⊗ₜ[R] single (Fin.tail b) s) := by
      rw [consEquiv_single_tmul_single, one_mul, Fin.cons_self_tail]
    rw [ha, hb, finCyclePairing_cup_cons,
      cupExample_lineCup_single R (d 0) (e 0) (h 0) (a 0) (b 0) (c 0) 1 1,
      ih (Fin.tail d) (Fin.tail e) (fun i => h i.succ) (Fin.tail a) (Fin.tail b) (Fin.tail c),
      TensorProduct.smul_tmul', smul_single, consEquiv_single_tmul_single, Fin.cons_self_tail,
      finCupCrossings_succ, pow_add, smul_eq_mul]
    congr 1
    ring

/-- A state basis whose every vertex factor has one element has all its indices equal. -/
theorem cupExample_hBasis_eq {V : Type*} {d : V → ℕ} (hd : ∀ v, phi (d v) = 1)
    (a b : HBasis d) : a = b :=
  funext fun v => cupExample_fin_eq_of_phi (hd v) _ _

/-- The twist pairs (0,0), (2,0), (0,2) give a one-element local state basis for the sum. -/
theorem cupExample_phi_add_of_zeroTwo {d e : ℕ}
    (h : (d = 0 ∧ e = 0) ∨ (d = 2 ∧ e = 0) ∨ (d = 0 ∧ e = 2)) : phi (d + e) = 1 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- Product of basis states for `cohomologyCup` on any finite vertex set, when every vertex
carries the twist pair (0,0), (2,0) or (0,2). The sign counts Koszul crossings in the
enumeration `Fintype.equivFin V` used to build the product. -/
theorem cohomologyCup_single_of_zeroTwo {V : Type*} [Fintype V] (d e : V → ℕ)
    (h : ∀ v, (d v = 0 ∧ e v = 0) ∨ (d v = 2 ∧ e v = 0) ∨ (d v = 0 ∧ e v = 2))
    (a : HBasis d) (b : HBasis e) (c : HBasis (d + e)) (r s : R) :
    cohomologyCup R d e (single a r) (single b s) =
      single c ((-1) ^ cupCrossings d e * (r * s)) := by
  rw [cohomologyCup, cyclePairing, CyclePairing.congr_cup_apply]
  simp only [mapDomain.linearEquiv_symm, mapDomain.coe_linearEquiv, mapDomain_single]
  rw [finCyclePairing_cup_single_of_zeroTwo R _ _ _ (fun i => h ((Fintype.equivFin V).symm i))
      _ _ (fun i => c ((Fintype.equivFin V).symm i)) r s,
    mapDomain_single, cupCrossings_eq_fin]
  congr 1
  exact cupExample_hBasis_eq (fun v => cupExample_phi_add_of_zeroTwo (h v)) _ _

end Product

section Generators

/-- The unique state index of a twist vector whose entries are zero or two. -/
def zeroTwoStateIndex {V : Type*} (d : V → ℕ) (hd : ∀ v, d v = 0 ∨ d v = 2) : HBasis d :=
  fun v => ⟨0, by rcases hd v with h | h <;> rw [h] <;> exact Nat.one_pos⟩

/-- The basis state with coefficient `r` of a twist vector whose entries are zero or two. -/
noncomputable def zeroTwoState {V : Type*} (d : V → ℕ) (hd : ∀ v, d v = 0 ∨ d v = 2)
    (r : R) : H R d :=
  single (zeroTwoStateIndex d hd) r

/-- Twists zero and two have a one-element local state basis. -/
theorem phi_eq_one_of_zeroTwo {k : ℕ} (hk : k = 0 ∨ k = 2) : phi k = 1 := by
  rcases hk with rfl | rfl <;> rfl

/-- Every state of a twist vector with entries zero or two is a multiple of the basis state. -/
theorem eq_zeroTwoState {V : Type*} (d : V → ℕ) (hd : ∀ v, d v = 0 ∨ d v = 2) (x : H R d) :
    x = zeroTwoState R d hd (x (zeroTwoStateIndex d hd)) := by
  ext κ
  rw [zeroTwoState, cupExample_hBasis_eq (fun v => phi_eq_one_of_zeroTwo (hd v)) κ
    (zeroTwoStateIndex d hd), single_eq_same]

/-- Transport of states along an equality of twist vectors. -/
noncomputable def stateTwistCast {V : Type*} {d d' : V → ℕ} (h : d = d') :
    H R d ≃ₗ[R] H R d' :=
  mapDomain.linearEquiv R R (Equiv.cast (congrArg HBasis h))

/-- Transport of a basis state to a twist vector with a one-element state basis. -/
theorem stateTwistCast_single {V : Type*} {d d' : V → ℕ} (h : d = d')
    (hd' : ∀ v, phi (d' v) = 1) (κ : HBasis d) (κ' : HBasis d') (r : R) :
    stateTwistCast R h (single κ r) = single κ' r := by
  rw [stateTwistCast, mapDomain.coe_linearEquiv, mapDomain_single]
  congr 1
  exact cupExample_hBasis_eq hd' _ _

/-- The `Fin`-order product of basis states, transported to a twist with a one-element basis. -/
theorem stateTwistCast_finCup_single_of_zeroTwo (n : ℕ) (d e d' : Fin n → ℕ)
    (h : ∀ i, (d i = 0 ∧ e i = 0) ∨ (d i = 2 ∧ e i = 0) ∨ (d i = 0 ∧ e i = 2))
    (hsum : d + e = d') (hd' : ∀ i, phi (d' i) = 1)
    (a : HBasis d) (b : HBasis e) (κ : HBasis d') (r s : R) :
    stateTwistCast R hsum ((finCyclePairing R n d e).cup (single a r) (single b s)) =
      single κ ((-1) ^ finCupCrossings n d e * (r * s)) := by
  rw [finCyclePairing_cup_single_of_zeroTwo R n d e h a b
      (cast (congrArg HBasis hsum).symm κ) r s,
    stateTwistCast_single R hsum hd' _ κ]

/-- The product of basis states, transported to a twist with a one-element basis. -/
theorem stateTwistCast_cohomologyCup_single_of_zeroTwo {V : Type*} [Fintype V] (d e d' : V → ℕ)
    (h : ∀ v, (d v = 0 ∧ e v = 0) ∨ (d v = 2 ∧ e v = 0) ∨ (d v = 0 ∧ e v = 2))
    (hsum : d + e = d') (hd' : ∀ v, phi (d' v) = 1)
    (a : HBasis d) (b : HBasis e) (κ : HBasis d') (r s : R) :
    stateTwistCast R hsum (cohomologyCup R d e (single a r) (single b s)) =
      single κ ((-1) ^ cupCrossings d e * (r * s)) := by
  rw [cohomologyCup_single_of_zeroTwo R d e h a b (cast (congrArg HBasis hsum).symm κ) r s,
    stateTwistCast_single R hsum hd' _ κ]

end Generators

section TwoVertex

/-- The twist sum (2,0)+(0,2) is the constant twist two. -/
theorem twoVertex_add : (![2, 0] + ![0, 2] : Fin 2 → ℕ) = fun _ => 2 := by
  funext v
  fin_cases v <;> rfl

/-- The twist sum (0,2)+(2,0) is the constant twist two. -/
theorem twoVertex_add_swap : (![0, 2] + ![2, 0] : Fin 2 → ℕ) = fun _ => 2 := by
  funext v
  fin_cases v <;> rfl

/-- The entries of the twist (2,0) are zero or two. -/
theorem twoVertexLeft_zeroTwo :
    ∀ v, (![2, 0] : Fin 2 → ℕ) v = 0 ∨ (![2, 0] : Fin 2 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The entries of the twist (0,2) are zero or two. -/
theorem twoVertexRight_zeroTwo :
    ∀ v, (![0, 2] : Fin 2 → ℕ) v = 0 ∨ (![0, 2] : Fin 2 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The degree-one state of twist (2,0): the H1 factor at vertex 0 and the H0 factor at vertex 1. -/
noncomputable def twoVertexLeftState (r : R) : H R (![2, 0] : Fin 2 → ℕ) :=
  zeroTwoState R _ twoVertexLeft_zeroTwo r

/-- The degree-one state of twist (0,2): the H0 factor at vertex 0 and the H1 factor at vertex 1. -/
noncomputable def twoVertexRightState (r : R) : H R (![0, 2] : Fin 2 → ℕ) :=
  zeroTwoState R _ twoVertexRight_zeroTwo r

/-- The sign of the enumeration of `Fin 2` chosen by `Fintype.equivFin`: one when it keeps the
vertex order, minus one when it swaps the two vertices. -/
noncomputable def twoVertexEnumerationSign : R :=
  if Fintype.equivFin (Fin 2) 0 < Fintype.equivFin (Fin 2) 1 then 1 else -1

/-- The enumeration sign is one or minus one. -/
theorem twoVertexEnumerationSign_eq_or :
    twoVertexEnumerationSign R = 1 ∨ twoVertexEnumerationSign R = -1 := by
  unfold twoVertexEnumerationSign
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The two-vertex left-right crossing count: one exactly when the enumeration swaps the
vertices. -/
theorem cupCrossings_twoVertex :
    cupCrossings (![2, 0] : Fin 2 → ℕ) ![0, 2] =
      if Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0 then 1 else 0 := by
  simp [cupCrossings, Fin.sum_univ_two, lineCohomologyDegree]

/-- The two-vertex right-left crossing count: one exactly when the enumeration keeps the order. -/
theorem cupCrossings_twoVertex_swap :
    cupCrossings (![0, 2] : Fin 2 → ℕ) ![2, 0] =
      if Fintype.equivFin (Fin 2) 0 < Fintype.equivFin (Fin 2) 1 then 1 else 0 := by
  simp [cupCrossings, Fin.sum_univ_two, lineCohomologyDegree]

/-- Every vertex carries the twist pair (2,0) or (0,2). -/
theorem twoVertex_pattern : ∀ v,
    ((![2, 0] : Fin 2 → ℕ) v = 0 ∧ (![0, 2] : Fin 2 → ℕ) v = 0) ∨
    ((![2, 0] : Fin 2 → ℕ) v = 2 ∧ (![0, 2] : Fin 2 → ℕ) v = 0) ∨
    ((![2, 0] : Fin 2 → ℕ) v = 0 ∧ (![0, 2] : Fin 2 → ℕ) v = 2) := by
  intro v
  fin_cases v <;> simp

/-- Every vertex carries the twist pair (0,2) or (2,0). -/
theorem twoVertex_pattern_swap : ∀ v,
    ((![0, 2] : Fin 2 → ℕ) v = 0 ∧ (![2, 0] : Fin 2 → ℕ) v = 0) ∨
    ((![0, 2] : Fin 2 → ℕ) v = 2 ∧ (![2, 0] : Fin 2 → ℕ) v = 0) ∨
    ((![0, 2] : Fin 2 → ℕ) v = 0 ∧ (![2, 0] : Fin 2 → ℕ) v = 2) := by
  intro v
  fin_cases v <;> simp

/-- In the vertex order 0 < 1, the product (2,0) ∪ (0,2) of the degree-one states is plus the
degree-two generator. -/
theorem twoVertex_finCup (r s : R) :
    stateTwistCast R twoVertex_add ((finCyclePairing R 2 ![2, 0] ![0, 2]).cup
      (twoVertexLeftState R r) (twoVertexRightState R s)) =
        single (fun _ => gapZero) (r * s) := by
  rw [twoVertexLeftState, twoVertexRightState, zeroTwoState, zeroTwoState,
    stateTwistCast_finCup_single_of_zeroTwo R 2 _ _ _ twoVertex_pattern twoVertex_add
      (fun _ => rfl) _ _ (fun _ => gapZero) r s]
  congr 1
  simp [finCupCrossings, Fin.sum_univ_two, lineCohomologyDegree]

/-- In the vertex order 0 < 1, the reversed product (0,2) ∪ (2,0) is minus the generator. -/
theorem twoVertex_finCup_swap (r s : R) :
    stateTwistCast R twoVertex_add_swap ((finCyclePairing R 2 ![0, 2] ![2, 0]).cup
      (twoVertexRightState R s) (twoVertexLeftState R r)) =
        single (fun _ => gapZero) (-(r * s)) := by
  rw [twoVertexLeftState, twoVertexRightState, zeroTwoState, zeroTwoState,
    stateTwistCast_finCup_single_of_zeroTwo R 2 _ _ _ twoVertex_pattern_swap twoVertex_add_swap
      (fun _ => rfl) _ _ (fun _ => gapZero) s r]
  congr 1
  simp [finCupCrossings, Fin.sum_univ_two, lineCohomologyDegree, mul_comm]

/-- In the vertex order 0 < 1, the two orders give different states whenever two is nonzero. -/
theorem twoVertex_finCup_ne_swap (h2 : (2 : R) ≠ 0) :
    stateTwistCast R twoVertex_add ((finCyclePairing R 2 ![2, 0] ![0, 2]).cup
      (twoVertexLeftState R 1) (twoVertexRightState R 1)) ≠
    stateTwistCast R twoVertex_add_swap ((finCyclePairing R 2 ![0, 2] ![2, 0]).cup
      (twoVertexRightState R 1) (twoVertexLeftState R 1)) := by
  rw [twoVertex_finCup, twoVertex_finCup_swap]
  intro h
  apply h2
  linear_combination single_injective _ h

/-- The sign `(-1)^crossings` of the left-right product is the enumeration sign. -/
theorem neg_one_pow_cupCrossings_twoVertex :
    (-1 : R) ^ cupCrossings (![2, 0] : Fin 2 → ℕ) ![0, 2] = twoVertexEnumerationSign R := by
  have hne : Fintype.equivFin (Fin 2) 0 ≠ Fintype.equivFin (Fin 2) 1 :=
    (Fintype.equivFin (Fin 2)).injective.ne (by simp)
  rw [cupCrossings_twoVertex, twoVertexEnumerationSign]
  by_cases h10 : Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0
  · rw [ite_eq_left h10, ite_eq_right (lt_asymm h10), pow_one]
  · rw [ite_eq_right h10, ite_eq_left (lt_of_le_of_ne (not_lt.mp h10) hne), pow_zero]

/-- The sign `(-1)^crossings` of the right-left product is minus the enumeration sign. -/
theorem neg_one_pow_cupCrossings_twoVertex_swap :
    (-1 : R) ^ cupCrossings (![0, 2] : Fin 2 → ℕ) ![2, 0] = -twoVertexEnumerationSign R := by
  have hne : Fintype.equivFin (Fin 2) 0 ≠ Fintype.equivFin (Fin 2) 1 :=
    (Fintype.equivFin (Fin 2)).injective.ne (by simp)
  rw [cupCrossings_twoVertex_swap, twoVertexEnumerationSign]
  by_cases h01 : Fintype.equivFin (Fin 2) 0 < Fintype.equivFin (Fin 2) 1
  · rw [ite_eq_left h01, ite_eq_left h01, pow_one]
  · rw [ite_eq_right h01, ite_eq_right h01, pow_zero, neg_neg]

/-- E1: the state cup (2,0) ∪ (0,2) of the degree-one states is the enumeration sign times the
degree-two generator of the constant twist two. -/
theorem twoVertex_cup (r s : R) :
    stateTwistCast R twoVertex_add (cohomologyCup R ![2, 0] ![0, 2]
      (twoVertexLeftState R r) (twoVertexRightState R s)) =
        single (fun _ => gapZero) (twoVertexEnumerationSign R * (r * s)) := by
  rw [twoVertexLeftState, twoVertexRightState, zeroTwoState, zeroTwoState,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R _ _ _ twoVertex_pattern twoVertex_add
      (fun _ => rfl) _ _ (fun _ => gapZero) r s, neg_one_pow_cupCrossings_twoVertex]

/-- E1, reversed order: (0,2) ∪ (2,0) is minus the enumeration sign times the generator. -/
theorem twoVertex_cup_swap (r s : R) :
    stateTwistCast R twoVertex_add_swap (cohomologyCup R ![0, 2] ![2, 0]
      (twoVertexRightState R s) (twoVertexLeftState R r)) =
        single (fun _ => gapZero) (-(twoVertexEnumerationSign R * (r * s))) := by
  rw [twoVertexLeftState, twoVertexRightState, zeroTwoState, zeroTwoState,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R _ _ _ twoVertex_pattern_swap
      twoVertex_add_swap (fun _ => rfl) _ _ (fun _ => gapZero) s r,
    neg_one_pow_cupCrossings_twoVertex_swap, neg_mul, mul_comm s r]

/-- E1, graded commutativity in degree 1×1: the two orders differ by exactly the sign −1. -/
theorem twoVertex_cup_swap_eq_neg (r s : R) :
    stateTwistCast R twoVertex_add_swap (cohomologyCup R ![0, 2] ![2, 0]
      (twoVertexRightState R s) (twoVertexLeftState R r)) =
    -stateTwistCast R twoVertex_add (cohomologyCup R ![2, 0] ![0, 2]
      (twoVertexLeftState R r) (twoVertexRightState R s)) := by
  rw [twoVertex_cup, twoVertex_cup_swap, single_neg]

/-- E1: whenever two is nonzero in the coefficient ring, the two orders give different states,
so the sign is detected and not only its reduction mod two. -/
theorem twoVertex_cup_ne_swap (h2 : (2 : R) ≠ 0) :
    stateTwistCast R twoVertex_add (cohomologyCup R ![2, 0] ![0, 2]
      (twoVertexLeftState R 1) (twoVertexRightState R 1)) ≠
    stateTwistCast R twoVertex_add_swap (cohomologyCup R ![0, 2] ![2, 0]
      (twoVertexRightState R 1) (twoVertexLeftState R 1)) := by
  rw [twoVertex_cup, twoVertex_cup_swap]
  intro h
  have hε := single_injective _ h
  apply h2
  rcases twoVertexEnumerationSign_eq_or R with he | he <;> rw [he] at hε
  · linear_combination hε
  · linear_combination -hε

/-- E1 over the integers: the two orders give different states. -/
theorem twoVertex_cup_ne_swap_int :
    stateTwistCast ℤ twoVertex_add (cohomologyCup ℤ ![2, 0] ![0, 2]
      (twoVertexLeftState ℤ 1) (twoVertexRightState ℤ 1)) ≠
    stateTwistCast ℤ twoVertex_add_swap (cohomologyCup ℤ ![0, 2] ![2, 0]
      (twoVertexRightState ℤ 1) (twoVertexLeftState ℤ 1)) :=
  twoVertex_cup_ne_swap ℤ two_ne_zero

end TwoVertex

section ThreeVertex

/-- Number of vertex pairs whose order is reversed by the enumeration `Fintype.equivFin (Fin 3)`. -/
noncomputable def threeVertexInversions : ℕ :=
  (if Fintype.equivFin (Fin 3) 1 < Fintype.equivFin (Fin 3) 0 then 1 else 0) +
  (if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 0 then 1 else 0) +
  (if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 1 then 1 else 0)

/-- Crossings of x ∪ y for the twists (2,0,0) and (0,2,0). -/
theorem cupCrossings_threeVertex_xy : cupCrossings (![2, 0, 0] : Fin 3 → ℕ) ![0, 2, 0] =
    if Fintype.equivFin (Fin 3) 1 < Fintype.equivFin (Fin 3) 0 then 1 else 0 := by
  simp [cupCrossings, Fin.sum_univ_three, lineCohomologyDegree]

/-- Crossings of (x ∪ y) ∪ z for the twists (2,0,0)+(0,2,0) and (0,0,2). -/
theorem cupCrossings_threeVertex_xy_z :
    cupCrossings ((![2, 0, 0] : Fin 3 → ℕ) + ![0, 2, 0]) ![0, 0, 2] =
      (if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 0 then 1 else 0) +
      (if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 1 then 1 else 0) := by
  simp [cupCrossings, Fin.sum_univ_three, lineCohomologyDegree]

/-- Crossings of y ∪ z for the twists (0,2,0) and (0,0,2). -/
theorem cupCrossings_threeVertex_yz : cupCrossings (![0, 2, 0] : Fin 3 → ℕ) ![0, 0, 2] =
    if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 1 then 1 else 0 := by
  simp [cupCrossings, Fin.sum_univ_three, lineCohomologyDegree]

/-- Crossings of x ∪ (y ∪ z) for the twists (2,0,0) and (0,2,0)+(0,0,2). -/
theorem cupCrossings_threeVertex_x_yz :
    cupCrossings (![2, 0, 0] : Fin 3 → ℕ) (![0, 2, 0] + ![0, 0, 2]) =
      (if Fintype.equivFin (Fin 3) 1 < Fintype.equivFin (Fin 3) 0 then 1 else 0) +
      (if Fintype.equivFin (Fin 3) 2 < Fintype.equivFin (Fin 3) 0 then 1 else 0) := by
  simp [cupCrossings, Fin.sum_univ_three, lineCohomologyDegree]

/-- The left-bracketed twist sum is the constant twist two. -/
theorem threeVertex_add_left :
    ((![2, 0, 0] : Fin 3 → ℕ) + ![0, 2, 0]) + ![0, 0, 2] = fun _ => 2 := by
  funext v
  fin_cases v <;> rfl

/-- The right-bracketed twist sum is the constant twist two. -/
theorem threeVertex_add_right :
    (![2, 0, 0] : Fin 3 → ℕ) + (![0, 2, 0] + ![0, 0, 2]) = fun _ => 2 := by
  funext v
  fin_cases v <;> rfl

/-- The entries of the twist (2,0,0) are zero or two. -/
theorem threeVertexX_zeroTwo :
    ∀ v, (![2, 0, 0] : Fin 3 → ℕ) v = 0 ∨ (![2, 0, 0] : Fin 3 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The entries of the twist (0,2,0) are zero or two. -/
theorem threeVertexY_zeroTwo :
    ∀ v, (![0, 2, 0] : Fin 3 → ℕ) v = 0 ∨ (![0, 2, 0] : Fin 3 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The entries of the twist (0,0,2) are zero or two. -/
theorem threeVertexZ_zeroTwo :
    ∀ v, (![0, 0, 2] : Fin 3 → ℕ) v = 0 ∨ (![0, 0, 2] : Fin 3 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The entries of the twist (2,0,0)+(0,2,0) are zero or two. -/
theorem threeVertexXY_zeroTwo : ∀ v : Fin 3, (![2, 0, 0] + ![0, 2, 0] : Fin 3 → ℕ) v = 0 ∨
    (![2, 0, 0] + ![0, 2, 0] : Fin 3 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The entries of the twist (0,2,0)+(0,0,2) are zero or two. -/
theorem threeVertexYZ_zeroTwo : ∀ v : Fin 3, (![0, 2, 0] + ![0, 0, 2] : Fin 3 → ℕ) v = 0 ∨
    (![0, 2, 0] + ![0, 0, 2] : Fin 3 → ℕ) v = 2 := by
  intro v
  fin_cases v <;> simp

/-- The degree-one state x of twist (2,0,0). -/
noncomputable def threeVertexX (r : R) : H R (![2, 0, 0] : Fin 3 → ℕ) :=
  zeroTwoState R _ threeVertexX_zeroTwo r

/-- The degree-one state y of twist (0,2,0). -/
noncomputable def threeVertexY (r : R) : H R (![0, 2, 0] : Fin 3 → ℕ) :=
  zeroTwoState R _ threeVertexY_zeroTwo r

/-- The degree-one state z of twist (0,0,2). -/
noncomputable def threeVertexZ (r : R) : H R (![0, 0, 2] : Fin 3 → ℕ) :=
  zeroTwoState R _ threeVertexZ_zeroTwo r

/-- E2, left bracketing: (x ∪ y) ∪ z is `(-1)^inversions` times the degree-three generator. -/
theorem threeVertex_cup_left (r s t : R) :
    stateTwistCast R threeVertex_add_left
      (cohomologyCup R _ ![0, 0, 2]
        (cohomologyCup R ![2, 0, 0] ![0, 2, 0] (threeVertexX R r) (threeVertexY R s))
        (threeVertexZ R t)) =
      single (fun _ => gapZero) ((-1) ^ threeVertexInversions * (r * s * t)) := by
  rw [threeVertexX, threeVertexY, threeVertexZ, zeroTwoState, zeroTwoState, zeroTwoState,
    cohomologyCup_single_of_zeroTwo R _ _ (by intro v; fin_cases v <;> simp) _ _
      (zeroTwoStateIndex _ threeVertexXY_zeroTwo) r s,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R _ _ _
      (by intro v; fin_cases v <;> simp) threeVertex_add_left (fun _ => rfl) _ _
      (fun _ => gapZero), cupCrossings_threeVertex_xy, cupCrossings_threeVertex_xy_z,
    threeVertexInversions]
  congr 1
  simp only [pow_add]
  ring

/-- E2, right bracketing: x ∪ (y ∪ z) is `(-1)^inversions` times the degree-three generator. -/
theorem threeVertex_cup_right (r s t : R) :
    stateTwistCast R threeVertex_add_right
      (cohomologyCup R ![2, 0, 0] _ (threeVertexX R r)
        (cohomologyCup R ![0, 2, 0] ![0, 0, 2] (threeVertexY R s) (threeVertexZ R t))) =
      single (fun _ => gapZero) ((-1) ^ threeVertexInversions * (r * s * t)) := by
  rw [threeVertexX, threeVertexY, threeVertexZ, zeroTwoState, zeroTwoState, zeroTwoState,
    cohomologyCup_single_of_zeroTwo R _ _ (by intro v; fin_cases v <;> simp) _ _
      (zeroTwoStateIndex _ threeVertexYZ_zeroTwo) s t,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R _ _ _
      (by intro v; fin_cases v <;> simp) threeVertex_add_right (fun _ => rfl) _ _
      (fun _ => gapZero), cupCrossings_threeVertex_yz, cupCrossings_threeVertex_x_yz,
    threeVertexInversions]
  congr 1
  simp only [pow_add]
  ring

/-- E2: the two bracketings of the triple product agree after transport to the constant
twist two. -/
theorem threeVertex_cup_assoc (r s t : R) :
    stateTwistCast R threeVertex_add_left
      (cohomologyCup R _ ![0, 0, 2]
        (cohomologyCup R ![2, 0, 0] ![0, 2, 0] (threeVertexX R r) (threeVertexY R s))
        (threeVertexZ R t)) =
    stateTwistCast R threeVertex_add_right
      (cohomologyCup R ![2, 0, 0] _ (threeVertexX R r)
        (cohomologyCup R ![0, 2, 0] ![0, 0, 2] (threeVertexY R s) (threeVertexZ R t))) := by
  rw [threeVertex_cup_left, threeVertex_cup_right]

/-- In the vertex order 0 < 1 < 2 the left bracketing (x ∪ y) ∪ z is plus the generator. -/
theorem threeVertex_finCup_left (r s t : R) :
    stateTwistCast R threeVertex_add_left
      ((finCyclePairing R 3 _ ![0, 0, 2]).cup
        ((finCyclePairing R 3 ![2, 0, 0] ![0, 2, 0]).cup (threeVertexX R r) (threeVertexY R s))
        (threeVertexZ R t)) =
      single (fun _ => gapZero) (r * s * t) := by
  rw [threeVertexX, threeVertexY, threeVertexZ, zeroTwoState, zeroTwoState, zeroTwoState,
    finCyclePairing_cup_single_of_zeroTwo R 3 _ _ (by intro v; fin_cases v <;> simp) _ _
      (zeroTwoStateIndex _ threeVertexXY_zeroTwo) r s,
    stateTwistCast_finCup_single_of_zeroTwo R 3 _ _ _
      (by intro v; fin_cases v <;> simp) threeVertex_add_left (fun _ => rfl) _ _
      (fun _ => gapZero)]
  congr 1
  simp [finCupCrossings, Fin.sum_univ_three, lineCohomologyDegree]

/-- In the vertex order 0 < 1 < 2 the right bracketing x ∪ (y ∪ z) is plus the generator. -/
theorem threeVertex_finCup_right (r s t : R) :
    stateTwistCast R threeVertex_add_right
      ((finCyclePairing R 3 ![2, 0, 0] _).cup (threeVertexX R r)
        ((finCyclePairing R 3 ![0, 2, 0] ![0, 0, 2]).cup (threeVertexY R s) (threeVertexZ R t))) =
      single (fun _ => gapZero) (r * s * t) := by
  rw [threeVertexX, threeVertexY, threeVertexZ, zeroTwoState, zeroTwoState, zeroTwoState,
    finCyclePairing_cup_single_of_zeroTwo R 3 _ _ (by intro v; fin_cases v <;> simp) _ _
      (zeroTwoStateIndex _ threeVertexYZ_zeroTwo) s t,
    stateTwistCast_finCup_single_of_zeroTwo R 3 _ _ _
      (by intro v; fin_cases v <;> simp) threeVertex_add_right (fun _ => rfl) _ _
      (fun _ => gapZero)]
  congr 1
  simp [finCupCrossings, Fin.sum_univ_three, lineCohomologyDegree]
  ring

/-- The sign `(-1)^inversions` of the three-vertex enumeration is one or minus one. -/
theorem neg_one_pow_threeVertexInversions_eq_or :
    (-1 : R) ^ threeVertexInversions = 1 ∨ (-1 : R) ^ threeVertexInversions = -1 := by
  rcases Nat.even_or_odd threeVertexInversions with h | h
  · exact Or.inl h.neg_one_pow
  · exact Or.inr h.neg_one_pow

end ThreeVertex

section Unit

/-- The degree-zero state of the zero twist: the H0 factor at every vertex. -/
noncomputable def zeroTwistState {V : Type*} (r : R) : H R (0 : V → ℕ) :=
  zeroTwoState R 0 (fun _ => Or.inl rfl) r

/-- A zero left twist produces no crossings. -/
theorem cupCrossings_zero_left {V : Type*} [Fintype V] (e : V → ℕ) : cupCrossings 0 e = 0 := by
  simp [cupCrossings, lineCohomologyDegree]

/-- A zero right twist produces no crossings. -/
theorem cupCrossings_zero_right {V : Type*} [Fintype V] (d : V → ℕ) : cupCrossings d 0 = 0 := by
  simp [cupCrossings, lineCohomologyDegree]

/-- E3, left unit: for twists with entries zero or two, the cup with the degree-zero state of
the zero twist on the left is scalar multiplication, after transport along `0 + d = d`. -/
theorem cohomologyCup_zeroTwistState_left {V : Type*} [Fintype V] (d : V → ℕ)
    (hd : ∀ v, d v = 0 ∨ d v = 2) (r : R) (x : H R d) :
    stateTwistCast R (zero_add d) (cohomologyCup R 0 d (zeroTwistState R r) x) = r • x := by
  rw [eq_zeroTwoState R d hd x, zeroTwistState, zeroTwoState, zeroTwoState,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R 0 d d
      (fun v => (hd v).elim (fun h => Or.inl ⟨rfl, h⟩) (fun h => Or.inr (Or.inr ⟨rfl, h⟩)))
      (zero_add d) (fun v => phi_eq_one_of_zeroTwo (hd v)) _ _ (zeroTwoStateIndex d hd),
    cupCrossings_zero_left, pow_zero, one_mul, smul_single, smul_eq_mul]

/-- E3, right unit: the cup with the degree-zero state of the zero twist on the right is scalar
multiplication, after transport along `d + 0 = d`. -/
theorem cohomologyCup_zeroTwistState_right {V : Type*} [Fintype V] (d : V → ℕ)
    (hd : ∀ v, d v = 0 ∨ d v = 2) (r : R) (x : H R d) :
    stateTwistCast R (add_zero d) (cohomologyCup R d 0 x (zeroTwistState R r)) = r • x := by
  rw [eq_zeroTwoState R d hd x, zeroTwistState, zeroTwoState, zeroTwoState,
    stateTwistCast_cohomologyCup_single_of_zeroTwo R d 0 d
      (fun v => (hd v).elim (fun h => Or.inl ⟨h, rfl⟩) (fun h => Or.inr (Or.inl ⟨h, rfl⟩)))
      (add_zero d) (fun v => phi_eq_one_of_zeroTwo (hd v)) _ _ (zeroTwoStateIndex d hd),
    cupCrossings_zero_right, pow_zero, one_mul, smul_single, smul_eq_mul, mul_comm]

/-- E3 on E1: the degree-zero unit state fixes the degree-one state of twist (2,0) on both sides. -/
theorem twoVertex_unit_cup (r : R) :
    stateTwistCast R (zero_add _) (cohomologyCup R 0 ![2, 0] (zeroTwistState R 1)
        (twoVertexLeftState R r)) = twoVertexLeftState R r ∧
    stateTwistCast R (add_zero _) (cohomologyCup R ![2, 0] 0 (twoVertexLeftState R r)
        (zeroTwistState R 1)) = twoVertexLeftState R r := by
  constructor
  · rw [cohomologyCup_zeroTwistState_left R _ twoVertexLeft_zeroTwo, one_smul]
  · rw [cohomologyCup_zeroTwistState_right R _ twoVertexLeft_zeroTwo, one_smul]

/-- E3 on the degree-three target: the unit state fixes the all-minus-two state of `Fin 3`. -/
theorem threeVertex_unit_cup_generator (r : R) :
    stateTwistCast R (zero_add _) (cohomologyCup R 0 (fun _ : Fin 3 => 2) (zeroTwistState R 1)
        (single (fun _ => gapZero) r)) = single (fun _ => gapZero) r ∧
    stateTwistCast R (add_zero _) (cohomologyCup R (fun _ : Fin 3 => 2) 0
        (single (fun _ => gapZero) r) (zeroTwistState R 1)) = single (fun _ => gapZero) r := by
  constructor
  · rw [cohomologyCup_zeroTwistState_left R _ (fun _ => Or.inr rfl), one_smul]
  · rw [cohomologyCup_zeroTwistState_right R _ (fun _ => Or.inr rfl), one_smul]

end Unit

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open CechProduct Finsupp

variable (R : Type) [CommRing R]

/-- E2: after transport to the constant twist two, the triple product (x ∪ y) ∪ z is the
all-minus-two state `threeMinusTwoState` with coefficient `(-1)^inversions * (r*s*t)`. -/
theorem threeVertex_cup_left_eq_threeMinusTwoState (r s t : R) :
    stateTwistCast R threeVertex_add_left
      (cohomologyCup R _ ![0, 0, 2]
        (cohomologyCup R ![2, 0, 0] ![0, 2, 0] (threeVertexX R r) (threeVertexY R s))
        (threeVertexZ R t)) =
      (threeMinusTwoState R ((-1) ^ threeVertexInversions * (r * s * t))).val :=
  threeVertex_cup_left R r s t

/-- E2: the other bracketing x ∪ (y ∪ z) gives the same all-minus-two state. -/
theorem threeVertex_cup_right_eq_threeMinusTwoState (r s t : R) :
    stateTwistCast R threeVertex_add_right
      (cohomologyCup R ![2, 0, 0] _ (threeVertexX R r)
        (cohomologyCup R ![0, 2, 0] ![0, 0, 2] (threeVertexY R s) (threeVertexZ R t))) =
      (threeMinusTwoState R ((-1) ^ threeVertexInversions * (r * s * t))).val :=
  threeVertex_cup_right R r s t

/-- The degree-one state of twist (2,0) lies in the degree-one state piece. -/
theorem twoVertexLeftState_mem (r : R) :
    twoVertexLeftState R r ∈ stateDegreePiece R (![2, 0] : Fin 2 → ℕ) 1 :=
  single_mem_supported R r (by simp [cohomologyDegree, lineCohomologyDegree, Fin.sum_univ_two])

/-- The degree-one state of twist (0,2) lies in the degree-one state piece. -/
theorem twoVertexRightState_mem (r : R) :
    twoVertexRightState R r ∈ stateDegreePiece R (![0, 2] : Fin 2 → ℕ) 1 :=
  single_mem_supported R r (by simp [cohomologyDegree, lineCohomologyDegree, Fin.sum_univ_two])

/-- The degree-two generator of the constant twist two on `Fin 2` lies in the degree-two piece. -/
theorem twoVertexGenerator_mem (r : R) :
    (single (fun _ => gapZero) r : H R (fun _ : Fin 2 => 2)) ∈
      stateDegreePiece R (fun _ : Fin 2 => 2) 2 :=
  single_mem_supported R r (by simp [cohomologyDegree, lineCohomologyDegree])

/-- The degree-one states x, y, z lie in the degree-one state pieces of their twists. -/
theorem threeVertexXYZ_mem (r : R) :
    threeVertexX R r ∈ stateDegreePiece R (![2, 0, 0] : Fin 3 → ℕ) 1 ∧
    threeVertexY R r ∈ stateDegreePiece R (![0, 2, 0] : Fin 3 → ℕ) 1 ∧
    threeVertexZ R r ∈ stateDegreePiece R (![0, 0, 2] : Fin 3 → ℕ) 1 :=
  have h : ∀ d : Fin 3 → ℕ, cohomologyDegree d = 1 → (cohomologyDegree d : ℤ) = 1 :=
    fun d hd => by rw [hd, Nat.cast_one]
  ⟨single_mem_supported R r (h _ (by simp [cohomologyDegree, lineCohomologyDegree,
      Fin.sum_univ_three])),
    single_mem_supported R r (h _ (by simp [cohomologyDegree, lineCohomologyDegree,
      Fin.sum_univ_three])),
    single_mem_supported R r (h _ (by simp [cohomologyDegree, lineCohomologyDegree,
      Fin.sum_univ_three]))⟩

end BPFixedPoints.ProjectiveLine

