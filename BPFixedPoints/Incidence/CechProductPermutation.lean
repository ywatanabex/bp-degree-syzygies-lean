import BPFixedPoints.Incidence.CechProductRingChange
import BPFixedPoints.Incidence.CechCupFormula
import BPFixedPoints.Incidence.CechCubicalBoundary
import BPFixedPoints.Incidence.CechProductSign

/-!
# Vertex bijections act on the product Čech complex with Koszul signs

The product Čech complex `C R V` of `CechProduct` and its state modules `H R d` are built by
tensoring one-vertex complexes in the order of the enumeration `Fintype.equivFin V`. A bijection
`ψ : V ≃ W` of finite vertex sets reorders the tensor factors. On a monomial `b : V → Basis` the
reordering is the monomial `b ∘ ψ.symm` times the Koszul sign `(-1)^N`, where `N` counts the pairs
of overlap (degree-one) vertices of `b` whose enumeration order is reversed by `ψ`
(`vertexInversions`, `vertexPermSign`). This is `cechVertexPerm`.

A state of twist `d` has its degree-one factors exactly at the vertices with `d v ≠ 0`
(`twistSupport`); the signed reindexing of states is `hVertexPerm`, with the constant sign of the
twist support. We prove:

* the signed reordering commutes with the product Čech differentials and parities and with the
  monomial section actions (`cechVertexPerm_d`, `cechVertexPerm_sign`, `cechVertexPerm_multiply`);
* it is compatible with the state inclusions and projections of the product contractions
  (`cechVertexPerm_i`, `contraction_p_cechVertexPerm`);
* it carries the full Čech chain product to the chain product (`cechVertexPerm_chainCup`), hence
  the signed state reindexing carries the multi-vertex cohomology cup product to the cup product
  (`hVertexPerm_cohomologyCup`) and the cohomology unit to the unit;
* identity and composition laws.

The sign is genuinely needed: the cup product of `CechProduct` moves the degree-one factors past
each other in the order of the enumeration, and `vertexPermSign_union` is the corresponding
shuffle identity.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open Finsupp CechProduct

/-! ## Inversions of vertex enumerations -/

section Signs

variable {V W X : Type} [Fintype V] [Fintype W] [Fintype X]

/-- Two parities agree when their sum is even. -/
theorem neg_one_pow_eq_of_even_add {R : Type*} [CommRing R] {a b : ℕ} (h : Even (a + b)) :
    (-1 : R) ^ a = (-1 : R) ^ b := by
  have h1 : (-1 : R) ^ (a + b) = 1 := h.neg_one_pow
  calc (-1 : R) ^ a = (-1 : R) ^ a * ((-1 : R) ^ b * (-1 : R) ^ b) := by
        rw [← pow_add, ← two_mul, pow_mul]; simp
    _ = (-1 : R) ^ (a + b) * (-1 : R) ^ b := by rw [pow_add, mul_assoc]
    _ = (-1 : R) ^ b := by rw [h1, one_mul]

/-- The number of pairs of a vertex set whose order in the enumerations of `V` and `W` is
reversed by `ψ`. -/
noncomputable def vertexInversions (ψ : V ≃ W) (A : Finset V) : ℕ :=
  ∑ a ∈ A, ∑ b ∈ A, if Fintype.equivFin V a < Fintype.equivFin V b ∧
    Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0

/-- The Koszul sign of reordering the degree-one factors at the vertices of `A` along `ψ`. -/
noncomputable def vertexPermSign (R : Type*) [CommRing R] (ψ : V ≃ W) (A : Finset V) : R :=
  (-1) ^ vertexInversions ψ A

/-- The number of pairs `(b, a) ∈ B × A` with `b` before `a` in the enumeration of `V`. -/
noncomputable def vertexCrossings (B A : Finset V) : ℕ :=
  ∑ b ∈ B, ∑ a ∈ A, if Fintype.equivFin V b < Fintype.equivFin V a then 1 else 0

@[simp] theorem vertexPermSign_mul_self (R : Type*) [CommRing R] (ψ : V ≃ W) (A : Finset V) :
    vertexPermSign R ψ A * vertexPermSign R ψ A = 1 := by
  rw [vertexPermSign, ← pow_add, ← two_mul, pow_mul]
  simp

@[simp] theorem map_vertexPermSign {R R' : Type*} [CommRing R] [CommRing R'] (f : R →+* R')
    (ψ : V ≃ W) (A : Finset V) : f (vertexPermSign R ψ A) = vertexPermSign R' ψ A := by
  simp [vertexPermSign]

@[simp] theorem vertexInversions_empty (ψ : V ≃ W) : vertexInversions ψ ∅ = 0 := by
  simp [vertexInversions]

@[simp] theorem vertexPermSign_empty (R : Type*) [CommRing R] (ψ : V ≃ W) :
    vertexPermSign R ψ ∅ = 1 := by
  simp [vertexPermSign]

@[simp] theorem vertexInversions_singleton (ψ : V ≃ W) (v : V) :
    vertexInversions ψ {v} = 0 := by
  simp [vertexInversions]

@[simp] theorem vertexPermSign_singleton (R : Type*) [CommRing R] (ψ : V ≃ W) (v : V) :
    vertexPermSign R ψ {v} = 1 := by
  simp [vertexPermSign]

/-- The identity has no inversions. -/
@[simp] theorem vertexInversions_refl (A : Finset V) : vertexInversions (Equiv.refl V) A = 0 := by
  unfold vertexInversions
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [ite_eq_right_iff]
  rintro ⟨h, h'⟩
  exact absurd h' (lt_asymm h)

@[simp] theorem vertexPermSign_refl (R : Type*) [CommRing R] (A : Finset V) :
    vertexPermSign R (Equiv.refl V) A = 1 := by
  simp [vertexPermSign]

/-- Inversions of a disjoint union split into those of the parts and the mixed pairs. -/
theorem vertexInversions_union [DecidableEq V] (ψ : V ≃ W) {A B : Finset V} (h : Disjoint A B) :
    vertexInversions ψ (A ∪ B) = vertexInversions ψ A + vertexInversions ψ B +
      ∑ a ∈ A, ∑ b ∈ B,
        ((if Fintype.equivFin V a < Fintype.equivFin V b ∧
            Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0) +
          (if Fintype.equivFin V b < Fintype.equivFin V a ∧
            Fintype.equivFin W (ψ a) < Fintype.equivFin W (ψ b) then 1 else 0)) := by
  unfold vertexInversions
  simp only [Finset.sum_union h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := B) (t := A)]
  ring

/-- Crossings of the image sets, as a sum over the original sets. -/
theorem vertexCrossings_map (ψ : V ≃ W) (B A : Finset V) :
    vertexCrossings (B.map ψ.toEmbedding) (A.map ψ.toEmbedding) =
      ∑ b ∈ B, ∑ a ∈ A,
        if Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0 := by
  unfold vertexCrossings
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_map]
  rfl

/-- **Shuffle identity.** Reordering a disjoint union along `ψ` and moving the factors of `B`
past the later factors of `A` agree up to the reordering of the parts. -/
theorem vertexPermSign_union [DecidableEq V] (R : Type*) [CommRing R] (ψ : V ≃ W)
    {A B : Finset V} (h : Disjoint A B) :
    vertexPermSign R ψ (A ∪ B) * (-1 : R) ^ vertexCrossings B A =
      (-1 : R) ^ vertexCrossings (B.map ψ.toEmbedding) (A.map ψ.toEmbedding) *
        (vertexPermSign R ψ A * vertexPermSign R ψ B) := by
  unfold vertexPermSign
  rw [← pow_add, ← pow_add, ← pow_add]
  apply neg_one_pow_eq_of_even_add
  rw [vertexInversions_union ψ h, vertexCrossings_map]
  have hcross : vertexCrossings B A = ∑ a ∈ A, ∑ b ∈ B,
      if Fintype.equivFin V b < Fintype.equivFin V a then 1 else 0 := by
    unfold vertexCrossings
    exact Finset.sum_comm
  have hcross' : (∑ b ∈ B, ∑ a ∈ A,
      if Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0) =
      ∑ a ∈ A, ∑ b ∈ B, if Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0 :=
    Finset.sum_comm
  rw [hcross, hcross']
  have hpt : ∀ a ∈ A, ∀ b ∈ B, Even (((if Fintype.equivFin V a < Fintype.equivFin V b ∧
        Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0) +
      (if Fintype.equivFin V b < Fintype.equivFin V a ∧
        Fintype.equivFin W (ψ a) < Fintype.equivFin W (ψ b) then 1 else 0)) +
      (if Fintype.equivFin V b < Fintype.equivFin V a then 1 else 0) +
      (if Fintype.equivFin W (ψ b) < Fintype.equivFin W (ψ a) then 1 else 0)) := by
    intro a ha b hb
    have hab : a ≠ b := fun hab => Finset.disjoint_left.mp h ha (hab ▸ hb)
    have h1 : Fintype.equivFin V a ≠ Fintype.equivFin V b :=
      fun h' => hab ((Fintype.equivFin V).injective h')
    have h2 : Fintype.equivFin W (ψ a) ≠ Fintype.equivFin W (ψ b) :=
      fun h' => hab (ψ.injective ((Fintype.equivFin W).injective h'))
    rcases lt_or_gt_of_ne h1 with h1 | h1 <;> rcases lt_or_gt_of_ne h2 with h2 | h2 <;>
      simp [h1, h2, not_lt_of_gt]
  have hsum := Finset.even_sum _ fun a ha => Finset.even_sum _ fun b hb => hpt a ha b hb
  simp only [Finset.sum_add_distrib] at hsum ⊢
  obtain ⟨k, hk⟩ := hsum
  exact ⟨vertexInversions ψ A + vertexInversions ψ B + k, by omega⟩

/-- Inversions of a composite have the parity of the sum of the inversions. -/
theorem even_vertexInversions_trans (ψ : V ≃ W) (χ : W ≃ X) (A : Finset V) :
    Even (vertexInversions (ψ.trans χ) A + vertexInversions χ (A.map ψ.toEmbedding) +
      vertexInversions ψ A) := by
  let rV := Fintype.equivFin V
  let rW := Fintype.equivFin W
  let rX := Fintype.equivFin X
  let f : V → V → ℕ := fun a b =>
    (if rV a < rV b ∧ rX (χ (ψ b)) < rX (χ (ψ a)) then 1 else 0) +
      (if rW (ψ a) < rW (ψ b) ∧ rX (χ (ψ b)) < rX (χ (ψ a)) then 1 else 0) +
      (if rV a < rV b ∧ rW (ψ b) < rW (ψ a) then 1 else 0)
  have hsum : vertexInversions (ψ.trans χ) A + vertexInversions χ (A.map ψ.toEmbedding) +
      vertexInversions ψ A = ∑ a ∈ A, ∑ b ∈ A, f a b := by
    simp only [f, Finset.sum_add_distrib, vertexInversions, Finset.sum_map, Equiv.trans_apply,
      Equiv.coe_toEmbedding]
    rfl
  have hdiag : ∀ a, f a a = 0 := by
    intro a
    simp [f]
  have hpair : ∀ a b, Even (f a b + f b a) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      rw [hdiag]
      exact Even.zero
    have h0 : rV a ≠ rV b := fun h => hab (rV.injective h)
    have h1 : rW (ψ a) ≠ rW (ψ b) := fun h => hab (ψ.injective (rW.injective h))
    have h2 : rX (χ (ψ a)) ≠ rX (χ (ψ b)) :=
      fun h => hab (ψ.injective (χ.injective (rX.injective h)))
    rcases lt_or_gt_of_ne h0 with h | h <;> rcases lt_or_gt_of_ne h1 with h' | h' <;>
      rcases lt_or_gt_of_ne h2 with h'' | h'' <;>
      simp [f, h, h', h'', not_lt_of_gt]
  have hsplit : ∑ a ∈ A, ∑ b ∈ A, f a b =
      ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f a b + f b a else 0) := by
    have hswap : ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f b a else 0) =
        ∑ a ∈ A, ∑ b ∈ A, (if rV b < rV a then f a b else 0) := Finset.sum_comm
    have hterm : ∀ a b, f a b = (if rV a < rV b then f a b else 0) +
        (if rV b < rV a then f a b else 0) := by
      intro a b
      rcases lt_trichotomy (rV a) (rV b) with h | h | h
      · simp [h, not_lt_of_gt h]
      · rw [rV.injective h, hdiag]
        simp
      · simp [h, not_lt_of_gt h]
    calc ∑ a ∈ A, ∑ b ∈ A, f a b
        = ∑ a ∈ A, ∑ b ∈ A, ((if rV a < rV b then f a b else 0) +
            (if rV b < rV a then f a b else 0)) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f a b else 0) +
          ∑ a ∈ A, ∑ b ∈ A, (if rV b < rV a then f a b else 0) := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f a b else 0) +
          ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f b a else 0) := by rw [hswap]
      _ = ∑ a ∈ A, ∑ b ∈ A, (if rV a < rV b then f a b + f b a else 0) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun b _ => ?_
          split_ifs <;> simp
  rw [hsum, hsplit]
  refine Finset.even_sum _ fun a _ => Finset.even_sum _ fun b _ => ?_
  split_ifs
  · exact hpair a b
  · exact Even.zero

/-- The reordering sign of a composite is the product of the reordering signs. -/
theorem vertexPermSign_trans (R : Type*) [CommRing R] (ψ : V ≃ W) (χ : W ≃ X) (A : Finset V) :
    vertexPermSign R (ψ.trans χ) A =
      vertexPermSign R χ (A.map ψ.toEmbedding) * vertexPermSign R ψ A := by
  unfold vertexPermSign
  rw [← pow_add]
  apply neg_one_pow_eq_of_even_add
  have h := even_vertexInversions_trans ψ χ A
  rw [show vertexInversions (ψ.trans χ) A + (vertexInversions χ (A.map ψ.toEmbedding) +
    vertexInversions ψ A) = vertexInversions (ψ.trans χ) A +
      vertexInversions χ (A.map ψ.toEmbedding) + vertexInversions ψ A by ring]
  exact h

/-- The reordering signs of `ψ` and of its inverse on the image set agree. -/
theorem vertexPermSign_symm_mul (R : Type*) [CommRing R] (ψ : V ≃ W) (A : Finset V) :
    vertexPermSign R ψ.symm (A.map ψ.toEmbedding) * vertexPermSign R ψ A = 1 := by
  rw [← vertexPermSign_trans, Equiv.self_trans_symm, vertexPermSign_refl]

/-- **The sign is not trivial.** A transposition of two vertices reverses the order of the pair,
so reordering two degree-one factors along it costs a sign. -/
theorem vertexInversions_swap [DecidableEq V] {a b : V} (h : a ≠ b) :
    vertexInversions (Equiv.swap a b) {a, b} = 1 := by
  have hr : Fintype.equivFin V a ≠ Fintype.equivFin V b :=
    fun h' => h ((Fintype.equivFin V).injective h')
  unfold vertexInversions
  rw [Finset.sum_pair h, Finset.sum_pair h, Finset.sum_pair h]
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, lt_irrefl, ite_false,
    and_self, zero_add, add_zero]
  rcases lt_or_gt_of_ne hr with h' | h'
  · simp [h', not_lt_of_gt h']
  · simp [h', not_lt_of_gt h']

theorem vertexPermSign_swap [DecidableEq V] (R : Type*) [CommRing R] {a b : V} (h : a ≠ b) :
    vertexPermSign R (Equiv.swap a b) {a, b} = -1 := by
  rw [vertexPermSign, vertexInversions_swap h, pow_one]

end Signs

/-! ## Overlap vertices and twist supports -/

section Supports

variable {V W : Type} [Fintype V] [Fintype W]

/-- One-vertex Čech degrees are at most one. -/
theorem lineDegree_le_one (x : Basis) : lineDegree x ≤ 1 := by
  rcases x with k | k | k <;> simp [lineDegree]

/-- The overlap vertices of a product monomial: the vertices where it has Čech degree one. -/
noncomputable def overlapVertices (b : V → Basis) : Finset V :=
  Finset.univ.filter fun v => lineDegree (b v) = 1

theorem mem_overlapVertices {b : V → Basis} {v : V} :
    v ∈ overlapVertices b ↔ lineDegree (b v) = 1 := by
  simp [overlapVertices]

/-- Sums over the overlap vertices weight every vertex by its Čech degree. -/
theorem sum_overlapVertices (b : V → Basis) (f : V → ℕ) :
    ∑ v ∈ overlapVertices b, f v = ∑ v, lineDegree (b v) * f v := by
  rw [overlapVertices, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases b v with k | k | k <;> simp [lineDegree]

/-- Reindexing a monomial reindexes its overlap vertices. -/
theorem overlapVertices_comp (ψ : V ≃ W) (b : V → Basis) :
    overlapVertices (fun w => b (ψ.symm w)) = (overlapVertices b).map ψ.toEmbedding := by
  ext w
  rw [Finset.mem_map_equiv, mem_overlapVertices, mem_overlapVertices]

/-- The vertices carrying a degree-one factor in the states of a twist. -/
noncomputable def twistSupport (d : V → ℕ) : Finset V :=
  Finset.univ.filter fun v => d v ≠ 0

theorem mem_twistSupport {d : V → ℕ} {v : V} : v ∈ twistSupport d ↔ d v ≠ 0 := by
  simp [twistSupport]

/-- Reindexing a twist reindexes its support. -/
theorem twistSupport_comp (ψ : V ≃ W) (d : V → ℕ) :
    twistSupport (fun w => d (ψ.symm w)) = (twistSupport d).map ψ.toEmbedding := by
  ext w
  rw [Finset.mem_map_equiv, mem_twistSupport, mem_twistSupport]

/-- The cohomological degree of a twist is the cardinality of its support. -/
theorem cohomologyDegree_eq_card_twistSupport (d : V → ℕ) :
    cohomologyDegree d = (twistSupport d).card := by
  rw [cohomologyDegree_eq_card, twistSupport]
  congr 1
  ext v
  simp [Nat.pos_iff_ne_zero]

/-- A one-vertex state index of type zero occurs only for twist zero, and one of type one only
for a nonzero twist. -/
theorem lineStateIndex_inl {d : ℕ} {k : Fin (phi d)} {j : CechLine.H0Index d}
    (_h : (lineStateIndexEquiv d).symm k = Sum.inl j) : d = 0 := by
  by_contra hd
  have hj := j.isLt
  simp only [hd, ite_false] at hj
  omega

theorem lineStateIndex_inr {d : ℕ} {k : Fin (phi d)} {j : CechLine.H1Index d}
    (_h : (lineStateIndexEquiv d).symm k = Sum.inr j) : d ≠ 0 := by
  rintro rfl
  exact Nat.not_lt_zero _ j.isLt

/-- Every inclusion monomial of a one-vertex state has the Čech degree of the state. -/
theorem lineDegree_of_mem_lineInclusionMonomials {d : ℕ} {k : Fin (phi d)} {a : Basis}
    (h : a ∈ lineInclusionMonomials d k) : lineDegree a = lineCohomologyDegree d := by
  unfold lineInclusionMonomials at h
  split at h
  · rename_i j hk
    rw [lineStateIndex_inl hk]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl <;> rfl
  · rename_i j hk
    rw [Finset.mem_singleton] at h
    subst h
    simp [lineCohomologyDegree, lineStateIndex_inr hk, lineDegree]

/-- The projection monomial of a one-vertex state has the Čech degree of the state. -/
theorem lineDegree_lineProjectionMonomial (d : ℕ) (k : Fin (phi d)) :
    lineDegree (lineProjectionMonomial d k) = lineCohomologyDegree d := by
  unfold lineProjectionMonomial
  split
  · rename_i j hk
    rw [lineStateIndex_inl hk]
    rfl
  · rename_i j hk
    simp [lineCohomologyDegree, lineStateIndex_inr hk, lineDegree]

theorem lineCohomologyDegree_eq_one_iff (d : ℕ) : lineCohomologyDegree d = 1 ↔ d ≠ 0 := by
  unfold lineCohomologyDegree
  split_ifs with h <;> simp [h]

/-- The overlap vertices of a state projection monomial are the twist support. -/
theorem overlapVertices_stateProjectionMonomial (d : V → ℕ) (κ : HBasis d) :
    overlapVertices (stateProjectionMonomial d κ) = twistSupport d := by
  ext v
  rw [mem_overlapVertices, mem_twistSupport, stateProjectionMonomial,
    lineDegree_lineProjectionMonomial, lineCohomologyDegree_eq_one_iff]

/-- Projection monomials of transported states agree. -/
theorem lineProjectionMonomial_congr {n m : ℕ} (h : n = m) {k : Fin (phi n)} {k' : Fin (phi m)}
    (hk : HEq k k') : lineProjectionMonomial n k = lineProjectionMonomial m k' := by
  subst h
  cases hk
  rfl

/-- The inverse transport of dependent functions evaluates to the original value, up to the
identification of fibres. -/
theorem piCongrLeft'_symm_apply_heq {α β : Type*} (P : α → Sort*) (e : α ≃ β)
    (g : ∀ b, P (e.symm b)) (a : α) :
    HEq ((Equiv.piCongrLeft' P e).symm g a) (g (e a)) := by
  rw [Equiv.piCongrLeft'_symm_apply]
  exact eqRec_heq _ _

/-- Reindexing a function after a pointwise update. -/
theorem update_comp_symm {α : Type*} [DecidableEq V] [DecidableEq W] (ψ : V ≃ W) (b : V → α)
    (v : V) (x : α) :
    (fun w => Function.update b v x (ψ.symm w)) =
      Function.update (fun w => b (ψ.symm w)) (ψ v) x := by
  funext w
  by_cases hw : w = ψ v
  · subst hw
    simp
  · have hv : ψ.symm w ≠ v := fun h => hw (by rw [← h, Equiv.apply_symm_apply])
    rw [Function.update_of_ne hw, Function.update_of_ne hv]

end Supports

/-! ## The signed reordering of the product Čech complex -/

section Chains

variable {V W X : Type} [Fintype V] [Fintype W] [Fintype X]
variable (R : Type) [CommRing R]

/-- The signed reordering of product Čech chains along a vertex bijection, as a linear map: a
monomial `b` goes to the Koszul sign of its overlap vertices times the monomial `b ∘ ψ.symm`. -/
noncomputable def cechVertexPermMap (ψ : V ≃ W) : C R V →ₗ[R] C R W :=
  Finsupp.lsum R fun b =>
    vertexPermSign R ψ (overlapVertices b) • Finsupp.lsingle (fun w => b (ψ.symm w))

@[simp] theorem cechVertexPermMap_single (ψ : V ≃ W) (b : V → Basis) (r : R) :
    cechVertexPermMap R ψ (single b r) =
      single (fun w => b (ψ.symm w)) (vertexPermSign R ψ (overlapVertices b) * r) := by
  simp [cechVertexPermMap, Finsupp.smul_single, smul_eq_mul]

/-- The signed reordering along the identity is the identity. -/
theorem cechVertexPermMap_refl : cechVertexPermMap R (Equiv.refl V) = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro b r
  rw [cechVertexPermMap_single, vertexPermSign_refl, one_mul]
  rfl

/-- The signed reordering along a composite is the composite of the reorderings. -/
theorem cechVertexPermMap_trans (ψ : V ≃ W) (χ : W ≃ X) :
    cechVertexPermMap R (ψ.trans χ) = (cechVertexPermMap R χ).comp (cechVertexPermMap R ψ) := by
  apply Finsupp.lhom_ext
  intro b r
  rw [LinearMap.comp_apply, cechVertexPermMap_single, cechVertexPermMap_single,
    cechVertexPermMap_single, vertexPermSign_trans, overlapVertices_comp, mul_assoc]
  rfl

/-- The signed reordering of product Čech chains along a vertex bijection. -/
noncomputable def cechVertexPerm (ψ : V ≃ W) : C R V ≃ₗ[R] C R W :=
  LinearEquiv.ofLinearMap (cechVertexPermMap R ψ) (cechVertexPermMap R ψ.symm)
    (by rw [← cechVertexPermMap_trans, Equiv.symm_trans_self, cechVertexPermMap_refl])
    (by rw [← cechVertexPermMap_trans, Equiv.self_trans_symm, cechVertexPermMap_refl])

theorem cechVertexPerm_apply (ψ : V ≃ W) (c : C R V) :
    cechVertexPerm R ψ c = cechVertexPermMap R ψ c := rfl

@[simp] theorem cechVertexPerm_single (ψ : V ≃ W) (b : V → Basis) (r : R) :
    cechVertexPerm R ψ (single b r) =
      single (fun w => b (ψ.symm w)) (vertexPermSign R ψ (overlapVertices b) * r) :=
  cechVertexPermMap_single R ψ b r

/-- Coefficients of a reordered chain. -/
theorem cechVertexPerm_apply_apply (ψ : V ≃ W) (c : C R V) (b : W → Basis) :
    cechVertexPerm R ψ c b =
      vertexPermSign R ψ (overlapVertices fun v => b (ψ v)) * c (fun v => b (ψ v)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single a r =>
    rw [cechVertexPerm_single]
    by_cases ha : a = fun v => b (ψ v)
    · subst ha
      have hb : (fun w => b (ψ (ψ.symm w))) = b := by
        funext w
        rw [Equiv.apply_symm_apply]
      rw [hb, single_eq_same, single_eq_same]
    · have hb : (fun w => a (ψ.symm w)) ≠ b := by
        intro hb
        apply ha
        funext v
        rw [← hb]
        simp only [Equiv.symm_apply_apply]
      rw [single_eq_of_ne (Ne.symm hb), single_eq_of_ne (Ne.symm ha), mul_zero]

@[simp] theorem cechVertexPerm_refl (c : C R V) : cechVertexPerm R (Equiv.refl V) c = c := by
  rw [cechVertexPerm_apply, cechVertexPermMap_refl, LinearMap.id_apply]

theorem cechVertexPerm_trans (ψ : V ≃ W) (χ : W ≃ X) (c : C R V) :
    cechVertexPerm R (ψ.trans χ) c = cechVertexPerm R χ (cechVertexPerm R ψ c) := by
  rw [cechVertexPerm_apply, cechVertexPermMap_trans]
  rfl

/-- Reordering preserves Čech degrees. -/
theorem cechDegree_comp (ψ : V ≃ W) (b : V → Basis) :
    cechDegree (fun w => b (ψ.symm w)) = cechDegree b :=
  ψ.symm.sum_comp (fun v => lineDegree (b v))

/-- Reordering commutes with the Čech parities. -/
theorem cechVertexPerm_sign (ψ : V ≃ W) (d : V → ℕ) (c : C R V) :
    cechVertexPerm R ψ ((contraction R d).sign c) =
      (contraction R (fun w => d (ψ.symm w))).sign (cechVertexPerm R ψ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single b r =>
    rw [contraction_sign_single, map_smul, cechVertexPerm_single, contraction_sign_single,
      cechDegree_comp]

/-- Reordering commutes with the monomial section actions. -/
theorem cechVertexPerm_multiply (ψ : V ≃ W) (a b : V → ℕ) (c : C R V) :
    cechVertexPerm R ψ (multiply R a b c) =
      multiply R (fun w => a (ψ.symm w)) (fun w => b (ψ.symm w)) (cechVertexPerm R ψ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single f r =>
    rw [multiply_single, cechVertexPerm_single, cechVertexPerm_single, multiply_single]
    congr 2
    unfold overlapVertices
    simp only [lineDegree_shift]

/-- The prefix degree of the product Čech differential counts the earlier overlap vertices. -/
theorem boundaryPrefix_eq_vertexCrossings (b : V → Basis) (v : V) :
    boundaryPrefix b v = vertexCrossings (overlapVertices b) {v} := by
  unfold boundaryPrefix vertexCrossings
  rw [sum_overlapVertices]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_singleton]
  split_ifs <;> simp

/-- Reordering commutes with the product Čech differentials. -/
theorem cechVertexPerm_d [DecidableEq V] [DecidableEq W] (ψ : V ≃ W) (d : V → ℕ) (c : C R V) :
    cechVertexPerm R ψ ((contraction R d).d c) =
      (contraction R (fun w => d (ψ.symm w))).d (cechVertexPerm R ψ c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single b r =>
    rw [contraction_d_single, map_sum, cechVertexPerm_single, contraction_d_single]
    apply Fintype.sum_equiv ψ
    intro v
    simp only [Equiv.symm_apply_apply]
    rw [cechVertexPerm_single, update_comp_symm]
    congr 1
    -- the coefficients
    rcases hbv : b v with k | k | k
    · have hodd : overlapVertices (Function.update b v (boundaryStep (d v) (Sum.inl k))) =
          {v} ∪ overlapVertices b := by
        ext w
        by_cases hw : w = v
        · subst hw
          simp [mem_overlapVertices, boundaryStep, lineDegree]
        · simp [mem_overlapVertices, hw]
      have hv : Disjoint {v} (overlapVertices b) := by
        rw [Finset.disjoint_singleton_left, mem_overlapVertices, hbv]
        simp [lineDegree]
      have hs := vertexPermSign_union R ψ hv
      rw [vertexPermSign_singleton, one_mul, Finset.map_singleton] at hs
      rw [hodd, boundaryPrefix_eq_vertexCrossings, boundaryPrefix_eq_vertexCrossings,
        overlapVertices_comp]
      simp only [Equiv.coe_toEmbedding] at hs ⊢
      linear_combination (boundaryCoefficient R (Sum.inl k) * r) * hs
    · have hodd : overlapVertices (Function.update b v (boundaryStep (d v) (Sum.inr (Sum.inl k)))) =
          {v} ∪ overlapVertices b := by
        ext w
        by_cases hw : w = v
        · subst hw
          simp [mem_overlapVertices, boundaryStep, lineDegree]
        · simp [mem_overlapVertices, hw]
      have hv : Disjoint {v} (overlapVertices b) := by
        rw [Finset.disjoint_singleton_left, mem_overlapVertices, hbv]
        simp [lineDegree]
      have hs := vertexPermSign_union R ψ hv
      rw [vertexPermSign_singleton, one_mul, Finset.map_singleton] at hs
      rw [hodd, boundaryPrefix_eq_vertexCrossings, boundaryPrefix_eq_vertexCrossings,
        overlapVertices_comp]
      simp only [Equiv.coe_toEmbedding] at hs ⊢
      linear_combination (boundaryCoefficient R (Sum.inr (Sum.inl k)) * r) * hs
    · simp [boundaryCoefficient]

end Chains

/-! ## The signed reindexing of states -/

section States

variable {V W : Type} [Fintype V] [Fintype W]
variable (R : Type) [CommRing R]

/-- The signed reindexing of product Čech states along a vertex bijection: a state of twist `d`
goes to the Koszul sign of the twist support times the reindexed state of twist `d ∘ ψ.symm`. -/
noncomputable def hVertexPerm (ψ : V ≃ W) (d : V → ℕ) :
    H R d →ₗ[R] H R (fun w => d (ψ.symm w)) :=
  vertexPermSign R ψ (twistSupport d) •
    Finsupp.lmapDomain R R (Equiv.piCongrLeft' (fun v => Fin (phi (d v))) ψ)

@[simp] theorem hVertexPerm_single (ψ : V ≃ W) (d : V → ℕ) (κ : HBasis d) (r : R) :
    hVertexPerm R ψ d (single κ r) =
      single (fun w => κ (ψ.symm w)) (vertexPermSign R ψ (twistSupport d) * r) := by
  simp [hVertexPerm, Finsupp.smul_single, smul_eq_mul]
  rfl

/-- Coefficients of a reindexed state. -/
theorem hVertexPerm_apply (ψ : V ≃ W) (d : V → ℕ) (x : H R d) (κ : HBasis fun w => d (ψ.symm w)) :
    hVertexPerm R ψ d x κ = vertexPermSign R ψ (twistSupport d) *
      x ((Equiv.piCongrLeft' (fun v => Fin (phi (d v))) ψ).symm κ) := by
  simp only [hVertexPerm, LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.lmapDomain_apply,
    smul_eq_mul]
  rw [mapDomain_equiv_apply]

/-- Reordering is compatible with the state inclusions of the product contractions. -/
theorem cechVertexPerm_i (ψ : V ≃ W) (d : V → ℕ) (x : H R d) :
    cechVertexPerm R ψ ((contraction R d).i x) =
      (contraction R (fun w => d (ψ.symm w))).i (hVertexPerm R ψ d x) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single κ r =>
    ext b
    rw [cechVertexPerm_apply_apply, contraction_i_single_apply, hVertexPerm_single,
      contraction_i_single_apply]
    have hmem : ∀ v, lineInclusionMonomials (d (ψ.symm (ψ v))) (κ (ψ.symm (ψ v))) =
        lineInclusionMonomials (d v) (κ v) := fun v =>
      congrArg (fun u => lineInclusionMonomials (d u) (κ u)) (ψ.symm_apply_apply v)
    have hiff : (∀ v, b (ψ v) ∈ lineInclusionMonomials (d v) (κ v)) ↔
        ∀ w, b w ∈ lineInclusionMonomials (d (ψ.symm w)) (κ (ψ.symm w)) := by
      constructor
      · intro h w
        have hw := h (ψ.symm w)
        rwa [Equiv.apply_symm_apply] at hw
      · intro h v
        have hv := h (ψ v)
        rwa [hmem] at hv
    by_cases h : ∀ v, b (ψ v) ∈ lineInclusionMonomials (d v) (κ v)
    · rw [ite_eq_left h, ite_eq_left (hiff.mp h)]
      congr 1
      congr 1
      ext v
      rw [mem_overlapVertices, mem_twistSupport, lineDegree_of_mem_lineInclusionMonomials (h v),
        lineCohomologyDegree_eq_one_iff]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (hiff.mpr h')), mul_zero]

/-- Reordering is compatible with the state projections of the product contractions. -/
theorem contraction_p_cechVertexPerm (ψ : V ≃ W) (d : V → ℕ) (c : C R V) :
    (contraction R (fun w => d (ψ.symm w))).p (cechVertexPerm R ψ c) =
      hVertexPerm R ψ d ((contraction R d).p c) := by
  ext κ
  rw [contraction_p_coefficient, cechVertexPerm_apply_apply, hVertexPerm_apply,
    contraction_p_coefficient]
  have hm : (fun v => stateProjectionMonomial (fun w => d (ψ.symm w)) κ (ψ v)) =
      stateProjectionMonomial d ((Equiv.piCongrLeft' (fun v => Fin (phi (d v))) ψ).symm κ) := by
    funext v
    exact lineProjectionMonomial_congr (congrArg d (ψ.symm_apply_apply v))
      (piCongrLeft'_symm_apply_heq (fun v => Fin (phi (d v))) ψ κ v).symm
  rw [hm, overlapVertices_stateProjectionMonomial]

/-! ## Products -/

/-- The monomial product of `CechProduct` commutes with reindexing. -/
theorem cupBasis_comp (ψ : V ≃ W) (e : V → ℕ) (x y : V → Basis) :
    cupBasis (fun w => e (ψ.symm w)) (fun w => x (ψ.symm w)) (fun w => y (ψ.symm w)) =
      (cupBasis e x y).map (fun z w => z (ψ.symm w)) := by
  cases h : cupBasis e x y with
  | some z =>
    apply (cupBasis_some_iff _ _ _ _).mpr
    intro w
    exact (cupBasis_some_iff _ _ _ _).mp h (ψ.symm w)
  | none =>
    cases h' : cupBasis (fun w => e (ψ.symm w)) (fun w => x (ψ.symm w))
        (fun w => y (ψ.symm w)) with
    | none => rfl
    | some z =>
      exfalso
      have hz : cupBasis e x y = some (fun v => z (ψ v)) := by
        apply (cupBasis_some_iff _ _ _ _).mpr
        intro v
        have hv := (cupBasis_some_iff _ _ _ _).mp h' (ψ v)
        simp only [Equiv.symm_apply_apply] at hv
        exact hv
      rw [h] at hz
      exact Option.some_ne_none _ hz.symm

/-- The crossing count of the ordered tensor product: a degree-one factor of the right monomial
before a degree-one factor of the left monomial. -/
theorem finCupCross_eq (n : ℕ) (x y : Fin n → Basis) :
    finCupCross n x y = ∑ i, ∑ j, if i < j then lineDegree (y i) * lineDegree (x j) else 0 := by
  induction n with
  | zero => simp [finCupCross]
  | succ n ih =>
    rw [finCupCross, ih, Fin.sum_univ_succ]
    simp only [Fin.sum_univ_succ, lt_irrefl, ite_false, zero_add, Fin.succ_pos, ite_true,
      Fin.succ_lt_succ_iff, Fin.not_lt_zero]
    unfold cechDegree
    rw [Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Fin.tail, mul_comm]

/-- The crossing count of the labelled product counts overlap vertices of the right monomial
before overlap vertices of the left monomial. -/
theorem cupCross_eq_vertexCrossings (x y : V → Basis) :
    cupCross x y = vertexCrossings (overlapVertices y) (overlapVertices x) := by
  unfold cupCross
  rw [finCupCross_eq]
  unfold vertexCrossings
  rw [sum_overlapVertices]
  have hinner : ∀ b, ∑ a ∈ overlapVertices x,
      (if Fintype.equivFin V b < Fintype.equivFin V a then 1 else 0) =
      ∑ a, lineDegree (x a) * (if Fintype.equivFin V b < Fintype.equivFin V a then 1 else 0) :=
    fun b => sum_overlapVertices x _
  simp only [hinner, Finset.mul_sum]
  refine Fintype.sum_equiv (Fintype.equivFin V).symm _ _ fun i => ?_
  refine Fintype.sum_equiv (Fintype.equivFin V).symm _ _ fun j => ?_
  simp only [Function.comp_apply, Equiv.apply_symm_apply]
  split_ifs <;> ring

/-- Overlap vertices of a monomial product are the disjoint union of those of the factors. -/
theorem overlapVertices_of_cupBasis [DecidableEq V] {e : V → ℕ} {x y z : V → Basis}
    (h : cupBasis e x y = some z) :
    overlapVertices z = overlapVertices x ∪ overlapVertices y ∧
      Disjoint (overlapVertices x) (overlapVertices y) := by
  have hdeg := fun v => cupBasis_degree h v
  constructor
  · ext v
    have h1 := lineDegree_le_one (x v)
    have h2 := lineDegree_le_one (y v)
    have h3 := lineDegree_le_one (z v)
    have h4 := hdeg v
    rw [Finset.mem_union, mem_overlapVertices, mem_overlapVertices, mem_overlapVertices]
    omega
  · rw [Finset.disjoint_left]
    intro v hx hy
    rw [mem_overlapVertices] at hx hy
    have h3 := lineDegree_le_one (z v)
    rw [hdeg v] at h3
    omega

/-- Reordering carries the full Čech chain product to the chain product. -/
theorem cechVertexPerm_chainCup [DecidableEq V] (ψ : V ≃ W) (d e : V → ℕ) (x y : C R V) :
    cechVertexPerm R ψ (chainCup R d e x y) =
      chainCup R (fun w => d (ψ.symm w)) (fun w => e (ψ.symm w))
        (cechVertexPerm R ψ x) (cechVertexPerm R ψ y) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | single a r =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y y' hy hy' => simp only [map_add, hy, hy']
    | single b s =>
      rw [chainCup_single, cechVertexPerm_single, cechVertexPerm_single, chainCup_single,
        cupBasis_comp]
      cases h : cupBasis e a b with
      | none => simp
      | some z =>
        simp only [Option.map_some, Option.elim, cechVertexPerm_single]
        congr 1
        obtain ⟨hz, hdisj⟩ := overlapVertices_of_cupBasis h
        have hs := vertexPermSign_union R ψ hdisj
        rw [hz, cupCross_eq_vertexCrossings, cupCross_eq_vertexCrossings, overlapVertices_comp,
          overlapVertices_comp]
        linear_combination (r * s) * hs

/-- **The signed reindexing of states carries the multi-vertex cohomology cup product to the
cup product.** -/
theorem hVertexPerm_cohomologyCup [DecidableEq V] (ψ : V ≃ W) (d e : V → ℕ) (x : H R d)
    (y : H R e) :
    hVertexPerm R ψ (d + e) (cohomologyCup R d e x y) =
      cohomologyCup R (fun w => d (ψ.symm w)) (fun w => e (ψ.symm w))
        (hVertexPerm R ψ d x) (hVertexPerm R ψ e y) := by
  have hcup : cohomologyCup R d e x y =
      (contraction R (d + e)).p (chainCup R d e ((contraction R d).i x) ((contraction R e).i y)) := by
    rw [← cohomologyCup_chain_projection R d e (contraction_d_i R d x) (contraction_d_i R e y),
      contraction_p_i, contraction_p_i]
  have hcup' : cohomologyCup R (fun w => d (ψ.symm w)) (fun w => e (ψ.symm w))
      (hVertexPerm R ψ d x) (hVertexPerm R ψ e y) =
      (contraction R ((fun w => d (ψ.symm w)) + fun w => e (ψ.symm w))).p
        (chainCup R (fun w => d (ψ.symm w)) (fun w => e (ψ.symm w))
          ((contraction R (fun w => d (ψ.symm w))).i (hVertexPerm R ψ d x))
          ((contraction R (fun w => e (ψ.symm w))).i (hVertexPerm R ψ e y))) := by
    rw [← cohomologyCup_chain_projection R _ _ (contraction_d_i R _ _) (contraction_d_i R _ _),
      contraction_p_i, contraction_p_i]
  rw [hcup, hcup', ← contraction_p_cechVertexPerm, cechVertexPerm_chainCup, cechVertexPerm_i,
    cechVertexPerm_i]
  rfl

/-- Reordering fixes the chain unit. -/
theorem cechVertexPerm_chainUnit (ψ : V ≃ W) :
    cechVertexPerm R ψ (chainUnit R (V := V)) = chainUnit R (V := W) := by
  classical
  unfold chainUnit
  rw [map_sum]
  refine Fintype.sum_equiv (ψ.arrowCongr (Equiv.refl Bool)) _ _ fun s => ?_
  rw [cechVertexPerm_single]
  have hodd : overlapVertices (fun v => unitBasis (s v)) = ∅ := by
    ext v
    simp [mem_overlapVertices]
  rw [hodd, vertexPermSign_empty, one_mul]
  rfl

/-- **The signed reindexing of states fixes the cohomology unit.** -/
theorem hVertexPerm_cohomologyUnit (ψ : V ≃ W) :
    hVertexPerm R ψ (0 : V → ℕ) (cohomologyUnit R) = cohomologyUnit R (V := W) := by
  rw [cohomologyUnit, ← contraction_p_cechVertexPerm, cechVertexPerm_chainUnit]
  rfl

end States

end BPFixedPoints.Multigraph
