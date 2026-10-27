import BPFixedPoints.Degree.Equations
import BPFixedPoints.StateSum.Parity
import BPFixedPoints.Incidence.Betti

/-!
# Nonbacktracking matrices and state determinants

For row dart α:i→j and column γ, let M_{αγ}=1_{h(γ)=t(α),γ≠ᾱ} (`nbMatrix`).
`det_nbMatrix` proves det M=(−1)^{|E|}∏_v(1−d(v)). Multiplying by dart reversal
R of sign (−1)^{|E|} gives RM=CCᵀ−I, C_{αv}=1_{h(α)=v}; use
 det(I−CCᵀ)=det(I−CᵀC) and CᵀC=diag(d(v)).

For edge set S, `stateMatrix` is the active-dart principal submatrix
(`stateMatrix_eq_submatrix`). Its determinant is
(−1)^{|S|}∏_v(1−d_S(v)) (`det_stateMatrix`), also
(−1)^{|S|+v(S)}w(S), w(S)=∏_{d_S(v)>0}(d_S(v)−1) (`det_stateMatrix_eq_w`).
It is nonzero for even-degree states (`det_stateMatrix_ne_zero`).
The block limit [[−diag(c_{h(α)})M_S,*],[0,I]] has determinant
(−1)^{|S|+v(S)}w(S)∏_v c_v^{d_S(v)} (`det_limitMatrix`), with sign
(−1)^{|S|−v(S)} when all c_v>0 (`sign_det_limitMatrix`). Subcubic even-degree
states satisfy |S|=v(S) (`card_eq_card_support_of_deg_le_three`).

The principal-minor formula det(I+A)=Σ_s det A_s
(`det_one_add_eq_sum_det_submatrix`) gives the signed θ identity. For
(B_σ)_{αβ}=σ_{e(β)}1_{h(α)=t(β),β≠ᾱ} (`signedNB`),
Σ_{σ∈{±1}^E}det(I−uB_σ)=2^{|E|}θ_G(u²,2i)
(`sum_det_one_sub_signedNB_eq_thetaTwoI`). Sign averaging leaves only
dart-reversal-closed subsets S×Bool (`sum_prod_sign`), whose minors are state determinants.

This module does not treat analytic extension along auxiliary branches,
the active-row δ_e limit, the ω matching expansion or gauge representatives.
Matrix identities allow loops counted twice by the dart convention, although
the paper does not treat loops. These are known finite-matrix identities;
no novelty is claimed.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

open Matrix BP

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E) (R : Type*) [CommRing R]

/-- Nonbacktracking convention: M_{αγ}=1_{h(γ)=t(α),γ≠ᾱ}. -/
def nbMatrix : Matrix (Dart E) (Dart E) R :=
  fun α γ => if G.head γ = G.tail α ∧ γ ≠ rev α then 1 else 0

/-- Head incidence matrix C_{αv}=1_{head α=v}. -/
def headMatrix : Matrix (Dart E) V R := fun α v => if G.head α = v then 1 else 0

/-- Dart reversal permutation. -/
def revPerm : Equiv.Perm (Dart E) := Equiv.prodCongrRight fun _ => Equiv.swap false true

omit [DecidableEq V] [Fintype V] in
@[simp] theorem revPerm_apply (α : Dart E) : (revPerm : Equiv.Perm (Dart E)) α = rev α := by
  rcases α with ⟨e, _ | _⟩ <;> rfl

omit [DecidableEq V] [Fintype V] in
theorem sign_revPerm :
    Equiv.Perm.sign (revPerm : Equiv.Perm (Dart E)) = (-1) ^ Fintype.card E := by
  rw [revPerm, Equiv.Perm.sign_prodCongrRight, Equiv.Perm.sign_swap (by decide),
    Finset.prod_const, Finset.card_univ]

theorem headMatrix_mul_transpose (α γ : Dart E) :
    (G.headMatrix R * (G.headMatrix R)ᵀ) α γ = if G.head α = G.head γ then 1 else 0 := by
  simp [headMatrix, Matrix.mul_apply, eq_comm]

theorem transpose_mul_headMatrix :
    (G.headMatrix R)ᵀ * G.headMatrix R = diagonal fun v => (G.degree v : R) := by
  ext v w
  simp only [Matrix.mul_apply, transpose_apply, headMatrix, diagonal_apply, mul_ite, mul_one,
    mul_zero]
  by_cases h : v = w
  · subst h
    simp [degree, inDarts, Finset.sum_ite, Finset.filter_filter]
  · rw [ite_eq_right_iff.2 fun h' => absurd h' h]
    apply Finset.sum_eq_zero
    intro α _
    split_ifs with h1 h2 <;> first | rfl | exact absurd (h1.symm.trans h2).symm h

theorem nbMatrix_submatrix_rev :
    (G.nbMatrix R).submatrix rev id = G.headMatrix R * (G.headMatrix R)ᵀ - 1 := by
  ext α γ
  rw [Matrix.sub_apply, headMatrix_mul_transpose, one_apply]
  simp only [submatrix_apply, id, nbMatrix, tail_rev, rev_rev]
  by_cases h : γ = α
  · subst h; simp
  · simp [h, Ne.symm h, eq_comm]

/-- Nonbacktracking determinant det M=(-1)^|E| product_v(1-deg v), including loops counted twice by the dart convention. -/
theorem det_nbMatrix :
    (G.nbMatrix R).det = (-1) ^ Fintype.card E * ∏ v, (1 - (G.degree v : R)) := by
  have h1 := det_permute (revPerm : Equiv.Perm (Dart E)) (G.nbMatrix R)
  have hrev : ⇑(revPerm : Equiv.Perm (Dart E)) = rev := funext revPerm_apply
  rw [hrev, nbMatrix_submatrix_rev, sign_revPerm] at h1
  have h2 : (G.headMatrix R * (G.headMatrix R)ᵀ - 1).det = ∏ v, (1 - (G.degree v : R)) := by
    have : G.headMatrix R * (G.headMatrix R)ᵀ - 1 =
        -(1 + (-G.headMatrix R) * (G.headMatrix R)ᵀ) := by
      rw [Matrix.neg_mul]; abel
    rw [this, det_neg, det_one_add_mul_comm, Matrix.mul_neg, transpose_mul_headMatrix]
    have hc : Fintype.card (Dart E) = 2 * Fintype.card E := by
      simp [Dart, Fintype.card_prod, mul_comm]
    rw [hc, pow_mul]
    have : (1 : Matrix V V R) + -diagonal (fun v => (G.degree v : R)) =
        diagonal fun v => 1 - (G.degree v : R) := by
      ext v w; by_cases h : v = w <;> simp [h, one_apply, sub_eq_add_neg]
    rw [this, det_diagonal]; simp
  rw [h2] at h1
  have hs : ((((-1 : ℤˣ) ^ Fintype.card E : ℤˣ) : ℤ) : R) = (-1) ^ Fintype.card E := by
    push_cast; rfl
  rw [hs] at h1
  calc (G.nbMatrix R).det
      = (-1) ^ Fintype.card E * ((-1) ^ Fintype.card E * (G.nbMatrix R).det) := by
        rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    _ = _ := by rw [← h1]

/-- Restrict edges to S while retaining the vertex type; this adds isolated vertices to the state graph (V(S),S). -/
def restrict (S : Finset E) : Multigraph V S where
  fst e := G.fst e
  snd e := G.snd e

theorem degree_restrict (S : Finset E) (v : V) : (G.restrict S).degree v = G.deg S v := by
  rw [degree_eq_deg]
  unfold Multigraph.deg
  rw [Finset.univ_eq_attach, ← Finset.sum_attach S (fun e => G.endCount e v)]
  rfl

/-- State matrix M_S, the nonbacktracking matrix of the state graph. -/
abbrev stateMatrix (S : Finset E) : Matrix (Dart S) (Dart S) R := (G.restrict S).nbMatrix R

/-- M_S is the active-dart principal submatrix of M. -/
theorem stateMatrix_eq_submatrix (S : Finset E) :
    G.stateMatrix R S =
      (G.nbMatrix R).submatrix (fun α : Dart S => (α.1.1, α.2)) (fun α => (α.1.1, α.2)) := by
  ext ⟨⟨e, he⟩, d⟩ ⟨⟨f, hf⟩, d'⟩
  cases d <;> cases d' <;> simp [nbMatrix, restrict, head, tail, rev, Prod.ext_iff]

/-- **State determinant:** det M_S=(−1)^{|S|}∏_v(1−d_S(v)). -/
theorem det_stateMatrix (S : Finset E) :
    (G.stateMatrix R S).det = (-1) ^ S.card * ∏ v, (1 - (G.deg S v : R)) := by
  rw [stateMatrix, det_nbMatrix]
  simp [degree_restrict]

/-- Equivalent form det M_S=(-1)^{|S|+v(S)} w(S), with excess |S|-v(S) and w(S)=product_{d_S(v)>0}(d_S(v)-1). -/
theorem det_stateMatrix_eq_w (S : Finset E) :
    (G.stateMatrix R S).det =
      (-1) ^ (S.card + (G.support S).card) * ∏ v ∈ G.support S, ((G.deg S v : R) - 1) := by
  rw [det_stateMatrix]
  have : ∏ v, (1 - (G.deg S v : R)) = ∏ v ∈ G.support S, (1 - (G.deg S v : R)) := by
    rw [← Finset.prod_subset (Finset.subset_univ _)]
    intro v _ hv
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
      Nat.le_zero] at hv
    simp [hv]
  rw [this, pow_add, mul_assoc, Finset.pow_card_mul_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro v _; ring

/-- For Eulerian S, det M_S≠0 in characteristic zero. -/
theorem det_stateMatrix_ne_zero [IsDomain R] [CharZero R] {S : Finset E} (hS : G.IsEvenSet S) :
    (G.stateMatrix R S).det ≠ 0 := by
  rw [det_stateMatrix_eq_w]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) (Finset.prod_ne_zero_iff.2 fun v hv => ?_)
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨k, hk⟩ := hS v
  have h2 : 2 ≤ G.deg S v := by omega
  rw [sub_ne_zero]
  exact_mod_cast (by omega : G.deg S v ≠ 1)

/-- Determinant of the active limit block −diag(c_{h(α)})M_S is det M_S·∏_v c_v^{d_S(v)}. There are 2|S| active darts, so the product of minus signs is one. -/
theorem det_neg_diagonal_mul_stateMatrix (S : Finset E) (c : V → R) :
    (-(diagonal fun α : Dart S => c ((G.restrict S).head α)) * G.stateMatrix R S).det =
      (G.stateMatrix R S).det * ∏ v, c v ^ G.deg S v := by
  rw [Matrix.neg_mul, det_neg, det_mul, det_diagonal]
  have hc : Fintype.card (Dart S) = 2 * S.card := by
    simp [Dart, Fintype.card_prod, mul_comm]
  have hp : ∏ α : Dart S, c ((G.restrict S).head α) = ∏ v, c v ^ G.deg S v := by
    rw [← Finset.prod_fiberwise Finset.univ (G.restrict S).head]
    apply Finset.prod_congr rfl
    intro v _
    rw [Finset.prod_congr rfl (fun α hα => by rw [(Finset.mem_filter.1 hα).2]),
      Finset.prod_const, ← degree_restrict]
    rfl
  rw [hc, pow_mul, hp]; simp [mul_comm]

/-- **Limit determinant.** Ordering active darts first, [[−diag(c_{h(α)})M_S,*],[0,I]] has determinant (−1)^{|S|+v(S)}w(S)∏_v c_v^{d_S(v)}. -/
theorem det_limitMatrix (S : Finset E) (c : V → R) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix (Dart S) ι R) :
    (fromBlocks (-(diagonal fun α : Dart S => c ((G.restrict S).head α)) * G.stateMatrix R S)
        B 0 1).det =
      (-1) ^ (S.card + (G.support S).card) * (∏ v ∈ G.support S, ((G.deg S v : R) - 1)) *
        ∏ v, c v ^ G.deg S v := by
  rw [det_fromBlocks_zero₂₁, det_one, mul_one, det_neg_diagonal_mul_stateMatrix,
    det_stateMatrix_eq_w]

/-- At a real starting point with all c_v>0 and even-degree S, the limit determinant has sign (−1)^{|S|−v(S)}. -/
theorem sign_det_limitMatrix {S : Finset E} (hS : G.IsEvenSet S) (c : V → ℝ) (hc : ∀ v, 0 < c v)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix (Dart S) ι ℝ) :
    0 < (-1) ^ (S.card + (G.support S).card) *
      (fromBlocks (-(diagonal fun α : Dart S => c ((G.restrict S).head α)) *
        G.stateMatrix ℝ S) B 0 1).det := by
  rw [det_limitMatrix, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
    one_pow, one_mul]
  refine mul_pos (Finset.prod_pos fun v hv => ?_) (Finset.prod_pos fun v _ => pow_pos (hc v) _)
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  obtain ⟨k, hk⟩ := hS v
  have : (2 : ℝ) ≤ G.deg S v := by exact_mod_cast (by omega : 2 ≤ G.deg S v)
  linarith

/-- For maximum degree at most three, every even-degree state has a(S)=|S|−v(S)=0. -/
theorem card_eq_card_support_of_deg_le_three {S : Finset E} (hS : G.IsEvenSet S)
    (h3 : ∀ v, G.deg S v ≤ 3) : S.card = (G.support S).card := by
  have hd : ∀ v, G.deg S v = if v ∈ G.support S then 2 else 0 := by
    intro v
    obtain ⟨k, hk⟩ := hS v
    have := h3 v
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
    split_ifs <;> omega
  have := G.sum_deg S
  rw [Finset.sum_congr rfl (fun v _ => hd v), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, smul_eq_mul] at this
  omega

end Multigraph

section PrincipalMinors

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- Principal-minor expansion det(I+A)=sum_s det A_s. -/
theorem det_one_add_eq_sum_det_submatrix (A : Matrix ι ι R) :
    (1 + A).det = ∑ s : Finset ι, (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have h0 : (1 + A).det =
      detRowAlternating ((fun i => A i) + (fun i => (1 : Matrix ι ι R) i)) := by
    rw [add_comm]; rfl
  rw [h0, AlternatingMap.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  let e := Equiv.sumCompl (fun i : ι => i ∈ s)
  let P : Matrix ι ι R := Matrix.of (s.piecewise (fun i => A i) (fun i => (1 : Matrix ι ι R) i))
  have h1 : detRowAlternating (s.piecewise (fun i => A i) (fun i => (1 : Matrix ι ι R) i)) =
      (P.submatrix e e).det := by
    rw [det_submatrix_equiv_self]; rfl
  rw [h1]
  have h2 : P.submatrix e e =
      fromBlocks (A.submatrix (Subtype.val : s → ι) Subtype.val)
        (A.submatrix (Subtype.val : s → ι) (Subtype.val : {i // i ∉ s} → ι)) 0 1 := by
    ext (⟨i, hi⟩ | ⟨i, hi⟩) (⟨j, hj⟩ | ⟨j, hj⟩)
    · simp [P, e, hi]
    · simp [P, e, hi]
    · simp [P, e, hi, one_apply]; rintro rfl; exact (hi hj).elim
    · simp [P, e, hi, one_apply, Subtype.ext_iff]
  rw [h2, det_fromBlocks_zero₂₁, det_one, mul_one]

end PrincipalMinors

namespace Multigraph

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E) (R : Type*) [CommRing R]

open BP

/-- Signed nonbacktracking convention: (B_σ)_{αβ}=σ_{e(β)}1_{h(α)=t(β),β≠ᾱ}. -/
def signedNB (σ : E → R) : Matrix (Dart E) (Dart E) R :=
  fun α β => σ β.1 * if G.head α = G.tail β ∧ β ≠ rev α then 1 else 0

/-- Dart sets containing either both orientations of each edge or neither. -/
def IsBalanced (s : Finset (Dart E)) : Prop := ∀ e, ((e, true) ∈ s ↔ (e, false) ∈ s)

instance (s : Finset (Dart E)) : Decidable (IsBalanced s) := by
  unfold IsBalanced; infer_instance

omit [DecidableEq V] [Fintype V] in
/-- The signing sum of product_{β∈s} σ_edgeβ is 2^|E| for reversal-closed s and zero otherwise. -/
theorem sum_prod_sign (s : Finset (Dart E)) :
    ∑ σ : E → ℤˣ, ∏ β ∈ s, ((σ β.1 : ℤ) : R) =
      if IsBalanced s then 2 ^ Fintype.card E else 0 := by
  have h1 : ∀ σ : E → ℤˣ, ∏ β ∈ s, ((σ β.1 : ℤ) : R) =
      ∏ e, ((if (e, true) ∈ s then ((σ e : ℤ) : R) else 1) *
        (if (e, false) ∈ s then ((σ e : ℤ) : R) else 1)) := by
    intro σ
    rw [← Fintype.prod_ite_mem, Fintype.prod_prod_type]
    simp only [Fintype.prod_bool]
  simp only [h1]
  rw [← Fintype.prod_sum (fun e (t : ℤˣ) => (if (e, true) ∈ s then ((t : ℤ) : R) else 1) *
    (if (e, false) ∈ s then ((t : ℤ) : R) else 1))]
  have h2 : ∀ e, ∑ t : ℤˣ, (if (e, true) ∈ s then ((t : ℤ) : R) else 1) *
      (if (e, false) ∈ s then ((t : ℤ) : R) else 1) =
      if ((e, true) ∈ s ↔ (e, false) ∈ s) then 2 else 0 := by
    intro e
    have hu : (Finset.univ : Finset ℤˣ) = {1, -1} := by decide
    rw [hu, Finset.sum_pair (by decide)]
    by_cases h1 : (e, true) ∈ s <;> by_cases h2 : (e, false) ∈ s <;> simp [h1, h2] <;> norm_num
  simp only [h2]
  rw [Finset.prod_ite_zero]
  simp [IsBalanced, Finset.prod_const, Finset.card_univ]

/-- Identify both orientations S×Bool with the darts of the state graph. -/
def dartsEquiv (S : Finset E) : Dart S ≃ (S ×ˢ (Finset.univ : Finset Bool) : Finset (Dart E)) where
  toFun α := ⟨(α.1.1, α.2), Finset.mem_product.2 ⟨α.1.2, Finset.mem_univ _⟩⟩
  invFun β := (⟨β.1.1, (Finset.mem_product.1 β.2).1⟩, β.1.2)
  left_inv := by rintro ⟨⟨e, he⟩, d⟩; rfl
  right_inv := by rintro ⟨⟨e, d⟩, h⟩; rfl

/-- The determinant of a reversal-closed principal submatrix is the state determinant, after transposition and reindexing. -/
theorem det_transpose_nbMatrix_submatrix (S : Finset E) :
    ((G.nbMatrix R)ᵀ.submatrix
        (Subtype.val : (S ×ˢ (Finset.univ : Finset Bool) : Finset (Dart E)) → Dart E)
        Subtype.val).det = (-1) ^ S.card * ∏ v, (1 - (G.deg S v : R)) := by
  rw [← transpose_submatrix, det_transpose, ← det_submatrix_equiv_self (dartsEquiv S),
    submatrix_submatrix, ← det_stateMatrix G R S, stateMatrix_eq_submatrix]
  rfl

/-- **Signed nonbacktracking θ identity:** Σ_{σ∈{±1}^E}det(I−uB_σ)=2^{|E|}Σ_S(−u²)^{|S|}∏_v(1−d_S(v)). Direct proof by principal minors, sign averaging and state determinants. No looplessness assumption is needed under the dart convention, although the paper excludes loops. -/
theorem sum_det_one_sub_signedNB (u : R) :
    ∑ σ : E → ℤˣ, (1 - u • G.signedNB R (fun e => ((σ e : ℤ) : R))).det =
      2 ^ Fintype.card E * ∑ S : Finset E, (-u ^ 2) ^ S.card * ∏ v, (1 - (G.deg S v : R)) := by
  set D : Finset (Dart E) → R := fun s =>
    ((G.nbMatrix R)ᵀ.submatrix (Subtype.val : s → Dart E) Subtype.val).det with hD
  have h1 : ∀ σ : E → ℤˣ, (1 - u • G.signedNB R (fun e => ((σ e : ℤ) : R))).det =
      ∑ s : Finset (Dart E), (-u) ^ s.card * D s * ∏ β ∈ s, ((σ β.1 : ℤ) : R) := by
    intro σ
    rw [sub_eq_add_neg, ← neg_smul, det_one_add_eq_sum_det_submatrix]
    apply Finset.sum_congr rfl
    intro s _
    have : (((-u) • G.signedNB R (fun e => ((σ e : ℤ) : R))).submatrix
        (Subtype.val : s → Dart E) Subtype.val) =
        (-u) • ((G.nbMatrix R)ᵀ.submatrix (Subtype.val : s → Dart E) Subtype.val *
          diagonal fun β : s => ((σ β.1.1 : ℤ) : R)) := by
      ext α β
      simp only [submatrix_apply, Matrix.smul_apply, smul_eq_mul, mul_diagonal, transpose_apply,
        signedNB, nbMatrix]
      congr 1
      rw [mul_comm]
      congr 1
      apply if_congr _ rfl rfl
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (by rw [h, rev_rev])⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun h => h2 (by rw [h, rev_rev])⟩
    rw [this, det_smul, det_mul, det_diagonal, Fintype.card_coe, ← mul_assoc,
      Finset.prod_coe_sort s (fun β => ((σ β.1 : ℤ) : R))]
  simp only [h1]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, sum_prod_sign, mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.mul_sum]
  symm
  apply Finset.sum_nbij' (fun S => S ×ˢ (Finset.univ : Finset Bool))
    (fun s => Finset.univ.filter fun e => (e, true) ∈ s)
  · intro S _
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun e => ?_⟩
    simp
  · intro _ _; exact Finset.mem_univ _
  · intro S _
    ext e; simp
  · intro s hs
    have hs : IsBalanced s := (Finset.mem_filter.1 hs).2
    ext ⟨e, d⟩
    cases d <;> simp [hs e]
  · intro S _
    simp only [hD, det_transpose_nbMatrix_submatrix, Finset.card_product, Finset.card_univ,
      Fintype.card_bool]
    rw [mul_comm S.card 2, pow_mul, neg_sq]
    rw [show (-u ^ 2) ^ S.card = (u ^ 2) ^ S.card * (-1) ^ S.card by
      rw [← mul_pow, mul_neg_one]]
    ring

/-- The same identity using the integer polynomial `thetaTwoI`: Σ_σdet(I−uB_σ)=2^{|E|}θ_G(u²,2i). -/
theorem sum_det_one_sub_signedNB_eq_thetaTwoI (u : R) :
    ∑ σ : E → ℤˣ, (1 - u • G.signedNB R (fun e => ((σ e : ℤ) : R))).det =
      2 ^ Fintype.card E * Polynomial.aeval (u ^ 2) G.thetaTwoI := by
  rw [sum_det_one_sub_signedNB, thetaTwoI]
  simp [map_sum]

end Multigraph

end BPFixedPoints
