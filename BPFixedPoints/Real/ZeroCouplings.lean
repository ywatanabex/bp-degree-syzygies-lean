import BPFixedPoints.Real.StrongFieldCount
import BPFixedPoints.Incidence.CycleSpace

/-!
# Zero couplings (`supp:zero-couplings`)

The real-root theorems (`thm:real` (ii)) assume a_e > 0 and a_e ≠ 1 (J_e ≠ 0) on every
edge. This file removes the second hypothesis by deleting the edges with a_e = 1.

Let A be a set of edges such that a_e = 1 for every edge e outside A, and let
G' = `G.edgeRestrict A` be the graph with the edges outside A deleted and all vertices
kept, with the restricted couplings a' = a|_A. Over an arbitrary field:

* at an admissible solution every message on an edge with a_e = 1 equals 1
  (`msg_eq_one_of_coupling_eq_one`): the update equation reads (y_α − 1)(X_α + 1) = 0
  and X_α + a_e ≠ 0 by admissibility;
* restriction of messages to the darts of G' (`restrictMsg`) and extension by 1 on the
  deleted darts (`extendMsg`) are inverse bijections of admissible solution sets
  (`zeroCouplingEquiv`). Cavity fields and total fields agree
  (`edgeRestrict_cavity`, `edgeRestrict_totalField`). In the reverse construction the new
  update denominators are X_α + 1 = F_{t(α)} + 1 (`cavity_extendMsg_of_not_mem`), nonzero
  by the vertex condition of admissibility in G'. For real a > 0 and b > 0 they are
  positive by `totalField_pos` (`real:sign-sectors`), as in the paper
  (`cavity_extendMsg_add_pos`).

For real a > 0, b > 0 the bijection preserves positivity of all messages
(`zeroCouplingPosEquiv`) and maps negative-message supports to their images in E
(`negSupport_extendMsg`). If moreover a_e ≠ 1 on A, transport of the results of
`thm:real` (ii) for G' gives:

* the negative-message supports of the admissible real roots of G are exactly the
  Eulerian edge sets of G contained in A (`zeroCoupling_negSupport_iff`);
* R_G(J, h) ≥ 2^{ν(G')} at every field (`zeroCoupling_lower`);
* min_h R_G(J, h) = 2^{ν(G')}, attained at a finite fiber with exactly one positive root
  (`zeroCoupling_min`);
* at strong fields the complex, real and positive counts are (Q(G'), 2^{ν(G')}, 1), with
  all complex roots simple (`zeroCoupling_strong`). Simplicity is transported by
  `isSimpleSolution_extendMsg_iff`: on a deleted dart the Jacobian row is (X_α + 1) w_α, so a
  kernel vector vanishes on the deleted darts and restricts to a kernel vector of G'.

The statements of the paper section, with Z the set of deleted edges (a_e = 1 on Z and
a_e ≠ 1 off Z), are `zero_couplings_msg_eq_one`, `zero_couplings_equiv`,
`zero_couplings_lower` and `zero_couplings_min`. The canonical support graph is
`G.edgeRestrict (couplingSupport a)`, with `couplingSupport a` the set of edges with
a_e ≠ 1; for it only a_e > 0 is assumed (`zero_couplings_min_support`). With all
couplings equal to 1 there is exactly one admissible real root at every positive field
(`card_real_of_couplings_eq_one`), so the bound 2^{ν(G)} fails as soon as ν(G) ≥ 1
(`not_two_pow_nu_le_real_of_couplings_eq_one`).
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace BP

variable {E : Type*}

/-- Darts of the edge restriction to A, viewed as darts of the ambient edge type. -/
def dartIncl (A : Finset E) : Dart {e // e ∈ A} ↪ Dart E where
  toFun α := (α.1.1, α.2)
  inj' := by
    rintro ⟨⟨e, he⟩, d⟩ ⟨⟨f, hf⟩, d'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

@[simp] theorem dartIncl_apply (A : Finset E) (α : Dart {e // e ∈ A}) :
    dartIncl A α = (α.1.1, α.2) := rfl

theorem dartIncl_rev (A : Finset E) (α : Dart {e // e ∈ A}) :
    dartIncl A (rev α) = rev (dartIncl A α) := rfl

/-- Restriction of messages to the darts of the edge restriction to A. -/
def restrictMsg {K : Type*} (A : Finset E) (y : Dart E → K) : Dart {e // e ∈ A} → K :=
  fun α => y (dartIncl A α)

/-- Extension of messages on the darts of the edge restriction to A by 1 on the other darts. -/
def extendMsg {K : Type*} [One K] [DecidableEq E] (A : Finset E) (y : Dart {e // e ∈ A} → K) :
    Dart E → K :=
  fun α => if h : α.1 ∈ A then y (⟨α.1, h⟩, α.2) else 1

variable [DecidableEq E] {K : Type*} [One K] {A : Finset E}

@[simp] theorem extendMsg_dartIncl (y : Dart {e // e ∈ A} → K) (α : Dart {e // e ∈ A}) :
    extendMsg A y (dartIncl A α) = y α := by
  rcases α with ⟨⟨e, he⟩, d⟩
  simp [extendMsg, he]

theorem extendMsg_of_not_mem (y : Dart {e // e ∈ A} → K) {α : Dart E} (h : α.1 ∉ A) :
    extendMsg A y α = 1 := by
  simp [extendMsg, h]

@[simp] theorem restrictMsg_extendMsg (y : Dart {e // e ∈ A} → K) :
    restrictMsg A (extendMsg A y) = y :=
  funext fun α => extendMsg_dartIncl y α

theorem extendMsg_restrictMsg {y : Dart E → K} (hy : ∀ α : Dart E, α.1 ∉ A → y α = 1) :
    extendMsg A (restrictMsg A y) = y := by
  funext α
  by_cases h : α.1 ∈ A
  · simp [extendMsg, h, restrictMsg]
  · rw [extendMsg_of_not_mem _ h, hy α h]

/-- A product over a filter of darts is a product over darts of the restriction to A when
the factors equal 1 off A. -/
@[to_additive /-- A sum over a filter of darts is a sum over darts of the restriction to A
when the terms vanish off A. -/]
theorem prod_filter_eq_prod_dartIncl {M : Type*} [CommMonoid M] [Fintype E] (A : Finset E)
    (y : Dart E → M) (hy : ∀ γ : Dart E, γ.1 ∉ A → y γ = 1) (p : Dart E → Prop)
    [DecidablePred p] :
    ∏ γ ∈ Finset.univ.filter p, y γ =
      ∏ γ ∈ Finset.univ.filter (fun γ : Dart {e // e ∈ A} => p (dartIncl A γ)),
        y (dartIncl A γ) := by
  rw [← Finset.prod_map _ (dartIncl A) y]
  symm
  apply Finset.prod_subset
  · intro γ hγ
    obtain ⟨γ', hγ', rfl⟩ := Finset.mem_map.1 hγ
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hγ').2⟩
  · intro γ hγ hγ'
    apply hy
    intro hA
    apply hγ'
    refine Finset.mem_map.2 ⟨(⟨γ.1, hA⟩, γ.2), ?_, rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hγ).2⟩

end BP

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-! ### Darts of the edge restriction -/

theorem edgeRestrict_head (A : Finset E) (α : Dart {e // e ∈ A}) :
    (G.edgeRestrict A).head α = G.head (dartIncl A α) := by
  rcases α with ⟨e, _ | _⟩ <;> rfl

theorem edgeRestrict_tail (A : Finset E) (α : Dart {e // e ∈ A}) :
    (G.edgeRestrict A).tail α = G.tail (dartIncl A α) := by
  rcases α with ⟨e, _ | _⟩ <;> rfl

/-- The edge restriction of a loopless graph is loopless. -/
theorem edgeRestrict_loopless (hG : G.Loopless) (A : Finset E) : (G.edgeRestrict A).Loopless :=
  fun e => hG e.1

theorem inDarts_erase_eq (v : V) (β : Dart E) :
    (G.inDarts v).erase β = Finset.univ.filter fun γ => G.head γ = v ∧ γ ≠ β := by
  ext γ
  simp [inDarts, and_comm]

/-- The cavity product of G at a dart of G' is the cavity product of G' when the factors
equal 1 off A. -/
@[to_additive /-- The cavity sum of G at a dart of G' is the cavity sum of G' when the terms
vanish off A. -/]
theorem prod_inDarts_erase_dartIncl {M : Type*} [CommMonoid M] {A : Finset E}
    (f : Dart E → M) (hf : ∀ γ : Dart E, γ.1 ∉ A → f γ = 1) (α : Dart {e // e ∈ A}) :
    ∏ γ ∈ (G.inDarts (G.tail (dartIncl A α))).erase (rev (dartIncl A α)), f γ =
      ∏ γ ∈ ((G.edgeRestrict A).inDarts ((G.edgeRestrict A).tail α)).erase (rev α),
        f (dartIncl A γ) := by
  rw [inDarts_erase_eq, inDarts_erase_eq, prod_filter_eq_prod_dartIncl A f hf]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext γ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, edgeRestrict_head, edgeRestrict_tail,
    ← dartIncl_rev, (dartIncl A).injective.ne_iff]

section General

variable {K : Type*} [Field K] {A : Finset E}

/-- Cavity fields agree on the darts of the edge restriction when the messages equal 1 off A. -/
theorem edgeRestrict_cavity {y : Dart E → K} (hy : ∀ γ : Dart E, γ.1 ∉ A → y γ = 1)
    (b : V → K) (α : Dart {e // e ∈ A}) :
    (G.edgeRestrict A).cavity b (restrictMsg A y) α = G.cavity b y (dartIncl A α) := by
  unfold cavity
  rw [G.prod_inDarts_erase_dartIncl y hy α, edgeRestrict_tail]
  rfl

/-- Total fields agree when the messages equal 1 off A. -/
theorem edgeRestrict_totalField {y : Dart E → K} (hy : ∀ γ : Dart E, γ.1 ∉ A → y γ = 1)
    (b : V → K) (i : V) :
    (G.edgeRestrict A).totalField b (restrictMsg A y) i = G.totalField b y i := by
  unfold totalField inDarts
  rw [prod_filter_eq_prod_dartIncl A y hy]
  rfl

variable {a : E → K} {b : V → K}

/-- **Messages on zero couplings.** At an admissible solution, a message on an edge with
a_e = 1 equals 1. No reality or positivity is used. -/
theorem msg_eq_one_of_coupling_eq_one {y : Dart E → K} (hy : G.IsAdmissibleSolution a b y)
    {α : Dart E} (hα : a α.1 = 1) : y α = 1 := by
  have h := hy.1 α
  have hd := hy.2.2.1 α
  unfold bpPoly at h
  rw [hα] at h hd
  have h' : (y α - 1) * (G.cavity b y α + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h' with h1 | h1
  · linear_combination h1
  · exact absurd h1 hd

/-- On a dart whose reverse message is 1, the cavity field is the total field at the tail. -/
theorem cavity_eq_totalField_of_rev_eq_one {y : Dart E → K} {α : Dart E}
    (h : y (rev α) = 1) : G.cavity b y α = G.totalField b y (G.tail α) := by
  rw [G.totalField_tail_eq b y α, h, mul_one]

/-- On a deleted dart, the cavity field of the extended messages is the total field of G'
at the tail. -/
theorem cavity_extendMsg_of_not_mem (y : Dart {e // e ∈ A} → K) {α : Dart E} (h : α.1 ∉ A) :
    G.cavity b (extendMsg A y) α = (G.edgeRestrict A).totalField b y (G.tail α) := by
  have hone : ∀ γ : Dart E, γ.1 ∉ A → extendMsg A y γ = 1 :=
    fun γ hγ => extendMsg_of_not_mem y hγ
  rw [G.cavity_eq_totalField_of_rev_eq_one (hone _ h), ← G.edgeRestrict_totalField hone,
    restrictMsg_extendMsg]

variable (hA : ∀ e, e ∉ A → a e = 1)
include hA

/-- Restriction of an admissible solution of G is an admissible solution of G' with the
restricted couplings. -/
theorem isAdmissibleSolution_restrictMsg {y : Dart E → K} (hy : G.IsAdmissibleSolution a b y) :
    (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b (restrictMsg A y) := by
  have hone : ∀ γ : Dart E, γ.1 ∉ A → y γ = 1 :=
    fun γ hγ => G.msg_eq_one_of_coupling_eq_one hy (hA _ hγ)
  refine ⟨fun α => ?_, fun α => hy.2.1 _, fun α => ?_, fun i => ?_⟩
  · have h := hy.1 (dartIncl A α)
    unfold bpPoly at h ⊢
    rw [G.edgeRestrict_cavity hone]
    exact h
  · rw [G.edgeRestrict_cavity hone]
    exact hy.2.2.1 _
  · rw [G.edgeRestrict_totalField hone]
    exact hy.2.2.2 i

/-- **Reverse construction.** Extension by 1 of an admissible solution of G' is an
admissible solution of G. The new update denominators X_α + 1 = F_{t(α)} + 1 are nonzero by
the vertex condition in G'. -/
theorem isAdmissibleSolution_extendMsg {y : Dart {e // e ∈ A} → K}
    (hy : (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y) :
    G.IsAdmissibleSolution a b (extendMsg A y) := by
  have hone : ∀ γ : Dart E, γ.1 ∉ A → extendMsg A y γ = 1 :=
    fun γ hγ => extendMsg_of_not_mem y hγ
  have hcav : ∀ α : Dart {e // e ∈ A},
      G.cavity b (extendMsg A y) (dartIncl A α) = (G.edgeRestrict A).cavity b y α := by
    intro α
    rw [← G.edgeRestrict_cavity hone, restrictMsg_extendMsg]
  refine ⟨fun α => ?_, fun α => ?_, fun α => ?_, fun i => ?_⟩
  · by_cases h : α.1 ∈ A
    · have hα : α = dartIncl A (⟨α.1, h⟩, α.2) := rfl
      rw [hα]
      have h' := hy.1 (⟨α.1, h⟩, α.2)
      unfold bpPoly at h' ⊢
      rw [hcav, extendMsg_dartIncl]
      exact h'
    · unfold bpPoly
      rw [hone α h, hA _ h]
      ring
  · by_cases h : α.1 ∈ A
    · have hα : α = dartIncl A (⟨α.1, h⟩, α.2) := rfl
      rw [hα, extendMsg_dartIncl]
      exact hy.2.1 _
    · rw [hone α h]
      exact one_ne_zero
  · by_cases h : α.1 ∈ A
    · have hα : α = dartIncl A (⟨α.1, h⟩, α.2) := rfl
      rw [hα, hcav]
      exact hy.2.2.1 _
    · rw [G.cavity_extendMsg_of_not_mem y h, hA _ h, add_comm]
      exact hy.2.2.2 _
  · rw [← G.edgeRestrict_totalField hone, restrictMsg_extendMsg]
    exact hy.2.2.2 i

/-- **Bijection of admissible solution sets.** If a_e = 1 for every edge outside A, then
restriction and extension by 1 identify the admissible solutions of G with those of
G' = `G.edgeRestrict A` with the restricted couplings, over any field. -/
def zeroCouplingEquiv :
    {y : Dart E → K // G.IsAdmissibleSolution a b y} ≃
      {y : Dart {e // e ∈ A} → K //
        (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y} where
  toFun y := ⟨restrictMsg A y.1, G.isAdmissibleSolution_restrictMsg hA y.2⟩
  invFun y := ⟨extendMsg A y.1, G.isAdmissibleSolution_extendMsg hA y.2⟩
  left_inv y := Subtype.ext (extendMsg_restrictMsg fun _ hγ =>
    G.msg_eq_one_of_coupling_eq_one y.2 (hA _ hγ))
  right_inv y := Subtype.ext (restrictMsg_extendMsg y.1)

@[simp] theorem zeroCouplingEquiv_apply (y : {y : Dart E → K // G.IsAdmissibleSolution a b y}) :
    (G.zeroCouplingEquiv hA y).1 = restrictMsg A y.1 := rfl

@[simp] theorem zeroCouplingEquiv_symm_apply
    (y : {y : Dart {e // e ∈ A} → K //
      (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y}) :
    ((G.zeroCouplingEquiv hA).symm y).1 = extendMsg A y.1 := rfl

end General

/-! ### Simplicity -/

section Simple

variable {K : Type*} [Field K] {A : Finset E} {a : E → K} {b : V → K}

/-- On a dart with a_e = 1 and y_α = 1 the Jacobian row is (X_α + 1) w_α. -/
theorem jacobian_mulVec_of_coupling_eq_one {y : Dart E → K} (hy0 : ∀ γ, y γ ≠ 0)
    (w : Dart E → K) {α : Dart E} (ha : a α.1 = 1) (hyα : y α = 1) :
    (G.jacobian a b y).mulVec w α = (G.cavity b y α + 1) * w α := by
  rw [G.jacobian_mulVec_row hy0 w α, hyα, ha]
  ring

/-- On the darts of G', the Jacobian of G at an extension by 1 agrees with the Jacobian of G'
on vectors vanishing off A. -/
theorem jacobian_mulVec_dartIncl {y : Dart {e // e ∈ A} → K} (hy0 : ∀ γ, y γ ≠ 0)
    {w : Dart E → K} (hw : ∀ γ : Dart E, γ.1 ∉ A → w γ = 0) (α : Dart {e // e ∈ A}) :
    (G.jacobian a b (extendMsg A y)).mulVec w (dartIncl A α) =
      ((G.edgeRestrict A).jacobian (fun e => a e.1) b y).mulVec (restrictMsg A w) α := by
  have hone : ∀ γ : Dart E, γ.1 ∉ A → extendMsg A y γ = 1 :=
    fun γ hγ => extendMsg_of_not_mem y hγ
  have hy0' : ∀ γ, extendMsg A y γ ≠ 0 := by
    intro γ
    by_cases h : γ.1 ∈ A
    · have hγ : γ = dartIncl A (⟨γ.1, h⟩, γ.2) := rfl
      rw [hγ, extendMsg_dartIncl]
      exact hy0 _
    · rw [hone γ h]
      exact one_ne_zero
  have hcav := G.edgeRestrict_cavity hone b α
  rw [restrictMsg_extendMsg] at hcav
  rw [G.jacobian_mulVec_row hy0' w, (G.edgeRestrict A).jacobian_mulVec_row hy0 (restrictMsg A w),
    G.sum_inDarts_erase_dartIncl (fun γ => w γ / extendMsg A y γ)
      (fun γ hγ => by simp [hw γ hγ]) α, ← hcav]
  simp only [extendMsg_dartIncl, restrictMsg]
  rfl

/-- **Simplicity is preserved.** If a_e = 1 off A, an admissible solution of G' is simple
(nonzero Jacobian determinant) exactly when its extension by 1 is a simple solution of G. -/
theorem isSimpleSolution_extendMsg_iff (hA : ∀ e, e ∉ A → a e = 1)
    {y : Dart {e // e ∈ A} → K}
    (hy : (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y) :
    G.IsSimpleSolution a b (extendMsg A y) ↔
      (G.edgeRestrict A).IsSimpleSolution (fun e => a e.1) b y := by
  have hyG := G.isAdmissibleSolution_extendMsg hA hy
  have hone : ∀ γ : Dart E, γ.1 ∉ A → extendMsg A y γ = 1 :=
    fun γ hγ => extendMsg_of_not_mem y hγ
  unfold IsSimpleSolution
  rw [ne_eq, ne_eq, not_iff_not, ← Matrix.exists_mulVec_eq_zero_iff,
    ← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨w, hw0, hw⟩
    have hwA : ∀ γ : Dart E, γ.1 ∉ A → w γ = 0 := by
      intro γ hγ
      have h1 := congrFun hw γ
      rw [Pi.zero_apply, G.jacobian_mulVec_of_coupling_eq_one hyG.2.1 w (hA _ hγ) (hone γ hγ)]
        at h1
      have hd := hyG.2.2.1 γ
      rw [hA _ hγ] at hd
      exact (mul_eq_zero.1 h1).resolve_left hd
    refine ⟨restrictMsg A w, fun h0 => hw0 ?_, ?_⟩
    · funext γ
      by_cases hγ : γ.1 ∈ A
      · exact congrFun h0 (⟨γ.1, hγ⟩, γ.2)
      · exact hwA γ hγ
    · funext α
      rw [← G.jacobian_mulVec_dartIncl hy.2.1 hwA α]
      exact congrFun hw _
  · rintro ⟨w, hw0, hw⟩
    let v : Dart E → K := fun γ => if h : γ.1 ∈ A then w (⟨γ.1, h⟩, γ.2) else 0
    have hvA : ∀ γ : Dart E, γ.1 ∉ A → v γ = 0 := fun γ hγ => by simp [v, hγ]
    have hvw : restrictMsg A v = w := funext fun γ => by
      rcases γ with ⟨⟨e, he⟩, d⟩
      simp [v, restrictMsg, he]
    refine ⟨v, fun h0 => hw0 ?_, ?_⟩
    · rw [← hvw, h0]
      rfl
    · funext α
      by_cases h : α.1 ∈ A
      · have hα : α = dartIncl A (⟨α.1, h⟩, α.2) := rfl
        rw [hα, G.jacobian_mulVec_dartIncl hy.2.1 hvA, hvw]
        exact congrFun hw _
      · rw [Pi.zero_apply, G.jacobian_mulVec_of_coupling_eq_one hyG.2.1 v (hA _ h) (hone α h),
          hvA α h, mul_zero]

/-- If a_e = 1 off A, an admissible solution of G is simple exactly when its restriction to
G' is simple. -/
theorem isSimpleSolution_iff_restrictMsg (hA : ∀ e, e ∉ A → a e = 1) {y : Dart E → K}
    (hy : G.IsAdmissibleSolution a b y) :
    G.IsSimpleSolution a b y ↔
      (G.edgeRestrict A).IsSimpleSolution (fun e => a e.1) b (restrictMsg A y) := by
  have hone : ∀ γ : Dart E, γ.1 ∉ A → y γ = 1 :=
    fun γ hγ => G.msg_eq_one_of_coupling_eq_one hy (hA _ hγ)
  conv_lhs => rw [← extendMsg_restrictMsg hone]
  exact G.isSimpleSolution_extendMsg_iff hA (G.isAdmissibleSolution_restrictMsg hA hy)

end Simple

/-! ### Real parameters -/

section Real

variable {A : Finset E} {a : E → ℝ} {b : V → ℝ}

/-- **New denominators are positive (`real:sign-sectors`).** For a > 0 and b > 0, extending an
admissible real solution of G' by 1 gives update denominators X_α + a_e = F_{t(α)} + 1 > 0 on
the deleted darts. -/
theorem cavity_extendMsg_add_pos (ha : ∀ e, 0 < a e) (hb : ∀ i, 0 < b i)
    (hA : ∀ e, e ∉ A → a e = 1) {y : Dart {e // e ∈ A} → ℝ}
    (hy : (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y) {α : Dart E}
    (h : α.1 ∉ A) : 0 < G.cavity b (extendMsg A y) α + a α.1 := by
  rw [G.cavity_extendMsg_of_not_mem y h, hA _ h]
  have := totalField_pos (a := fun e : {e // e ∈ A} => a e.1) (fun e => ha e.1) hb hy (G.tail α)
  linarith

/-- Restriction and extension by 1 also identify the admissible real solutions with all
messages positive. -/
def zeroCouplingPosEquiv (hA : ∀ e, e ∉ A → a e = 1) :
    {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} ≃
      {y : Dart {e // e ∈ A} → ℝ //
        (G.edgeRestrict A).IsAdmissibleSolution (fun e => a e.1) b y ∧ ∀ α, 0 < y α} where
  toFun y := ⟨restrictMsg A y.1, G.isAdmissibleSolution_restrictMsg hA y.2.1,
    fun α => y.2.2 _⟩
  invFun y := ⟨extendMsg A y.1, G.isAdmissibleSolution_extendMsg hA y.2.1, fun α => by
    by_cases h : α.1 ∈ A
    · have hα : α = dartIncl A (⟨α.1, h⟩, α.2) := rfl
      rw [hα, extendMsg_dartIncl]
      exact y.2.2 _
    · rw [extendMsg_of_not_mem _ h]
      exact one_pos⟩
  left_inv y := Subtype.ext (extendMsg_restrictMsg fun _ hγ =>
    G.msg_eq_one_of_coupling_eq_one y.2.1 (hA _ hγ))
  right_inv y := Subtype.ext (restrictMsg_extendMsg y.1)

/-- The negative-message support of an extension by 1 is the image of the negative-message
support in G'. -/
theorem negSupport_extendMsg (y : Dart {e // e ∈ A} → ℝ) :
    negSupport (extendMsg A y) = (negSupport y).map (Function.Embedding.subtype _) := by
  ext e
  simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.subtype_apply]
  by_cases he : e ∈ A
  · constructor
    · intro h
      refine ⟨⟨e, he⟩, ?_, rfl⟩
      simpa [extendMsg, he] using h
    · rintro ⟨e', h, rfl⟩
      simpa [extendMsg, e'.2] using h
  · rw [extendMsg_of_not_mem y (α := (e, true)) he]
    constructor
    · intro h
      exact absurd h (by norm_num)
    · rintro ⟨e', -, rfl⟩
      exact absurd e'.2 he

variable (hG : G.Loopless) (ha : ∀ e, 0 < a e) (hA : ∀ e, e ∉ A → a e = 1)
  (hA1 : ∀ e ∈ A, a e ≠ 1)
include hG ha hA hA1

/-- **Sectors (`thm:real` (ii) for G').** At every positive field, every Eulerian edge set of
G' is, as an edge set of G, the negative-message support of an admissible real root of G. -/
theorem zeroCoupling_sector (hb : ∀ i, 0 < b i) {S : Finset {e // e ∈ A}}
    (hS : (G.edgeRestrict A).IsEvenSet S) :
    ∃ y, G.IsAdmissibleSolution a b y ∧ negSupport y = S.map (Function.Embedding.subtype _) := by
  obtain ⟨y, hy, hyS⟩ := exists_real_solution (a := fun e : {e // e ∈ A} => a e.1)
    (fun e => ha e.1) (fun e => hA1 e.1 e.2) (G.edgeRestrict_loopless hG A) hS hb
  exact ⟨extendMsg A y, G.isAdmissibleSolution_extendMsg hA hy, by
    rw [negSupport_extendMsg, hyS]⟩

/-- **Negative supports.** At every positive field, the negative-message supports of the
admissible real roots of G are exactly the Eulerian edge sets of G contained in A. -/
theorem zeroCoupling_negSupport_iff (hb : ∀ i, 0 < b i) (S : Finset E) :
    (∃ y, G.IsAdmissibleSolution a b y ∧ negSupport y = S) ↔ S ⊆ A ∧ G.IsEvenSet S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun e he => ?_, isEvenSet_negSupport hG ha hb hy⟩
    by_contra h
    have h1 := G.msg_eq_one_of_coupling_eq_one hy (α := (e, true)) (hA e h)
    simp only [negSupport, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [h1] at he
    norm_num at he
  · rintro ⟨hSA, hS⟩
    have hmap : (S.subtype (· ∈ A)).map (Function.Embedding.subtype _) = S :=
      Finset.subtype_map_of_mem fun e he => hSA he
    have hS' : (G.edgeRestrict A).IsEvenSet (S.subtype (· ∈ A)) := by
      rw [edgeRestrict_isEvenSet_iff, hmap]
      exact hS
    obtain ⟨y, hy, hyS⟩ := G.zeroCoupling_sector hG ha hA hA1 hb hS'
    exact ⟨y, hy, hyS.trans hmap⟩

/-- **Lower bound with the support graph.** At every positive field there are at least
2^{ν(G')} admissible real roots of G (`ENat.card`, so finiteness is not assumed). -/
theorem zeroCoupling_lower (hb : ∀ i, 0 < b i) :
    ((2 ^ (G.edgeRestrict A).nu : ℕ) : ℕ∞) ≤
      ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} := by
  rw [ENat.card_congr (G.zeroCouplingEquiv hA), ← card_evenSets_eq_two_pow_nu]
  exact card_evenSets_le_real (a := fun e : {e // e ∈ A} => a e.1) (fun e => ha e.1)
    (fun e => hA1 e.1 e.2) (G.edgeRestrict_loopless hG A) hb

/-- **Minimum with the support graph.** min_h R_G(J, h) = 2^{ν(G')}: at least 2^{ν(G')} at
every positive field, and exactly 2^{ν(G')} (finitely many, exactly one positive) at some
positive field. -/
theorem zeroCoupling_min :
    (∀ b : V → ℝ, (∀ i, 0 < b i) →
        ((2 ^ (G.edgeRestrict A).nu : ℕ) : ℕ∞) ≤
          ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) ∧
      ∃ b : V → ℝ, (∀ i, 0 < b i) ∧
        Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 2 ^ (G.edgeRestrict A).nu ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  refine ⟨fun b hb => G.zeroCoupling_lower hG ha hA hA1 hb, ?_⟩
  obtain ⟨-, b, hb, hfin, hcard, hpos⟩ := min_real_count (a := fun e : {e // e ∈ A} => a e.1)
    (fun e => ha e.1) (fun e => hA1 e.1 e.2) (G.edgeRestrict_loopless hG A)
  rw [card_evenSets_eq_two_pow_nu] at hcard
  refine ⟨b, hb, (G.zeroCouplingEquiv hA).finite_iff.2 hfin, ?_, ?_⟩
  · rw [Nat.card_congr (G.zeroCouplingEquiv hA), hcard]
  · rw [Nat.card_congr (G.zeroCouplingPosEquiv hA), hpos]

/-- **Strong fields with the support graph.** If |log b_i| is large at every vertex (any
signs), the complex, real and positive counts of G are (Q(G'), 2^{ν(G')}, 1), and all complex
admissible roots of G are simple. -/
theorem zeroCoupling_strong :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      Nat.card {y : Dart E → ℂ //
          G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y} =
        (G.edgeRestrict A).Q ∧
      (∀ y, G.IsAdmissibleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y →
        G.IsSimpleSolution (fun e => (a e : ℂ)) (fun i => (b i : ℂ)) y) ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 2 ^ (G.edgeRestrict A).nu ∧
      Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 := by
  obtain ⟨H, hH⟩ := strong_field_three_counts (G.edgeRestrict A) (G.edgeRestrict_loopless hG A)
    (a := fun e : {e // e ∈ A} => a e.1) (fun e => ha e.1) (fun e => hA1 e.1 e.2)
  refine ⟨H, fun b hb hbH => ?_⟩
  obtain ⟨hC, hS, hR, hP⟩ := hH b hb hbH
  have hAC : ∀ e, e ∉ A → (a e : ℂ) = 1 := fun e he => by rw [hA e he, Complex.ofReal_one]
  refine ⟨?_, fun y hy => ?_, ?_, ?_⟩
  · rw [Nat.card_congr (G.zeroCouplingEquiv (a := fun e => (a e : ℂ)) (b := fun i => (b i : ℂ))
      hAC), hC]
  · have hy' := G.isAdmissibleSolution_restrictMsg hAC hy
    exact (G.isSimpleSolution_iff_restrictMsg hAC hy).2 (hS _ hy')
  · rw [Nat.card_congr (G.zeroCouplingEquiv hA), hR, card_evenSets_eq_two_pow_nu]
  · rw [Nat.card_congr (G.zeroCouplingPosEquiv hA), hP]

end Real

/-! ### The statements of `supp:zero-couplings` -/

section Paper

variable {a : E → ℝ} {b : V → ℝ}

/-- **(`supp:zero-couplings`) Messages on zero couplings.** For a set Z of edges with a_e = 1
(J_e = 0), every admissible real solution has message 1 on both darts of every edge of Z. The
positivity hypotheses a_e > 0, b_i > 0 are not needed (see `msg_eq_one_of_coupling_eq_one`,
valid over any field). -/
theorem zero_couplings_msg_eq_one {Z : Finset E} (hZ : ∀ e ∈ Z, a e = 1) {y : Dart E → ℝ}
    (hy : G.IsAdmissibleSolution a b y) {e : E} (he : e ∈ Z) :
    y (e, true) = 1 ∧ y (e, false) = 1 :=
  ⟨G.msg_eq_one_of_coupling_eq_one hy (hZ e he), G.msg_eq_one_of_coupling_eq_one hy (hZ e he)⟩

/-- **(`supp:zero-couplings`) Bijection.** If a_e = 1 for every edge of Z, the admissible real
solutions of G correspond bijectively, by restriction of messages and extension by 1, to the
admissible real solutions of the graph G − Z = `G.edgeRestrict Zᶜ` (all vertices kept) with the
restricted couplings. -/
noncomputable def zero_couplings_equiv {Z : Finset E} (hZ : ∀ e ∈ Z, a e = 1) :
    {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ≃
      {y : Dart {e // e ∈ Zᶜ} → ℝ //
        (G.edgeRestrict Zᶜ).IsAdmissibleSolution (fun e => a e.1) b y} :=
  G.zeroCouplingEquiv fun e he => hZ e (by simpa using he)

/-- **(`supp:zero-couplings`) Lower bound.** For a_e > 0, b_i > 0, a_e = 1 on Z and a_e ≠ 1 off
Z, R_G(J, h) ≥ 2^{ν(G − Z)}. -/
theorem zero_couplings_lower (hG : G.Loopless) (ha : ∀ e, 0 < a e) {Z : Finset E}
    (hZ : ∀ e ∈ Z, a e = 1) (hZ1 : ∀ e ∉ Z, a e ≠ 1) (hb : ∀ i, 0 < b i) :
    ((2 ^ (G.edgeRestrict Zᶜ).nu : ℕ) : ℕ∞) ≤
      ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} :=
  G.zeroCoupling_lower hG ha (fun e he => hZ e (by simpa using he))
    (fun e he => hZ1 e (by simpa using he)) hb

/-- **(`supp:zero-couplings`) Minimum.** For a_e > 0, a_e = 1 on Z and a_e ≠ 1 off Z,
min_h R_G(J, h) = 2^{ν(G − Z)}. -/
theorem zero_couplings_min (hG : G.Loopless) (ha : ∀ e, 0 < a e) {Z : Finset E}
    (hZ : ∀ e ∈ Z, a e = 1) (hZ1 : ∀ e ∉ Z, a e ≠ 1) :
    (∀ b : V → ℝ, (∀ i, 0 < b i) →
        ((2 ^ (G.edgeRestrict Zᶜ).nu : ℕ) : ℕ∞) ≤
          ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) ∧
      ∃ b : V → ℝ, (∀ i, 0 < b i) ∧
        Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 2 ^ (G.edgeRestrict Zᶜ).nu ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 :=
  G.zeroCoupling_min hG ha (fun e he => hZ e (by simpa using he))
    (fun e he => hZ1 e (by simpa using he))

/-- The support of the couplings: the edges with a_e ≠ 1 (J_e ≠ 0). -/
noncomputable def couplingSupport (a : E → ℝ) : Finset E :=
  Finset.univ.filter fun e => a e ≠ 1

@[simp] theorem mem_couplingSupport {a : E → ℝ} {e : E} : e ∈ couplingSupport a ↔ a e ≠ 1 := by
  simp [couplingSupport]

/-- **(`supp:zero-couplings`) Minimum with the support graph.** For arbitrary couplings
a_e > 0 (a_e = 1 allowed), min_h R_G(J, h) = 2^{ν(G_J)}, where G_J = `G.edgeRestrict
(couplingSupport a)` keeps exactly the edges with J_e ≠ 0. -/
theorem zero_couplings_min_support (hG : G.Loopless) (ha : ∀ e, 0 < a e) :
    (∀ b : V → ℝ, (∀ i, 0 < b i) →
        ((2 ^ (G.edgeRestrict (couplingSupport a)).nu : ℕ) : ℕ∞) ≤
          ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y}) ∧
      ∃ b : V → ℝ, (∀ i, 0 < b i) ∧
        Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} =
          2 ^ (G.edgeRestrict (couplingSupport a)).nu ∧
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ ∀ α, 0 < y α} = 1 :=
  G.zeroCoupling_min hG ha (fun e he => by simpa using he) (fun e he => by simpa using he)

/-- **All couplings equal to 1.** If a_e = 1 for every edge, then at every positive field the
only admissible real solution is y ≡ 1. -/
theorem card_real_of_couplings_eq_one (h1 : ∀ e, a e = 1) (hb : ∀ i, 0 < b i) :
    Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} = 1 := by
  have hX : ∀ α, G.cavity b (fun _ => (1 : ℝ)) α = b (G.tail α) := fun α => by simp [cavity]
  have hF : ∀ i, G.totalField b (fun _ => (1 : ℝ)) i = b i := fun i => by simp [totalField]
  have hsol : G.IsAdmissibleSolution a b (fun _ => 1) := by
    refine ⟨fun α => ?_, fun _ => one_ne_zero, fun α => ?_, fun i => ?_⟩
    · unfold bpPoly
      rw [h1]
      ring
    · rw [hX, h1]
      exact (by linarith [hb (G.tail α)] : (0 : ℝ) < b (G.tail α) + 1).ne'
    · rw [hF]
      exact (by linarith [hb i] : (0 : ℝ) < 1 + b i).ne'
  rw [Nat.card_eq_one_iff_exists]
  exact ⟨⟨_, hsol⟩, fun y => Subtype.ext (funext fun α =>
    G.msg_eq_one_of_coupling_eq_one y.2 (h1 α.1))⟩

/-- **The nonzero-coupling hypothesis is essential for the bound with ν(G).** If a_e = 1 for
every edge and ν(G) ≥ 1, then at every positive field R_G(J, h) = 1 < 2^{ν(G)}, so the
conclusion of `thm:real` (ii) with the cycle rank of G fails. -/
theorem not_two_pow_nu_le_real_of_couplings_eq_one (h1 : ∀ e, a e = 1) (hb : ∀ i, 0 < b i)
    (hν : 0 < G.nu) :
    ¬ ((2 ^ G.nu : ℕ) : ℕ∞) ≤ ENat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} := by
  have hcard := G.card_real_of_couplings_eq_one h1 hb
  have : Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact one_ne_zero)
  rw [ENat.card_eq_coe_natCard, hcard, Nat.cast_le, not_le]
  exact Nat.one_lt_two_pow hν.ne'

end Paper

end Multigraph

end BPFixedPoints
