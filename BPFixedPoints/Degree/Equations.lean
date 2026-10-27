import BPFixedPoints.StateSum.Basic

/-!
# BP equations in message-ratio coordinates

Define binary Ising BP on a loopless multigraph G over a field K.
Darts are E×Bool: (e,true) goes from fst e to snd e; false reverses it.
`rev`, `tail` and `head` give reversal and endpoints.
Parameters are a_e=exp(2J_e), b_i=exp(2h_i), with messages y:E×Bool→K.
The cavity field is X_α=b_{t(α)}∏_{h(γ)=t(α),γ≠ᾱ}y_γ, excluding only the
reverse dart of the same edge. BP is y_α=(a_e X_α+1)/(X_α+a_e), or
f_α=y_α(X_α+a_e)−(a_e X_α+1)=0. Total fields are F_i=b_i∏_{h(α)=i}y_α.
Admissibility D≠0 requires nonzero messages, update denominators X_α+a_e,
and normalization factors 1+F_i.

Also define A_{e,i}=X_{i,e}/a_e, s_e=a_e², β_i=b_i/∏_{e∋i}a_e and prove
auxiliary relations (4)–(5) and the one-edge quadratic (7).
The BP layer assumes `G.Loopless`.
-/

namespace BPFixedPoints

-- Suppress warnings about section variables unused by some lemmas.
set_option linter.unusedSectionVars false

namespace BP

variable {E : Type*}

/-- Directed edge (dart); (e,true) goes from fst e to snd e. -/
abbrev Dart (E : Type*) := E × Bool

/-- Reverse dart. -/
def rev (α : Dart E) : Dart E := (α.1, !α.2)

@[simp] theorem rev_rev (α : Dart E) : rev (rev α) = α := by
  cases α with | mk e d => cases d <;> rfl

@[simp] theorem rev_fst (α : Dart E) : (rev α).1 = α.1 := rfl

theorem rev_ne (α : Dart E) : rev α ≠ α := by
  cases α with | mk e d => cases d <;> simp [rev]

theorem rev_injective : Function.Injective (rev : Dart E → Dart E) :=
  Function.LeftInverse.injective rev_rev

end BP

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (G : Multigraph V E)

/-- Tail vertex. -/
def tail (α : Dart E) : V := cond α.2 (G.fst α.1) (G.snd α.1)

/-- Head vertex. -/
def head (α : Dart E) : V := cond α.2 (G.snd α.1) (G.fst α.1)

@[simp] theorem tail_rev (α : Dart E) : G.tail (rev α) = G.head α := by
  cases α with | mk e d => cases d <;> rfl

@[simp] theorem head_rev (α : Dart E) : G.head (rev α) = G.tail α := by
  cases α with | mk e d => cases d <;> rfl

theorem tail_ne_head (hG : G.Loopless) (α : Dart E) : G.tail α ≠ G.head α := by
  rcases α with ⟨e, _ | _⟩
  · exact (hG e).symm
  · exact hG e

/-- Darts whose head is i. -/
def inDarts (i : V) : Finset (Dart E) := Finset.univ.filter fun α => G.head α = i

/-- Degree of i, counted by incoming darts; for a loopless graph this is G.deg univ i. -/
def degree (i : V) : ℕ := (G.inDarts i).card

/-- Dart degree equals edge-set degree with multiplicities, counting a loop twice. -/
theorem degree_eq_deg (i : V) : G.degree i = G.deg Finset.univ i := by
  unfold degree inDarts Multigraph.deg
  rw [Finset.card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro e _
  rw [Fintype.sum_bool]
  simp only [head, Bool.cond_true, Bool.cond_false, Multigraph.endCount]
  exact add_comm _ _

section Messages

variable {K : Type*} [Field K]
variable (a : E → K) (b : V → K) (y : Dart E → K)

/-- Cavity field X_α=b_tailα product_{head γ=tail α,γ≠rev α} y_γ. -/
def cavity (α : Dart E) : K :=
  b (G.tail α) * ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), y γ

/-- Cleared-denominator BP polynomial f_α=y_α(X_α+a_e)-(a_e X_α+1). -/
def bpPoly (α : Dart E) : K :=
  y α * (G.cavity b y α + a α.1) - (a α.1 * G.cavity b y α + 1)

/-- Full field F_i=b_i product_{head α=i} y_α. -/
def totalField (i : V) : K := b i * ∏ α ∈ G.inDarts i, y α

/-- Fixed point of the polynomial system. -/
def IsFixedPoint : Prop := ∀ α, G.bpPoly a b y α = 0

/-- Rational BP update, when its denominator is nonzero. -/
def IsRationalFixedPoint : Prop :=
  ∀ α, G.cavity b y α + a α.1 ≠ 0 ∧ y α = (a α.1 * G.cavity b y α + 1) / (G.cavity b y α + a α.1)

/-- Admissibility D≠0: nonzero messages, update denominators and vertex normalization factors. -/
def Admissible : Prop :=
  (∀ α, y α ≠ 0) ∧ (∀ α, G.cavity b y α + a α.1 ≠ 0) ∧ (∀ i, 1 + G.totalField b y i ≠ 0)

/-- Admissible BP solution: a polynomial fixed point with D≠0. -/
def IsAdmissibleSolution : Prop := G.IsFixedPoint a b y ∧ G.Admissible a b y

/-- Where update denominators are nonzero, rational BP updates are equivalent to the polynomial system. -/
theorem isFixedPoint_iff_isRationalFixedPoint (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0) :
    G.IsFixedPoint a b y ↔ G.IsRationalFixedPoint a b y := by
  constructor
  · intro h α
    refine ⟨hden α, ?_⟩
    have := h α
    unfold bpPoly at this
    rw [eq_div_iff (hden α)]
    linear_combination this
  · intro h α
    obtain ⟨hd, hy⟩ := h α
    unfold bpPoly
    rw [hy, div_mul_cancel₀ _ hd]
    ring

/-- At a rational fixed point with nonzero messages, message numerators are also nonzero. -/
theorem rev_mem_inDarts (α : Dart E) : rev α ∈ G.inDarts (G.tail α) := by
  simp [inDarts]

/-- Total/cavity field relation: F_{t(α)}=X_α·y_ᾱ. -/
theorem totalField_tail_eq (α : Dart E) :
    G.totalField b y (G.tail α) = G.cavity b y α * y (rev α) := by
  unfold totalField cavity
  rw [← Finset.mul_prod_erase (G.inDarts (G.tail α)) y (G.rev_mem_inDarts α)]
  ring

/-- Normalization identity: (1+F_i)(Y+a)=aXY+X+Y+a, with X=X_α, Y=X_ᾱ, i=t(α). -/
theorem normalization_identity (hfix : G.IsFixedPoint a b y) (α : Dart E) :
    (1 + G.totalField b y (G.tail α)) * (G.cavity b y (rev α) + a α.1) =
      a α.1 * G.cavity b y α * G.cavity b y (rev α) + G.cavity b y α +
        G.cavity b y (rev α) + a α.1 := by
  rw [G.totalField_tail_eq b y α]
  have h := hfix (rev α)
  unfold bpPoly at h
  rw [rev_fst] at h
  linear_combination G.cavity b y α * h

/-- The full fields of an admissible solution are nonzero. -/
theorem totalField_ne_zero (hb : ∀ i, b i ≠ 0) (hy : ∀ α, y α ≠ 0) (i : V) : G.totalField b y i ≠ 0 := by
  unfold totalField
  exact mul_ne_zero (hb i) (Finset.prod_ne_zero_iff.2 fun α _ => hy α)

end Messages

section Auxiliary

/-!
## Auxiliary coordinates

A α=X_α/a_e at the tail i=t(α), s e=a_e², and β i=b_i/∏_{e∋i}a_e.
-/

variable {K : Type*} [Field K]
variable (a : E → K) (b : V → K) (y : Dart E → K)

/-- `s_e = a_e²`。 -/
def auxS {K : Type*} [Field K] (a : E → K) (e : E) : K := a e ^ 2

/-- Auxiliary coordinate A_{e,i}=X_{i,e}/a_e at the tail of dart α. -/
def auxA (α : Dart E) : K := G.cavity b y α / a α.1

/-- `β_i = b_i / ∏_{e∋i} a_e`。 -/
def auxBeta (i : V) : K := b i / ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), a e

/-- Forgetting the direction of darts with head i gives edges incident to i. -/
theorem image_inDarts_fst (i : V) :
    (G.inDarts i).image Prod.fst = Finset.univ.filter (fun e => G.Incident e i) := by
  ext e
  rw [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨e', d⟩, hd, rfl⟩
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [inDarts, Finset.mem_filter] at hd
    cases d
    · exact Or.inl hd.2
    · exact Or.inr hd.2
  · rintro ⟨_, h⟩
    rcases h with h | h
    · exact ⟨(e, false), by rw [inDarts, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩, rfl⟩
    · exact ⟨(e, true), by rw [inDarts, Finset.mem_filter]; exact ⟨Finset.mem_univ _, h⟩, rfl⟩

/-- For a loopless graph, darts with head i correspond bijectively to edges incident to i. -/
theorem prod_inDarts_edge (hG : G.Loopless) (i : V) (g : E → K) :
    ∏ α ∈ G.inDarts i, g α.1 = ∏ e ∈ Finset.univ.filter (fun e => G.Incident e i), g e := by
  rw [← G.image_inDarts_fst i, Finset.prod_image]
  rintro ⟨e, d⟩ hα ⟨e', d'⟩ hα' h
  simp only [inDarts, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hα hα'
  simp only at h
  subst h
  cases d <;> cases d'
  · rfl
  · exact absurd (hα.trans hα'.symm) (hG e)
  · exact absurd (hα'.trans hα.symm) (hG e)
  · rfl

/-- Edge equation (`eq:aux-edge`): at an admissible fixed point, F_i=A_{e,i}(1+s_e A_{e,j})/(1+A_{e,j}), where i=t(α), j=h(α), s_e=a_e². -/
theorem field_eq_auxA (hfix : G.IsFixedPoint a b y) (ha : ∀ e, a e ≠ 0)
    (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0) (α : Dart E) :
    G.totalField b y (G.tail α) =
      G.auxA a b y α * (1 + a α.1 ^ 2 * G.auxA a b y (rev α)) / (1 + G.auxA a b y (rev α)) := by
  have hB : 1 + G.auxA a b y (rev α) ≠ 0 := by
    unfold auxA
    rw [rev_fst]
    intro h
    apply hden (rev α)
    rw [rev_fst]
    have := ha α.1
    field_simp at h
    linear_combination h
  rw [G.totalField_tail_eq b y α, eq_div_iff hB]
  have h := hfix (rev α)
  unfold bpPoly at h
  rw [rev_fst] at h
  unfold auxA
  rw [rev_fst]
  have ha' := ha α.1
  have hd := hden (rev α)
  rw [rev_fst] at hd
  field_simp
  linear_combination G.cavity b y α * h

/-- The cavity field is the full field divided by the incoming message on that edge: X_revα=F_headα/y_α. -/
theorem cavity_rev_eq (hy : ∀ α, y α ≠ 0) (α : Dart E) :
    G.cavity b y (rev α) = G.totalField b y (G.head α) / y α := by
  have h := G.totalField_tail_eq b y (rev α)
  rw [tail_rev, rev_rev] at h
  rw [eq_div_iff (hy α), h]

/-- Vertex equation (`eq:aux-vertex`): at an admissible fixed point, β_i=F_i^{1−d_i}∏_{e∋i}A_{e,i}. -/
theorem auxBeta_eq (hG : G.Loopless) (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0)
    (hy : ∀ α, y α ≠ 0) (i : V) :
    G.auxBeta a b i =
      G.totalField b y i ^ ((1 : ℤ) - G.degree i) * ∏ α ∈ G.inDarts i, G.auxA a b y (rev α) := by
  have hF : G.totalField b y i ≠ 0 := G.totalField_ne_zero b y hb hy i
  have hprodA : ∏ α ∈ G.inDarts i, G.auxA a b y (rev α) =
      ∏ α ∈ G.inDarts i, (G.totalField b y i / y α / a α.1) := by
    apply Finset.prod_congr rfl
    intro α hα
    simp only [inDarts, Finset.mem_filter, Finset.mem_univ, true_and] at hα
    unfold auxA
    rw [rev_fst, G.cavity_rev_eq b y hy α, hα]
  rw [hprodA]
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_inv_distrib]
  unfold auxBeta degree
  rw [← G.prod_inDarts_edge hG i a]
  have hprody : ∏ α ∈ G.inDarts i, y α = G.totalField b y i / b i := by
    unfold totalField; rw [mul_div_cancel_left₀ _ (hb i)]
  rw [hprody]
  have hpa : ∏ α ∈ G.inDarts i, a α.1 ≠ 0 := Finset.prod_ne_zero_iff.2 fun α _ => ha α.1
  have hbi := hb i
  rw [zpow_sub₀ hF, zpow_one, zpow_natCast]
  first
    | (field_simp; done)
    | (field_simp; ring)

/-- At an admissible solution, A_{e,i}≠0. -/
theorem auxA_ne_zero (ha : ∀ e, a e ≠ 0) (hb : ∀ i, b i ≠ 0) (hy : ∀ α, y α ≠ 0) (α : Dart E) :
    G.auxA a b y α ≠ 0 := by
  unfold auxA cavity
  exact div_ne_zero (mul_ne_zero (hb _) (Finset.prod_ne_zero_iff.2 fun γ _ => hy γ)) (ha _)

/-- At an admissible solution, A_{e,i}≠-1 because the update denominator is nonzero. -/
theorem auxA_ne_neg_one (ha : ∀ e, a e ≠ 0) (hden : ∀ α, G.cavity b y α + a α.1 ≠ 0)
    (α : Dart E) : G.auxA a b y α ≠ -1 := by
  unfold auxA
  intro h
  apply hden α
  have := ha α.1
  field_simp at h
  linear_combination h

end Auxiliary

end Multigraph

namespace BP

section EdgeQuadratic

/-!
## One-edge quadratic

Set A=A_{e,i}, B=A_{e,j}, F=F_i, J=F_j and s=s_e. Eliminate B from the two equations (4).
-/

variable {K : Type*} [Field K]

/-- J(1+A)=B(1+sA), J≠0 and A≠-1 imply 1+sA≠0. -/
theorem one_add_s_mul_ne_zero {A B J s : K} (h2 : J * (1 + A) = B * (1 + s * A)) (hJ : J ≠ 0)
    (hA : 1 + A ≠ 0) : 1 + s * A ≠ 0 := by
  intro h
  rw [h, mul_zero] at h2
  exact mul_ne_zero hJ hA h2

/-- Quadratic after eliminating B (`eq:edge-quadratic`): s(1+J)A²+[1+sJ−F(s+J)]A−F(1+J)=0. -/
theorem edge_quadratic {A B F J s : K} (h1 : F * (1 + B) = A * (1 + s * B))
    (h2 : J * (1 + A) = B * (1 + s * A)) :
    s * (1 + J) * A ^ 2 + (1 + s * J - F * (s + J)) * A - F * (1 + J) = 0 := by
  linear_combination (-(1 + s * A)) * h1 + (A * s - F) * h2

/-- After division by 1+J≠0: sA²+[1−F+(s−1)(1−(1+F)/(1+J))]A−F=0. -/
theorem edge_quadratic' {A B F J s : K} (h1 : F * (1 + B) = A * (1 + s * B))
    (h2 : J * (1 + A) = B * (1 + s * A)) (hJ : 1 + J ≠ 0) :
    s * A ^ 2 + (1 - F + (s - 1) * (1 - (1 + F) / (1 + J))) * A - F = 0 := by
  have h := edge_quadratic h1 h2
  field_simp
  linear_combination h

end EdgeQuadratic

end BP

end BPFixedPoints
