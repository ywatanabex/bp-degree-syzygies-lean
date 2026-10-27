import BPFixedPoints.StateSum.Basic
import Mathlib

/-!
# Roots of the weak-coupling vertex equation

The local part of N=Q is β=(−1)^k F^{1−k}, F≠0, at active degree k.
For algebraically closed characteristic-zero K and β≠0,−1 there are φ(k) roots:
one root F=β if k=0; none if k=1 (which forces β=−1); and k−1 distinct roots
of F^{k−1}=(−1)^k/β if k≥2, by splitting and separability of X^{k−1}−c.
Every root avoids 0 and −1, since F=−1 would force β=−1.
-/

namespace BPFixedPoints.BP

open Polynomial

section Field

variable {K : Type*} [Field K]

/-- Weak-coupling vertex equation: F≠0 and β=(-1)^k F^{1-k}, using integer powers in the field. -/
def VertexLimitEq (k : ℕ) (β F : K) : Prop :=
  F ≠ 0 ∧ β = (-1) ^ k * F ^ ((1 : ℤ) - k)

/-- If β≠-1, a root cannot equal -1, since that would force β=-1. -/
theorem vertexLimitEq_ne_neg_one {k : ℕ} {β F : K} (hβ : β ≠ -1) (h : VertexLimitEq k β F) :
    F ≠ -1 := by
  rintro rfl
  obtain ⟨-, hβ'⟩ := h
  apply hβ
  rw [hβ', ← zpow_natCast, ← zpow_add₀ (neg_ne_zero.mpr one_ne_zero),
    show (k : ℤ) + (1 - k) = 1 by ring, zpow_one]

/-- For k=0 the equation is F=β, with F≠0. -/
theorem vertexLimitEq_zero_iff (β F : K) : VertexLimitEq 0 β F ↔ F = β ∧ F ≠ 0 := by
  simp only [VertexLimitEq, pow_zero, Nat.cast_zero, sub_zero, zpow_one, one_mul]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h2.symm, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1.symm⟩⟩

/-- For k=1 and β≠-1 there are no roots. -/
theorem vertexLimitEq_one (β F : K) (hβ : β ≠ -1) : ¬ VertexLimitEq 1 β F := by
  rintro ⟨-, h⟩
  apply hβ
  rw [h]
  simp

/-- For k=m+2 and β≠0, the equation is equivalent to F^{m+1}=(-1)^{m+2}/β; the nonzero right side also excludes F=0. -/
theorem vertexLimitEq_succ_succ_iff (m : ℕ) (β F : K) (hβ0 : β ≠ 0) :
    VertexLimitEq (m + 2) β F ↔ F ^ (m + 1) = (-1) ^ (m + 2) / β := by
  have h1 : ((1 : ℤ) - ((m + 2 : ℕ) : ℤ)) = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [eq_div_iff hβ0]
  constructor
  · rintro ⟨hF, hβ⟩
    rw [hβ, h1, zpow_neg, zpow_natCast, mul_comm, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hF), mul_one]
  · intro h
    have hF : F ≠ 0 := by
      rintro rfl
      rw [zero_pow (Nat.succ_ne_zero m), zero_mul] at h
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) h.symm
    refine ⟨hF, ?_⟩
    rw [h1, zpow_neg, zpow_natCast, ← h, mul_comm (F ^ (m + 1)) β, mul_assoc,
      mul_inv_cancel₀ (pow_ne_zero _ hF), mul_one]

end Field

section AlgClosed

variable (K : Type*) [Field K] [IsAlgClosed K] [CharZero K]

/-- For n>0,c≠0 over an algebraically closed characteristic-zero field, X^n-c has exactly n distinct roots by separability. -/
theorem card_roots_X_pow_sub_C [DecidableEq K] (n : ℕ) (hn : 0 < n) (c : K) (hc : c ≠ 0) :
    ((X ^ n - C c : K[X]).roots.toFinset.card = n) := by
  rw [Multiset.toFinset_card_of_nodup
      (nodup_roots (separable_X_pow_sub_C c (Nat.cast_ne_zero.mpr hn.ne') hc)),
    IsAlgClosed.card_roots_eq_natDegree, natDegree_X_pow_sub_C]

/-- Main theorem: for β≠0,−1, the vertex equation has φ(k) solutions. -/
theorem card_vertexLimitEq (k : ℕ) (β : K) (hβ0 : β ≠ 0) (hβ1 : β ≠ -1) :
    Nat.card {F : K // VertexLimitEq k β F} = phi k := by
  match k with
  | 0 =>
    have : Nonempty {F : K // VertexLimitEq 0 β F} :=
      ⟨⟨β, (vertexLimitEq_zero_iff β β).2 ⟨rfl, hβ0⟩⟩⟩
    have : Subsingleton {F : K // VertexLimitEq 0 β F} :=
      ⟨fun ⟨F, hF⟩ ⟨G, hG⟩ => Subtype.ext
        (((vertexLimitEq_zero_iff β F).1 hF).1.trans ((vertexLimitEq_zero_iff β G).1 hG).1.symm)⟩
    rw [phi_zero]
    exact Nat.card_unique
  | 1 =>
    have : IsEmpty {F : K // VertexLimitEq 1 β F} :=
      ⟨fun ⟨F, hF⟩ => vertexLimitEq_one β F hβ1 hF⟩
    rw [phi_one]
    exact Nat.card_of_isEmpty
  | m + 2 =>
    obtain ⟨c, hc⟩ : ∃ c : K, c = (-1) ^ (m + 2) / β := ⟨_, rfl⟩
    have hc0 : c ≠ 0 := by
      rw [hc]; exact div_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hβ0
    have hn : ((m + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)
    obtain ⟨p, hp⟩ : ∃ p : K[X], p = X ^ (m + 1) - C c := ⟨_, rfl⟩
    have hsep : p.Separable := by rw [hp]; exact separable_X_pow_sub_C c hn hc0
    have hsplit : (p.map (algebraMap K K)).Splits := IsAlgClosed.splits_domain p
    have hcard : Fintype.card (p.rootSet K) = p.natDegree := card_rootSet_eq_natDegree hsep hsplit
    have hdeg : p.natDegree = m + 1 := by rw [hp]; exact natDegree_X_pow_sub_C
    have hp0 : p ≠ 0 := by rw [hp]; exact X_pow_sub_C_ne_zero (Nat.succ_pos m) c
    have hmem : ∀ F : K, VertexLimitEq (m + 2) β F ↔ F ∈ p.rootSet K := by
      intro F
      rw [mem_rootSet_of_ne hp0, vertexLimitEq_succ_succ_iff m β F hβ0, hp, hc]
      simp [sub_eq_zero]
    have e : {F : K // VertexLimitEq (m + 2) β F} ≃ p.rootSet K :=
      Equiv.subtypeEquivRight hmem
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, hcard, hdeg]
    rfl

/-- The root set is finite: positive φ(k) for k≠1, and empty for k=1. -/
theorem finite_vertexLimitEq (k : ℕ) (β : K) (hβ0 : β ≠ 0) (hβ1 : β ≠ -1) :
    Finite {F : K // VertexLimitEq k β F} := by
  rcases eq_or_ne k 1 with rfl | hk
  · have : IsEmpty {F : K // VertexLimitEq 1 β F} :=
      ⟨fun ⟨F, hF⟩ => vertexLimitEq_one β F hβ1 hF⟩
    infer_instance
  · exact Nat.finite_of_card_ne_zero (by
      rw [card_vertexLimitEq K k β hβ0 hβ1]
      exact (phi_pos_of_ne_one hk).ne')

end AlgClosed

end BPFixedPoints.BP
