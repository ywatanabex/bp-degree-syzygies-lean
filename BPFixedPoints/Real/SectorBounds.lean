import BPFixedPoints.Real.StrongFieldCount
import BPFixedPoints.Incidence.CycleSpace
import BPFixedPoints.Real.SectorBox

/-!
# Sector box bounds and strong-field real counts by sector

`abs_sub_le_of_sectorField_eq` gives |(1−k_i)u_i−h_i|≤J̄_i for 𝔥_S(u)=h,
with J̄_i=Σ_{e∋i}|J_e| and J_e=½log a_e (`real:global-box`), using
`abs_zPlus_le`. For Eulerian S, |1−k_i|≥1, hence |u_i|≤|h_i|+J̄_i
(`abs_le_of_sectorField_eq`), the properness estimate in `real:sector-degree`.
At strong fields each Eulerian negative-edge sector has one real solution
and non-Eulerian sectors have none (`card_sector_strong_field`). Use the
total count `card_real_strong_field`, sector existence `exists_real_solution`
and `real_sign_sectors`. This gives the sectorwise part of the real-root row
in `fig:k4-states` and `real:all-real-states`.
-/

namespace BPFixedPoints

set_option linter.unusedSectionVars false

namespace Multigraph

open BP

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] {G : Multigraph V E}


section Strong

variable {a : E → ℝ} (ha : ∀ e, 0 < a e) (ha1 : ∀ e, a e ≠ 1)
include ha ha1

/-- **Strong-field count by sector.** If every |log b_i| is sufficiently large, there is exactly one admissible real solution with negative-edge set S if S is Eulerian, and none otherwise. -/
theorem card_sector_strong_field (hG : G.Loopless) :
    ∃ H : ℝ, ∀ b : V → ℝ, (∀ i, 0 < b i) → (∀ i, H ≤ |Real.log (b i)|) →
      ∀ S : Finset E,
        Nat.card {y : Dart E → ℝ // G.IsAdmissibleSolution a b y ∧ negSupport y = S} =
          if G.IsEvenSet S then 1 else 0 := by
  classical
  obtain ⟨H, hH⟩ := card_real_strong_field ha ha1 hG
  refine ⟨H, fun b hb hbH S => ?_⟩
  obtain ⟨hR, -⟩ := hH b hb hbH
  let f : {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} → {S : Finset E // G.IsEvenSet S} :=
    fun y => ⟨negSupport y.1, (real_sign_sectors hG ha hb y.2).2.2⟩
  have hsurj : Function.Surjective f := fun ⟨S, hS⟩ => by
    obtain ⟨y, hy, hyS⟩ := exists_real_solution ha ha1 hG hS hb
    exact ⟨⟨y, hy⟩, Subtype.ext hyS⟩
  have hcardS : Nat.card {S : Finset E // G.IsEvenSet S} =
      (Finset.univ.filter G.IsEvenSet).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hpos : 0 < (Finset.univ.filter G.IsEvenSet).card :=
    Finset.card_pos.2 ⟨∅, by simp [IsEvenSet]⟩
  have hfin : Finite {y : Dart E → ℝ // G.IsAdmissibleSolution a b y} :=
    Nat.finite_of_card_ne_zero (by omega)
  have hinj : Function.Injective f :=
    (hsurj.bijective_of_nat_card_le (by rw [hR, hcardS])).1
  split_ifs with hS
  · rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun y₁ y₂ => ?_⟩, ?_⟩
    · have : f ⟨y₁.1, y₁.2.1⟩ = f ⟨y₂.1, y₂.2.1⟩ := Subtype.ext (y₁.2.2.trans y₂.2.2.symm)
      have h2 := congrArg Subtype.val (hinj this)
      exact Subtype.ext h2
    · obtain ⟨y, hy, hyS⟩ := exists_real_solution ha ha1 hG hS hb
      exact ⟨⟨y, hy, hyS⟩⟩
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun y => hS (y.2.2 ▸ (real_sign_sectors hG ha hb y.2.1).2.2)⟩

end Strong

end Multigraph

end BPFixedPoints

