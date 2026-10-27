import BPFixedPoints.Incidence.KoszulContraction
import BPFixedPoints.Incidence.ResolutionHomogeneous

/-!
# Exterior degrees of the Koszul contraction

Local homotopy raises exterior degree by one and projection preserves degree.
Normalization to a strong contraction retains these degrees, making Čech
perturbation terminate after finitely many steps.
-/

namespace BPFixedPoints.Koszul

open ResolutionTools

variable {E σ R : Type*} [LinearOrder E] [DecidableEq σ] [CommRing R]

def exteriorDegree (S : Finset E) : ℤ := S.card

theorem homotopyOne_degree (ι : E → σ) (e : E) :
    HasDegree exteriorDegree exteriorDegree 1 (homotopyOne (R := R) ι e) := by
  apply HasDegree.of_single
  intro S p
  rw [homotopyOne_single]
  split_ifs with he
  · exact Submodule.zero_mem _
  · apply Finsupp.single_mem_supported
    change ((Insert.insert e S).card : ℤ) = (S.card : ℤ) + 1
    rw [Finset.card_insert_of_notMem he, Nat.cast_add, Nat.cast_one]

theorem projectOne_degree (ι : E → σ) (e : E) :
    HasDegree exteriorDegree exteriorDegree 0 (projectOne (R := R) ι e) := by
  apply HasDegree.of_single
  intro S p
  rw [projectOne_single]
  split_ifs
  · exact Submodule.zero_mem _
  · exact Finsupp.single_mem_supported R _ (by simp)

theorem projectList_degree (ι : E → σ) (L : List E) :
    HasDegree exteriorDegree exteriorDegree 0 (projectList (R := R) ι L) := by
  apply HasDegree.of_single
  intro S p
  rw [projectList_single]
  split_ifs
  · exact Finsupp.single_mem_supported R _ (by simp)
  · exact Submodule.zero_mem _

theorem homotopyList_degree (ι : E → σ) (L : List E) :
    HasDegree exteriorDegree exteriorDegree 1 (homotopyList (R := R) ι L) := by
  induction L with
  | nil => exact HasDegree.zero _ _ _
  | cons e L ih =>
    change HasDegree exteriorDegree exteriorDegree 1
      (homotopyOne ι e + projectOne ι e * homotopyList ι L)
    apply (homotopyOne_degree ι e).add
    simpa only [add_zero, Module.End.mul_eq_comp] using (projectOne_degree ι e).comp ih

theorem variableTerm_degree (ι : E → σ) (e : E) :
    HasDegree exteriorDegree exteriorDegree (-1) (variableTerm (R := R) ι e) := by
  apply HasDegree.of_single
  intro S p
  rw [variableTerm_single]
  split_ifs with he
  · apply Finsupp.single_mem_supported
    change ((S.erase e).card : ℤ) = (S.card : ℤ) + (-1)
    have hcard := Finset.card_erase_add_one he
    omega
  · exact Submodule.zero_mem _

section Fintype

variable [Fintype E]

theorem variableDifferential_degree (ι : E → σ) :
    HasDegree exteriorDegree exteriorDegree (-1) (variableDifferential (R := R) ι) := by
  rw [variableDifferential_eq_sum]
  exact HasDegree.sum _ _ (fun e _ => variableTerm_degree ι e)

/-- The normalized strong-contraction homotopy also raises exterior degree by one. -/
theorem variableContraction_h_degree (ι : E → σ) (hι : Function.Injective ι) :
    HasDegree exteriorDegree exteriorDegree 1 (variableContraction (R := R) ι hι).h := by
  rw [variableContraction, IncidencePerturbation.Contraction.ofHomotopy_h,
    variableSection_augmentation]
  have hq : HasDegree exteriorDegree exteriorDegree 0
      (1 - projectList (R := R) ι Finset.univ.toList) := by
    simpa only [Module.End.one_eq_id] using
      (HasDegree.id exteriorDegree).sub (projectList_degree (R := R) ι Finset.univ.toList)
  have h₀ : HasDegree exteriorDegree exteriorDegree 1
      ((1 - projectList (R := R) ι Finset.univ.toList) *
        homotopyList ι Finset.univ.toList *
          (1 - projectList ι Finset.univ.toList)) := by
    simpa only [zero_add, add_zero, Module.End.mul_eq_comp] using
      (hq.comp (homotopyList_degree ι Finset.univ.toList)).comp hq
  simpa only [Int.reduceAdd, Module.End.mul_eq_comp] using
    (h₀.comp (variableDifferential_degree ι)).comp h₀

/-- Projection to the degree-zero quotient vanishes on positive exterior degrees. -/
theorem variableContraction_p_eq_zero (ι : E → σ) (hι : Function.Injective ι)
    {n : ℤ} {x : Space E (MvPolynomial σ R)}
    (hx : x ∈ Finsupp.supported (MvPolynomial σ R) R {S | exteriorDegree S = n})
    (hn : n ≠ 0) : (variableContraction (R := R) ι hι).p x = 0 := by
  change Ideal.Quotient.mkₐ R (variableIdeal ι) (x ∅) = 0
  have hx0 : x ∅ = 0 := (Finsupp.mem_supported' R x).mp hx ∅ (by
    change exteriorDegree ∅ ≠ n
    simpa only [exteriorDegree, Finset.card_empty, Nat.cast_zero] using hn.symm)
  rw [hx0, map_zero]

theorem variableContraction_i_mem_degree_zero (ι : E → σ) (hι : Function.Injective ι)
    (x : VariableQuotient (R := R) ι) :
    (variableContraction (R := R) ι hι).i x ∈
      Finsupp.supported (MvPolynomial σ R) R {S | exteriorDegree S = 0} := by
  change Finsupp.single ∅ (variableQuotientSection ι x) ∈ _
  exact Finsupp.single_mem_supported R _ rfl

end Fintype

end BPFixedPoints.Koszul
