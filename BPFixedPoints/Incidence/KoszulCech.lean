import BPFixedPoints.Incidence.KoszulCechTools
import BPFixedPoints.Incidence.CechProductMaps
import BPFixedPoints.Incidence.ResolutionStates
import BPFixedPoints.Incidence.FiniteFiltration

/-!
# Actual graph Koszul–Čech complex and a finite free model

Implement bilinear edge sections as commuting operators on Laurent monomials.
Perturb the Čech contraction by the Koszul differential. A geometric series,
finite by the state count, constructs a differential on the finite free module.
-/

namespace BPFixedPoints.Multigraph

open IncidencePerturbation Finsupp

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Free module common to the Čech terms of every state. -/
abbrev IncCechModule := CechProduct.C (IncCoeffRing E) V

/-- Total module combining exterior states and Čech monomials. -/
abbrev IncTotalModule := Koszul.Space E (IncCechModule (V := V) (E := E))

/-- Multiplication by the bilinear edge section; for self-loops add both endpoint exponents. -/
noncomputable def incEdgeAction (e : E) :
    Module.End (IncCoeffRing E) (IncCechModule (V := V) (E := E)) :=
  ∑ α : Fin 2, ∑ β : Fin 2,
    (MvPolynomial.X (e, α, β) : IncCoeffRing E) • CechProduct.multiply (IncCoeffRing E)
      (G.incSectionLeft e α β) (G.incSectionRight e α β)

theorem incEdgeAction_commute (e j : E) : Commute (G.incEdgeAction e) (G.incEdgeAction j) := by
  unfold incEdgeAction
  apply Commute.sum_left
  intro α _
  apply Commute.sum_left
  intro β _
  apply Commute.sum_right
  intro α' _
  apply Commute.sum_right
  intro β' _
  apply Commute.smul_left
  apply Commute.smul_right
  exact CechProduct.multiply_commute (IncCoeffRing E) _ _ _ _

theorem incEdgeAction_cech {S : Finset E} {e : E} (he : e ∈ S) :
    (CechProduct.contraction (IncCoeffRing E) (G.deg (S.erase e))).d * G.incEdgeAction e =
      G.incEdgeAction e * (CechProduct.contraction (IncCoeffRing E) (G.deg S)).d := by
  unfold incEdgeAction
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  have hh := CechProduct.multiply_chainMap (IncCoeffRing E) (G.deg S)
    (G.incSectionLeft e α β) (G.incSectionRight e α β)
    (G.incSection_sum_le_degree he α β)
  rw [G.degree_sub_incSection he α β] at hh
  exact hh.symm

theorem incEdgeAction_sign (S T : Finset E) (e : E) :
    (CechProduct.contraction (IncCoeffRing E) (G.deg T)).sign * G.incEdgeAction e =
      G.incEdgeAction e * (CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign := by
  unfold incEdgeAction
  simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  exact (CechProduct.multiply_sign (IncCoeffRing E) (G.deg S) (G.deg T)
    (G.incSectionLeft e α β) (G.incSectionRight e α β)).symm

/-- Direct sum of statewise Čech contractions. -/
noncomputable def incCechContraction :
    Contraction (IncCoeffRing E) (IncTotalModule (V := V) (E := E))
      (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  Contraction.finsupp fun S =>
    (CechProduct.contraction (IncCoeffRing E) (G.deg S)).toContraction

theorem incCechContraction_d :
    G.incCechContraction.d =
      Koszul.diagonal (fun S => (CechProduct.contraction (IncCoeffRing E) (G.deg S)).d) := by
  apply Finsupp.lhom_ext
  intro S x
  ext T
  by_cases hST : S = T
  · subst T
    simp [incCechContraction]
  · simp [incCechContraction, hST]

@[simp] theorem incCechContraction_h_single (S : Finset E)
    (x : IncCechModule (V := V) (E := E)) :
    G.incCechContraction.h (single S x) =
      single S ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).h x) := by
  ext T
  by_cases hST : S = T
  · subst T
    simp [incCechContraction]
  · simp [incCechContraction, hST]

/-- Koszul differential multiplied by Čech-degree parity. -/
noncomputable def incKoszulPerturbation :
    Module.End (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) :=
  Koszul.signedDifferential
    (fun S => (CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign) G.incEdgeAction

/-- The actual total differential. -/
noncomputable def incTotalDifferential :
    Module.End (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) :=
  G.incCechContraction.d + G.incKoszulPerturbation

theorem incTotalDifferential_sq : G.incTotalDifferential * G.incTotalDifferential = 0 := by
  rw [incTotalDifferential, G.incCechContraction_d]
  apply Koszul.total_differential_sq
  · intro S
    exact (CechProduct.contraction (IncCoeffRing E) (G.deg S)).d_sq
  · exact G.incEdgeAction_commute
  · intro S e he
    exact G.incEdgeAction_cech he
  · intro S e he
    exact G.incEdgeAction_sign S (S.erase e) e
  · intro S
    have hh := (CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign_d
    apply LinearMap.ext
    intro x
    have he := LinearMap.congr_fun hh x
    change (CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign
        ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).d x) =
      -((CechProduct.contraction (IncCoeffRing E) (G.deg S)).d
        ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign x)) at he
    change (CechProduct.contraction (IncCoeffRing E) (G.deg S)).d
        ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign x) =
      -((CechProduct.contraction (IncCoeffRing E) (G.deg S)).sign
        ((CechProduct.contraction (IncCoeffRing E) (G.deg S)).d x))
    rw [he, neg_neg]

theorem incKoszulPerturbation_single (S : Finset E)
    (x : IncCechModule (V := V) (E := E)) :
    G.incKoszulPerturbation (single S x) =
      ∑ e ∈ S, single (S.erase e)
        ((CechProduct.contraction (IncCoeffRing E) (G.deg (S.erase e))).sign
          (Koszul.sign (A := IncCoeffRing E) S e • G.incEdgeAction e x)) := by
  simp only [incKoszulPerturbation, Koszul.signedDifferential, Module.End.mul_apply,
    Koszul.differentialLinear_single, map_sum, Koszul.diagonal_single]

/-- The composite of perturbation and Čech homotopy always lowers edge count by one. -/
theorem incKoszulPerturbation_h_nilpotent :
    (G.incKoszulPerturbation * G.incCechContraction.h) ^ (Fintype.card E + 1) = 0 := by
  apply pow_eq_zero_of_lowers_support _ Finset.card
  · intro S
    exact Nat.lt_succ_of_le (Finset.card_le_univ S)
  · intro S x
    rw [Module.End.mul_apply, G.incCechContraction_h_single,
      G.incKoszulPerturbation_single]
    apply Submodule.sum_mem
    intro e he
    exact single_mem_supported _ _ (Finset.card_erase_lt_of_mem he)

theorem incKoszulPerturbation_unit_left :
    IsUnit (1 + G.incKoszulPerturbation * G.incCechContraction.h) := by
  letI : Ring (Module.End (IncCoeffRing E) (IncTotalModule (V := V) (E := E))) :=
    Module.End.instRing (R := IncCoeffRing E) (N₁ := IncTotalModule (V := V) (E := E))
  exact (show IsNilpotent (G.incKoszulPerturbation * G.incCechContraction.h) from
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩).isUnit_one_add

theorem incKoszulPerturbation_unit_right :
    IsUnit (1 + G.incCechContraction.h * G.incKoszulPerturbation) := by
  exact end_isUnit_one_add_mul_swap _ _ _ G.incKoszulPerturbation_h_nilpotent

/-- Differential of the finite free model acting on the state-sum basis. -/
noncomputable def incResolutionDifferential :
    Module.End (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  G.incCechContraction.transfer G.incKoszulPerturbation

theorem incResolutionDifferential_sq :
    G.incResolutionDifferential * G.incResolutionDifferential = 0 :=
  G.incCechContraction.transfer_sq G.incKoszulPerturbation G.incTotalDifferential_sq
    G.incKoszulPerturbation_unit_left G.incKoszulPerturbation_unit_right

end BPFixedPoints.Multigraph
