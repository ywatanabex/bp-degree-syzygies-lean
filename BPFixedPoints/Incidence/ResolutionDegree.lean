import BPFixedPoints.Incidence.KoszulCech
import BPFixedPoints.Incidence.CechProductDegree
import BPFixedPoints.Incidence.ResolutionSubmoduleDegree
import BPFixedPoints.Incidence.ResolutionGrading

/-!
# Degrees of the actual Koszul–Čech transferred differential

Use total degree |S|−Čech degree in the finitely supported edge-state presentation.
Prove that the finite-perturbation differential lowers homological degree of
the state-cohomology basis by exactly one.
-/

namespace BPFixedPoints.Multigraph

open Finsupp IncidencePerturbation ResolutionTools

set_option linter.unusedSectionVars false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Submodule of total degree n. -/
noncomputable def incTotalPiece (n : ℤ) :
    Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) where
  carrier := {x | ∀ S, x S ∈ supported (IncCoeffRing E) (IncCoeffRing E)
    {b | (CechProduct.cechDegree b : ℤ) = (S.card : ℤ) - n}}
  zero_mem' := fun _S => Submodule.zero_mem _
  add_mem' hx hy := fun S => Submodule.add_mem _ (hx S) (hy S)
  smul_mem' r _x hx := fun S => Submodule.smul_mem _ r (hx S)

/-- Submodule of Čech degree n, also used for nilpotence after local Koszul contraction. -/
noncomputable def incCechPiece (n : ℤ) :
    Submodule (IncCoeffRing E) (IncTotalModule (V := V) (E := E)) where
  carrier := {x | ∀ S, x S ∈ supported (IncCoeffRing E) (IncCoeffRing E)
    {b | (CechProduct.cechDegree b : ℤ) = n}}
  zero_mem' := fun _S => Submodule.zero_mem _
  add_mem' hx hy := fun S => Submodule.add_mem _ (hx S) (hy S)
  smul_mem' r _x hx := fun S => Submodule.smul_mem _ r (hx S)

noncomputable def incResolutionPiece (n : ℤ) :
    Submodule (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  supported (IncCoeffRing E) (IncCoeffRing E)
    {b | (G.incResolutionDegree b : ℤ) = n}

theorem incTotalPiece_single {n : ℤ} (S : Finset E)
    (x : IncCechModule (V := V) (E := E))
    (hx : x ∈ supported (IncCoeffRing E) (IncCoeffRing E)
      {b | (CechProduct.cechDegree b : ℤ) = (S.card : ℤ) - n}) :
    single S x ∈ incTotalPiece (V := V) (E := E) n := by
  change ∀ T, (single S x) T ∈ supported (IncCoeffRing E) (IncCoeffRing E)
    {b | (CechProduct.cechDegree b : ℤ) = (T.card : ℤ) - n}
  intro T
  by_cases hST : S = T
  · subst T
    simpa only [single_eq_same] using hx
  · rw [single_eq_of_ne (Ne.symm hST)]
    exact Submodule.zero_mem _

theorem incResolutionDegree_cast (b : G.IncResolutionBasis) :
    (G.incResolutionDegree b : ℤ) = (b.1.card : ℤ) -
      (CechProduct.cohomologyDegree (G.deg b.1) : ℤ) := by
  rw [incResolutionDegree, Nat.cast_sub (G.incResolutionBasis_card_support_le b)]
  rw [CechProduct.cohomologyDegree_eq_card]
  rfl

@[simp] theorem incCechContraction_d_apply (x : IncTotalModule (V := V) (E := E))
    (S : Finset E) :
    G.incCechContraction.d x S =
      (CechProduct.contraction (IncCoeffRing E) (G.deg S)).d (x S) := rfl

@[simp] theorem incCechContraction_h_apply (x : IncTotalModule (V := V) (E := E))
    (S : Finset E) :
    G.incCechContraction.h x S =
      (CechProduct.contraction (IncCoeffRing E) (G.deg S)).h (x S) := rfl

@[simp] theorem incCechContraction_i_apply
    (x : G.IncResolutionBasis →₀ IncCoeffRing E) (S : Finset E) :
    G.incCechContraction.i x S =
      (CechProduct.contraction (IncCoeffRing E) (G.deg S)).i
        ((Finsupp.sigmaFinsuppLEquivPiFinsupp (IncCoeffRing E)) x S) := rfl

@[simp] theorem incCechContraction_p_apply (x : IncTotalModule (V := V) (E := E))
    (S : Finset E) (k : CechProduct.HBasis (G.deg S)) :
    G.incCechContraction.p x ⟨S, k⟩ =
      (CechProduct.contraction (IncCoeffRing E) (G.deg S)).p (x S) k := rfl

theorem incCechContraction_d_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incTotalPiece (V := V) (E := E)) (incTotalPiece (V := V) (E := E)) (-1) G.incCechContraction.d := by
  intro n x hx S
  rw [G.incCechContraction_d_apply]
  have h := CechProduct.contraction_d_degree (IncCoeffRing E) (G.deg S)
    ((S.card : ℤ) - n) (x S) (hx S)
  have hn : (S.card : ℤ) - n + 1 = (S.card : ℤ) - (n + -1) := by ring
  simpa only [hn] using h

theorem incCechContraction_h_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incTotalPiece (V := V) (E := E)) (incTotalPiece (V := V) (E := E)) 1 G.incCechContraction.h := by
  intro n x hx S
  rw [G.incCechContraction_h_apply]
  have h := CechProduct.contraction_h_degree (IncCoeffRing E) (G.deg S)
    ((S.card : ℤ) - n) (x S) (hx S)
  have hn : (S.card : ℤ) - n + -1 = (S.card : ℤ) - (n + 1) := by ring
  simpa only [hn] using h

theorem incCechContraction_i_shifts :
    Shifts (R := IncCoeffRing E) (M := G.IncResolutionBasis →₀ IncCoeffRing E)
      (N := IncTotalModule (V := V) (E := E))
      G.incResolutionPiece (incTotalPiece (V := V) (E := E)) 0
      G.incCechContraction.i := by
  intro n x hx S
  rw [G.incCechContraction_i_apply]
  let y := (Finsupp.sigmaFinsuppLEquivPiFinsupp (IncCoeffRing E)) x S
  by_cases hn : (CechProduct.cohomologyDegree (G.deg S) : ℤ) = (S.card : ℤ) - n
  · have hy : y ∈ supported (IncCoeffRing E) (IncCoeffRing E)
        {b : CechProduct.HBasis (G.deg S) |
          (CechProduct.cohomologyDegree (G.deg S) : ℤ) =
            (CechProduct.cohomologyDegree (G.deg S) : ℤ)} := by
      apply (mem_supported' _ _).mpr
      intro b hb
      exact (hb rfl).elim
    have h := CechProduct.contraction_i_degree (IncCoeffRing E) (G.deg S)
      (CechProduct.cohomologyDegree (G.deg S) : ℤ) y hy
    simpa only [add_zero, hn] using h
  · have hy : y = 0 := by
      apply Finsupp.ext
      intro k
      change x ⟨S, k⟩ = 0
      apply (mem_supported' (IncCoeffRing E) x).mp hx ⟨S, k⟩
      change (G.incResolutionDegree ⟨S, k⟩ : ℤ) ≠ n
      rw [G.incResolutionDegree_cast]
      change (S.card : ℤ) - (CechProduct.cohomologyDegree (G.deg S) : ℤ) ≠ n
      omega
    change (CechProduct.contraction (IncCoeffRing E) (G.deg S)).i y ∈ _
    rw [hy, map_zero]
    exact Submodule.zero_mem _

theorem incCechContraction_p_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := G.IncResolutionBasis →₀ IncCoeffRing E)
      (incTotalPiece (V := V) (E := E)) G.incResolutionPiece 0
      G.incCechContraction.p := by
  intro n x hx
  apply (mem_supported' (IncCoeffRing E) _).mpr
  rintro ⟨S, k⟩ hk
  rw [G.incCechContraction_p_apply]
  have hne : (CechProduct.cohomologyDegree (G.deg S) : ℤ) ≠ (S.card : ℤ) - n + 0 := by
    intro he
    apply hk
    change (G.incResolutionDegree ⟨S, k⟩ : ℤ) = n + 0
    rw [G.incResolutionDegree_cast]
    change (S.card : ℤ) - (CechProduct.cohomologyDegree (G.deg S) : ℤ) = n + 0
    omega
  have hz := (CechProduct.contraction_p_degree (IncCoeffRing E) (G.deg S)).eq_zero_of_const
    (hx S) hne
  exact congrArg (fun z => z k) hz

theorem incEdgeAction_degree (e : E) :
    HasDegree (fun b => (CechProduct.cechDegree b : ℤ))
      (fun b => (CechProduct.cechDegree b : ℤ)) 0 (G.incEdgeAction e) := by
  have hm (a b : V → ℕ) :
      HasDegree (fun f => (CechProduct.cechDegree f : ℤ))
        (fun f => (CechProduct.cechDegree f : ℤ)) 0
          (CechProduct.multiply (IncCoeffRing E) a b) := by
    apply HasDegree.of_single
    intro f r
    rw [CechProduct.multiply_single]
    exact single_mem_supported _ _ (by simp)
  intro n x hx
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro α hα
  apply Submodule.sum_mem
  intro β hβ
  exact Submodule.smul_mem _ _ (hm _ _ n x hx)

theorem incKoszulPerturbation_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incTotalPiece (V := V) (E := E)) (incTotalPiece (V := V) (E := E)) (-1) G.incKoszulPerturbation := by
  intro n x hx
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro S hS
  change G.incKoszulPerturbation (single S (x S)) ∈ incTotalPiece (n + -1)
  rw [G.incKoszulPerturbation_single]
  apply Submodule.sum_mem
  intro e he
  apply incTotalPiece_single
  have h₁ := G.incEdgeAction_degree e ((S.card : ℤ) - n) (x S) (hx S)
  have h₂ := (CechProduct.contraction_degrees (IncCoeffRing E) (G.deg (S.erase e))).sign
    ((S.card : ℤ) - n) (Koszul.sign (A := IncCoeffRing E) S e • G.incEdgeAction e (x S))
    (Submodule.smul_mem _ _ (by simpa only [add_zero] using h₁))
  have hc := Finset.card_erase_add_one he
  have hn : ((S.erase e).card : ℤ) - (n + -1) = (S.card : ℤ) - n + 0 := by omega
  simpa only [hn] using h₂


/-- The Čech differential raises Čech degree by one. -/
theorem incCechContraction_d_cechShifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incCechPiece (V := V) (E := E)) (incCechPiece (V := V) (E := E)) 1 G.incCechContraction.d := by
  intro n x hx S
  rw [G.incCechContraction_d_apply]
  exact CechProduct.contraction_d_degree (IncCoeffRing E) (G.deg S) n (x S) (hx S)

/-- Čech homotopy lowers Čech degree by one. -/
theorem incCechContraction_h_cechShifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incCechPiece (V := V) (E := E)) (incCechPiece (V := V) (E := E)) (-1) G.incCechContraction.h := by
  intro n x hx S
  rw [G.incCechContraction_h_apply]
  exact CechProduct.contraction_h_degree (IncCoeffRing E) (G.deg S) n (x S) (hx S)

theorem incCechPiece_single {n : ℤ} (S : Finset E)
    (x : IncCechModule (V := V) (E := E))
    (hx : x ∈ supported (IncCoeffRing E) (IncCoeffRing E)
      {b | (CechProduct.cechDegree b : ℤ) = n}) :
    single S x ∈ incCechPiece (V := V) (E := E) n := by
  change ∀ T, (single S x) T ∈ supported (IncCoeffRing E) (IncCoeffRing E)
    {b | (CechProduct.cechDegree b : ℤ) = n}
  intro T
  by_cases hST : S = T
  · subst T
    simpa only [single_eq_same] using hx
  · rw [single_eq_of_ne (Ne.symm hST)]
    exact Submodule.zero_mem _

/-- The Koszul differential preserves Čech face degree. -/
theorem incKoszulPerturbation_cechShifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incCechPiece (V := V) (E := E)) (incCechPiece (V := V) (E := E)) 0 G.incKoszulPerturbation := by
  intro n x hx
  rw [← x.sum_single, map_finsuppSum]
  apply Submodule.sum_mem
  intro S hS
  change G.incKoszulPerturbation (single S (x S)) ∈ incCechPiece (n + 0)
  rw [G.incKoszulPerturbation_single]
  apply Submodule.sum_mem
  intro e he
  apply incCechPiece_single
  have h₁ := G.incEdgeAction_degree e n (x S) (hx S)
  have h₂ := (CechProduct.contraction_degrees (IncCoeffRing E) (G.deg (S.erase e))).sign
    n (Koszul.sign (A := IncCoeffRing E) S e • G.incEdgeAction e (x S))
    (Submodule.smul_mem _ _ (by simpa only [add_zero] using h₁))
  exact h₂

theorem incCechPiece_eq_bot_of_negative {n : ℤ} (hn : n < 0) :
    incCechPiece (V := V) (E := E) n = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply Finsupp.ext
  intro S
  apply Finsupp.ext
  intro b
  apply (mem_supported' (IncCoeffRing E) (x S)).mp (hx S) b
  change (CechProduct.cechDegree b : ℤ) ≠ n
  omega

theorem incCechPiece_eq_bot_of_gt_card {n : ℤ} (hn : (Fintype.card V : ℤ) < n) :
    incCechPiece (V := V) (E := E) n = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  apply Finsupp.ext
  intro S
  apply Finsupp.ext
  intro b
  apply (mem_supported' (IncCoeffRing E) (x S)).mp (hx S) b
  change (CechProduct.cechDegree b : ℤ) ≠ n
  have hb := CechProduct.cechDegree_le_card b
  omega

theorem incResolutionDifferential_hasDegree :
    HasDegree (fun b => (G.incResolutionDegree b : ℤ))
      (fun b => (G.incResolutionDegree b : ℤ)) (-1) G.incResolutionDifferential := by
  change Shifts G.incResolutionPiece G.incResolutionPiece (-1)
    (G.incCechContraction.transfer G.incKoszulPerturbation)
  exact G.incCechContraction.transfer_shifts G.incKoszulPerturbation
    (incTotalPiece (V := V) (E := E)) G.incResolutionPiece
    G.incKoszulPerturbation_shifts G.incCechContraction_h_shifts
    G.incCechContraction_i_shifts G.incCechContraction_p_shifts
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩

/-- The perturbed chain map from the finite free model to the total complex preserves total degree. -/
theorem incResolutionInclusion_shifts :
    Shifts (R := IncCoeffRing E) (M := G.IncResolutionBasis →₀ IncCoeffRing E)
      (N := IncTotalModule (V := V) (E := E))
      G.incResolutionPiece (incTotalPiece (V := V) (E := E)) 0
      (G.incCechContraction.inclusion G.incKoszulPerturbation) :=
  G.incCechContraction.inclusion_shifts G.incKoszulPerturbation
    (incTotalPiece (V := V) (E := E)) G.incResolutionPiece
    G.incKoszulPerturbation_shifts G.incCechContraction_h_shifts
    G.incCechContraction_i_shifts ⟨_, G.incKoszulPerturbation_h_nilpotent⟩

theorem incResolutionProjection_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := G.IncResolutionBasis →₀ IncCoeffRing E)
      (incTotalPiece (V := V) (E := E)) G.incResolutionPiece 0
      (G.incCechContraction.projection G.incKoszulPerturbation) :=
  G.incCechContraction.projection_shifts G.incKoszulPerturbation
    (incTotalPiece (V := V) (E := E)) G.incResolutionPiece
    G.incKoszulPerturbation_shifts G.incCechContraction_h_shifts
    G.incCechContraction_p_shifts ⟨_, G.incKoszulPerturbation_h_nilpotent⟩

theorem incResolutionHomotopy_shifts :
    Shifts (R := IncCoeffRing E) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (incTotalPiece (V := V) (E := E)) (incTotalPiece (V := V) (E := E)) 1
      (G.incCechContraction.contractingHomotopy G.incKoszulPerturbation) :=
  G.incCechContraction.contractingHomotopy_shifts G.incKoszulPerturbation
    (incTotalPiece (V := V) (E := E))
    G.incKoszulPerturbation_shifts G.incCechContraction_h_shifts
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩

theorem incResolutionDifferential_degree (n : ℕ)
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree (n + 1)) :
    G.incResolutionDifferential x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n := by
  have hx' : x ∈ supported (IncCoeffRing E) (IncCoeffRing E)
      {b | (G.incResolutionDegree b : ℤ) = ((n + 1 : ℕ) : ℤ)} := by
    simpa only [gradedPiece, Int.natCast_inj] using hx
  have h := G.incResolutionDifferential_hasDegree ((n + 1 : ℕ) : ℤ) x hx'
  simpa only [gradedPiece, Nat.cast_add, Nat.cast_one, Int.add_neg_cancel_right, Int.natCast_inj] using h

theorem incResolutionDifferential_zero_degree
    (x : G.IncResolutionBasis →₀ IncCoeffRing E)
    (hx : x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree 0) :
    G.incResolutionDifferential x = 0 := by
  have hx' : x ∈ supported (IncCoeffRing E) (IncCoeffRing E)
      {b | (G.incResolutionDegree b : ℤ) = 0} := by
    simpa only [gradedPiece, Int.natCast_eq_zero] using hx
  have h := G.incResolutionDifferential_hasDegree 0 x hx'
  apply Finsupp.ext
  intro b
  apply (mem_supported' (IncCoeffRing E) _).mp h b
  change (G.incResolutionDegree b : ℤ) ≠ 0 + -1
  omega

end BPFixedPoints.Multigraph
