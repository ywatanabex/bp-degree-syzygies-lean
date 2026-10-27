import BPFixedPoints.Incidence.CechCoefficientMatrices
import BPFixedPoints.Incidence.CoefficientGrading
import BPFixedPoints.Incidence.PerturbationCoefficientGrading
import BPFixedPoints.Incidence.ResolutionBasisCount
import BPFixedPoints.Incidence.ResolutionDegree
import BPFixedPoints.Incidence.ResolutionExactness

/-!
# Internal grading of the actual incidence resolution differential

The weight of a state generator is `|S|`. A Koszul step removes one edge
and multiplies by a coefficient variable of degree one. The actual Čech
contraction has constant entries and preserves the state. Consequently
all terms of the finite transferred differential preserve total internal
degree. These statements concern `incResolutionDifferential` itself.

This file does not identify a derived Tor product or a sheaf-cohomology
algebra. Such an identification is a separate mathematical assertion.
-/

namespace BPFixedPoints.Multigraph

open Finsupp IncidencePerturbation ResolutionTools

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Constants inside the coefficient polynomial ring. -/
noncomputable def incConstantSubring (E : Type) : Subring (IncCoeffRing E) :=
  (algebraMap ℂ (IncCoeffRing E)).range

/-- Homogeneous coefficient subspace on the concrete Čech module. -/
noncomputable def incCechInternalPiece (n : ℤ) :
    Submodule ℂ (IncCechModule (V := V) (E := E)) :=
  coefficientwise (homogeneousCoeffPiece (σ := E × Fin 2 × Fin 2) (k := ℂ) n)

/-- Internal degree `q` on the actual Koszul--Čech total module. -/
noncomputable def incTotalInternalPiece (q : ℤ) :
    Submodule ℂ (IncTotalModule (V := V) (E := E)) where
  carrier := {x | ∀ S, x S ∈ incCechInternalPiece (V := V) (E := E) (q - (S.card : ℤ))}
  zero_mem' := fun S => (incCechInternalPiece (V := V) (E := E) (q - (S.card : ℤ))).zero_mem
  add_mem' hx hy := fun S =>
    (incCechInternalPiece (V := V) (E := E) (q - (S.card : ℤ))).add_mem (hx S) (hy S)
  smul_mem' c _ hx := fun S =>
    (incCechInternalPiece (V := V) (E := E) (q - (S.card : ℤ))).smul_mem c (hx S)

/-- Internal degree `q` on the actual state-indexed free module. -/
noncomputable def incResolutionInternalPiece (q : ℤ) :
    Submodule ℂ (G.IncResolutionBasis →₀ IncCoeffRing E) :=
  weightedFreePiece G.incResolutionInternalDegree q

theorem incTotalInternalPiece_single (q : ℤ) (S : Finset E)
    {x : IncCechModule (V := V) (E := E)}
    (hx : x ∈ incCechInternalPiece (V := V) (E := E) (q - (S.card : ℤ))) :
    single S x ∈ incTotalInternalPiece (V := V) (E := E) q := by
  intro T
  by_cases h : T = S
  · subst T; simpa using hx
  · rw [Finsupp.single_eq_of_ne h]
    exact (incCechInternalPiece (V := V) (E := E) (q - (T.card : ℤ))).zero_mem

/-- A coefficient variable raises coefficient degree by one. -/
theorem incEdgeAction_coefficient_degree (e : E) (n : ℤ)
    {x : IncCechModule (V := V) (E := E)}
    (hx : x ∈ incCechInternalPiece (V := V) (E := E) n) :
    G.incEdgeAction e x ∈ incCechInternalPiece (V := V) (E := E) (n + 1) := by
  simp only [incEdgeAction, LinearMap.sum_apply, LinearMap.smul_apply]
  apply (incCechInternalPiece (V := V) (E := E) (n + 1)).sum_mem
  intro α hα
  apply (incCechInternalPiece (V := V) (E := E) (n + 1)).sum_mem
  intro β hβ
  have hm : MatrixOver (incConstantSubring E)
      (CechProduct.multiply (IncCoeffRing E)
        (G.incSectionLeft e α β) (G.incSectionRight e α β)) :=
    MatrixOver.mapDomain _
  have hy := hm.preserve_coefficients (homogeneousCoeffPiece n) hx
  intro b
  change MvPolynomial.X (e, α, β) *
    CechProduct.multiply (IncCoeffRing E)
      (G.incSectionLeft e α β) (G.incSectionRight e α β) x b ∈
        homogeneousCoeffPiece (n + 1)
  simpa only [add_comm 1 n] using
    homogeneousCoeffPiece_mul (homogeneousCoeffPiece_X (k := ℂ) (e, α, β)) (hy b)

theorem incKoszulSign_constant (S : Finset E) (e : E) :
    Koszul.sign (A := IncCoeffRing E) S e ∈ incConstantSubring E := by
  refine ⟨(-1 : ℂ) ^ Koszul.index S e, ?_⟩
  simp [Koszul.sign]

/-- Removing an edge and adding a coefficient variable preserves total
internal degree. The Čech and exterior signs have constant coefficients. -/
theorem incKoszulPerturbation_internal_degree (q : ℤ)
    {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) :
    G.incKoszulPerturbation x ∈ incTotalInternalPiece q := by
  rw [← x.sum_single, map_finsuppSum]
  apply (incTotalInternalPiece q).sum_mem
  intro S hS
  change G.incKoszulPerturbation (single S (x S)) ∈ incTotalInternalPiece q
  rw [G.incKoszulPerturbation_single]
  apply (incTotalInternalPiece q).sum_mem
  intro e he
  apply incTotalInternalPiece_single
  have hcard := Finset.card_erase_add_one he
  have hdeg : q - ((S.erase e).card : ℤ) = q - (S.card : ℤ) + 1 := by omega
  rw [hdeg]
  have h1 := G.incEdgeAction_coefficient_degree e (q - (S.card : ℤ)) (hx S)
  have h2 := coefficientwise_smul_constant
    (homogeneousCoeffPiece (q - (S.card : ℤ) + 1)) (incKoszulSign_constant S e) h1
  exact (CechProduct.contraction_matrices (IncCoeffRing E) (incConstantSubring E)
    (G.deg (S.erase e))).sign.preserve_coefficients _ h2

theorem incCechContraction_d_internal_degree (q : ℤ)
    {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) :
    G.incCechContraction.d x ∈ incTotalInternalPiece q := by
  intro S
  rw [G.incCechContraction_d_apply]
  exact (CechProduct.contraction_matrices (IncCoeffRing E) (incConstantSubring E)
    (G.deg S)).d.preserve_coefficients _ (hx S)

theorem incCechContraction_h_internal_degree (q : ℤ)
    {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) :
    G.incCechContraction.h x ∈ incTotalInternalPiece q := by
  intro S
  rw [G.incCechContraction_h_apply]
  exact (CechProduct.contraction_matrices (IncCoeffRing E) (incConstantSubring E)
    (G.deg S)).h.preserve_coefficients _ (hx S)

theorem incCechContraction_i_internal_degree (q : ℤ)
    {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ G.incResolutionInternalPiece q) :
    G.incCechContraction.i x ∈ incTotalInternalPiece q := by
  intro S
  rw [G.incCechContraction_i_apply]
  apply (CechProduct.contraction_matrices (IncCoeffRing E) (incConstantSubring E)
    (G.deg S)).i.preserve_coefficients
  intro b
  exact hx ⟨S, b⟩

theorem incCechContraction_p_internal_degree (q : ℤ)
    {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) :
    G.incCechContraction.p x ∈ G.incResolutionInternalPiece q := by
  rintro ⟨S, b⟩
  rw [G.incCechContraction_p_apply]
  exact ((CechProduct.contraction_matrices (IncCoeffRing E) (incConstantSubring E)
    (G.deg S)).p.preserve_coefficients _ (hx S)) b

/-- The transferred differential of the already constructed resolution
preserves internal degree. No extra grading hypothesis is imposed. -/
theorem incResolutionDifferential_internal_degree (q : ℤ)
    {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ G.incResolutionInternalPiece q) :
    G.incResolutionDifferential x ∈ G.incResolutionInternalPiece q := by
  exact G.incCechContraction.transfer_mem_of_preserves G.incKoszulPerturbation
    (incTotalInternalPiece q) (G.incResolutionInternalPiece q)
    (fun _ hx => G.incKoszulPerturbation_internal_degree q hx)
    (fun _ hx => G.incCechContraction_h_internal_degree q hx)
    (fun _ hx => G.incCechContraction_i_internal_degree q hx)
    (fun _ hx => G.incCechContraction_p_internal_degree q hx)
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩ hx

/-- The actual perturbed inclusion also preserves internal degree. -/
theorem incResolutionInclusion_internal_degree (q : ℤ)
    {x : G.IncResolutionBasis →₀ IncCoeffRing E}
    (hx : x ∈ G.incResolutionInternalPiece q) :
    G.incResolutionInclusion x ∈ incTotalInternalPiece q := by
  exact G.incCechContraction.inclusion_mem_of_preserves G.incKoszulPerturbation
    (incTotalInternalPiece q) (G.incResolutionInternalPiece q)
    (fun _ hx => G.incKoszulPerturbation_internal_degree q hx)
    (fun _ hx => G.incCechContraction_h_internal_degree q hx)
    (fun _ hx => G.incCechContraction_i_internal_degree q hx)
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩ hx

/-- The actual perturbed projection preserves internal degree. -/
theorem incResolutionProjection_internal_degree (q : ℤ)
    {x : IncTotalModule (V := V) (E := E)}
    (hx : x ∈ incTotalInternalPiece q) :
    G.incResolutionProjection x ∈ G.incResolutionInternalPiece q := by
  exact G.incCechContraction.projection_mem_of_preserves G.incKoszulPerturbation
    (incTotalInternalPiece q) (G.incResolutionInternalPiece q)
    (fun _ hx => G.incKoszulPerturbation_internal_degree q hx)
    (fun _ hx => G.incCechContraction_h_internal_degree q hx)
    (fun _ hx => G.incCechContraction_p_internal_degree q hx)
    ⟨_, G.incKoszulPerturbation_h_nilpotent⟩ hx

/-- Entrywise form: a coefficient from state `b` to state `c` is
homogeneous of degree `|b.S|-|c.S|`, with negative degrees interpreted as zero. -/
theorem incResolutionDifferential_entry_degree (b c : G.IncResolutionBasis) :
    G.incResolutionDifferential (single b 1) c ∈
      homogeneousCoeffPiece
        ((G.incResolutionInternalDegree b : ℤ) - G.incResolutionInternalDegree c) := by
  have h1 : (1 : IncCoeffRing E) ∈ homogeneousCoeffPiece (0 : ℤ) := by
    simpa only [map_one] using homogeneousCoeffPiece_C
      (σ := E × Fin 2 × Fin 2) (1 : ℂ)
  have hx : single b (1 : IncCoeffRing E) ∈
      G.incResolutionInternalPiece (G.incResolutionInternalDegree b : ℤ) :=
    weightedFreePiece_single _ _ _ (by simpa only [sub_self] using h1)
  exact (G.incResolutionDifferential_internal_degree _ hx) c

/-- A nonzero differential entry never increases the edge-state weight. -/
theorem incResolutionDifferential_entry_order (b c : G.IncResolutionBasis)
    (h : G.incResolutionDifferential (single b 1) c ≠ 0) :
    G.incResolutionInternalDegree c ≤ G.incResolutionInternalDegree b := by
  by_contra hn
  have hd := G.incResolutionDifferential_entry_degree b c
  rw [homogeneousCoeffPiece_negative (by omega)] at hd
  exact h hd

end BPFixedPoints.Multigraph
