import BPFixedPoints.Incidence.KoszulLocalModel
import BPFixedPoints.Incidence.KoszulFaceGrading
import BPFixedPoints.Incidence.CechFaceDegree
import BPFixedPoints.Incidence.ResolutionDegree

/-!
# Local Koszul contraction and total degree

The local quotient has exterior degree zero, hence total degree is minus
Čech degree. The target vanishes in positive total degrees, so the second
perturbation proves exactness there.
-/

namespace BPFixedPoints.Multigraph

open CechProduct Koszul IncidencePerturbation ResolutionTools Finsupp

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Total-degree part of the product of local quotients. -/
noncomputable def incQuotientPiece (n : ℤ) : Submodule ℂ G.IncQuotientCechModule where
  carrier := {y | ∀ q, n ≠ -(faceDegree q : ℤ) → y q = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hx hy := by
    intro q hq
    simp only [Pi.add_apply, hx q hq, hy q hq, add_zero]
  smul_mem' r x hx := by
    intro q hq
    simp only [Pi.smul_apply, hx q hq, smul_zero]

/-- A local quotient cannot have positive total degree. -/
theorem incQuotientPiece_eq_bot_of_positive {n : ℤ} (hn : 0 < n) :
    G.incQuotientPiece n = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  funext q
  exact hx q (by omega)

theorem incKoszulContraction_h_face
    (x : IncTotalModule (V := V) (E := E)) (q : V → Fin 3) :
    totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulContraction.h x) q =
      (-1 : ℂ) ^ faceDegree q • (G.incFaceContraction q).h
        (totalFaceEquiv ℂ (IncCoeffIdx E) E x q) := by
  rw [incKoszulContraction, Contraction.congr_h_apply, LinearEquiv.symm_symm,
    LinearEquiv.apply_symm_apply]
  rfl

theorem incKoszulContraction_i_face
    (x : G.IncQuotientCechModule) (q : V → Fin 3) :
    totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulContraction.i x) q =
      (G.incFaceContraction q).i (x q) := by
  rw [incKoszulContraction, Contraction.congr_i_apply, LinearEquiv.apply_symm_apply]
  rfl

theorem incKoszulContraction_p_face
    (x : IncTotalModule (V := V) (E := E)) (q : V → Fin 3) :
    G.incKoszulContraction.p x q =
      (G.incFaceContraction q).p (totalFaceEquiv ℂ (IncCoeffIdx E) E x q) := by
  rw [incKoszulContraction, Contraction.congr_p_apply]
  rfl

/-- Returning local homotopy to the total module still gives zero empty-state coefficient. -/
theorem incKoszulContraction_h_empty (x : IncTotalModule (V := V) (E := E)) :
    (G.incKoszulContraction.h x) ∅ = 0 := by
  apply (polynomialFaceEquiv ℂ (IncCoeffIdx E)).injective
  rw [map_zero]
  funext q
  change (totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulContraction.h x) q) ∅ = 0
  rw [G.incKoszulContraction_h_face, Finsupp.smul_apply,
    G.incFaceContraction_h_empty, smul_zero]

theorem incKoszulContraction_i_apply_of_ne_empty (x : G.IncQuotientCechModule)
    (S : Finset E) (hS : S ≠ ∅) : (G.incKoszulContraction.i x) S = 0 := by
  apply (polynomialFaceEquiv ℂ (IncCoeffIdx E)).injective
  rw [map_zero]
  funext q
  change (totalFaceEquiv ℂ (IncCoeffIdx E) E (G.incKoszulContraction.i x) q) S = 0
  rw [G.incKoszulContraction_i_face, G.incFaceContraction_i_apply_of_ne_empty q (x q) S hS]

theorem incKoszulContraction_h_shifts :
    Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      1 G.incKoszulContraction.h := by
  intro n x hx
  apply (totalFaceEquiv_degree_iff ℂ (IncCoeffIdx E) E (n + 1) _).mpr
  have hxf := (totalFaceEquiv_degree_iff ℂ (IncCoeffIdx E) E n x).mp hx
  intro q
  rw [G.incKoszulContraction_h_face]
  apply Submodule.smul_mem
  have h := G.incFaceContraction_h_degree q (n + (faceDegree q : ℤ)) _ (hxf q)
  have hn : n + (faceDegree q : ℤ) + 1 = n + 1 + (faceDegree q : ℤ) := by ring
  simpa only [exteriorDegree, hn] using h

theorem incKoszulContraction_i_shifts :
    Shifts (R := ℂ) (M := G.IncQuotientCechModule)
      (N := IncTotalModule (V := V) (E := E)) G.incQuotientPiece
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      0 G.incKoszulContraction.i := by
  intro n x hx
  apply (totalFaceEquiv_degree_iff ℂ (IncCoeffIdx E) E (n + 0) _).mpr
  intro q
  rw [G.incKoszulContraction_i_face]
  by_cases hq : n = -(faceDegree q : ℤ)
  · have hn : n + 0 + (faceDegree q : ℤ) = 0 := by omega
    rw [hn]
    exact G.incFaceContraction_i_mem_degree_zero q (x q)
  · rw [hx q hq, map_zero]
    exact Submodule.zero_mem _

theorem incKoszulContraction_p_shifts :
    Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := G.IncQuotientCechModule)
      (fun n => (incTotalPiece (V := V) (E := E) n).restrictScalars ℂ)
      G.incQuotientPiece 0 G.incKoszulContraction.p := by
  intro n x hx q hq
  rw [G.incKoszulContraction_p_face]
  have hxf := (totalFaceEquiv_degree_iff ℂ (IncCoeffIdx E) E n x).mp hx
  exact G.incFaceContraction_p_eq_zero q (hxf q) (by omega)

/-- Local Koszul homotopy preserves the Čech face. -/
theorem incKoszulContraction_h_cechShifts :
    Shifts (R := ℂ) (M := IncTotalModule (V := V) (E := E))
      (N := IncTotalModule (V := V) (E := E))
      (fun n => (incCechPiece (V := V) (E := E) n).restrictScalars ℂ)
      (fun n => (incCechPiece (V := V) (E := E) n).restrictScalars ℂ)
      0 G.incKoszulContraction.h := by
  intro n x hx
  apply (totalFaceEquiv_cechDegree_iff ℂ (IncCoeffIdx E) E (n + 0) _).mpr
  have hxf := (totalFaceEquiv_cechDegree_iff ℂ (IncCoeffIdx E) E n x).mp hx
  intro q hq
  rw [G.incKoszulContraction_h_face, hxf q (by simpa only [add_zero] using hq),
    map_zero, smul_zero]

end BPFixedPoints.Multigraph
