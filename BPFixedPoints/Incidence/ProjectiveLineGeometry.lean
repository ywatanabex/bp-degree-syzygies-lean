import BPFixedPoints.Incidence.ProjectiveLineCharts
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # The two genuine polynomial charts covering Mathlib's projective line

The standard Proj chart isomorphism and cover are taken from Mathlib. Only the
explicit homogeneous-coordinate comparison is supplied by this project.
-/

namespace BPFixedPoints.ProjectiveLine
open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The actual standard open of Mathlib's Proj. -/
noncomputable def standardOpen (i : Fin 2) : (projectiveLine R).Opens :=
  Proj.basicOpen (grading R) (X i)

/-- Genuine scheme isomorphism from the standard Proj open to the polynomial chart. -/
noncomputable def standardOpenIso (i : Fin 2) :
    (standardOpen R i).toScheme ≅ Spec (CommRingCat.of (Polynomial R)) :=
  Proj.basicOpenIsoSpec (grading R) (X i) (isHomogeneous_X R i) (by decide) ≪≫
    Scheme.Spec.mapIso (chartEquiv R i).toCommRingCatIso.symm.op

/-- Existence form of the actual Proj chart comparison. -/
theorem standardOpen_comparison (i : Fin 2) :
    Nonempty ((standardOpen R i).toScheme ≅ Spec (CommRingCat.of (Polynomial R))) :=
  ⟨standardOpenIso R i⟩

/-- The actual chart inclusion into the independently defined projective line. -/
noncomputable def chartι (i : Fin 2) :
    Spec (CommRingCat.of (Polynomial R)) ⟶ projectiveLine R :=
  Spec.map (chartEquiv R i).toCommRingCatIso.hom ≫
    Proj.awayι (grading R) (X i) (isHomogeneous_X R i) (by decide)

instance chartι_isOpenImmersion (i : Fin 2) : IsOpenImmersion (chartι R i) := by
  dsimp only [chartι]
  infer_instance

/-- The original variable opens cover Proj because they span its irrelevant ideal. -/
theorem irrelevant_le_variables :
    (HomogeneousIdeal.irrelevant (grading R)).toIdeal ≤
      Ideal.span (Set.range (X : Fin 2 → CoxRing R)) := by
  classical
  rw [HomogeneousIdeal.irrelevant_eq_span]
  refine Ideal.span_le.mpr (Set.iUnion_subset fun n => Set.iUnion_subset fun hn => ?_)
  intro p hp
  change p.IsHomogeneous n at hp
  change p ∈ MvPolynomial.idealOfVars (Fin 2) R
  rw [← pow_one (MvPolynomial.idealOfVars (Fin 2) R), mem_pow_idealOfVars_iff]
  intro d hd
  change 1 ≤ ∑ j ∈ d.support, d j
  rw [← hp.degree_eq_sum_deg_support hd]
  exact hn

/-- Mathlib's standard two-chart cover in homogeneous localization coordinates. -/
noncomputable def homogeneousChartCover : (projectiveLine R).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (grading R) (X : Fin 2 → CoxRing R)
    (fun i => isHomogeneous_X R i) (fun _ => by decide) (irrelevant_le_variables R)

/-- The two polynomial charts cover the actual projective line. -/
noncomputable def polynomialChartCover : (projectiveLine R).OpenCover :=
  (homogeneousChartCover R).openCover.copy (Fin 2)
    (fun _ => Spec (CommRingCat.of (Polynomial R))) (chartι R) (Equiv.refl _)
    (fun i => Scheme.Spec.mapIso (chartEquiv R i).toCommRingCatIso.op) (fun _ => rfl)

/-- The polynomial chart has exactly the original Proj standard open as its image. -/
theorem chartι_opensRange (i : Fin 2) : (chartι R i).opensRange = standardOpen R i := by
  dsimp only [chartι]
  rw [Scheme.Hom.opensRange_comp_of_isIso, Proj.opensRange_awayι]
  rfl

/-- The original two standard opens cover the whole projective line. -/
theorem standardOpen_cover : standardOpen R 0 ⊔ standardOpen R 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top (grading R) (X : Fin 2 → CoxRing R)
    (irrelevant_le_variables R)
  have h' : (⨆ i : Fin 2, standardOpen R i) = ⊤ := h
  apply le_antisymm le_top
  rw [← h']
  refine iSup_le fun i => ?_
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

end BPFixedPoints.ProjectiveLine
