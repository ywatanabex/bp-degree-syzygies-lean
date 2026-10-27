import BPFixedPoints.Incidence.VertexProjectiveTwistTwoH2States
import BPFixedPoints.Incidence.CechTwoTopStatePiece

/-! # Actual two-vertex H2 for every nonpositive twist

The target is the degree-two submodule of the original state module.
All base actions, representatives and connecting maps remain the original ones.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct TopologicalSpace Opposite Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] [IsNoetherianRing R]
noncomputable local instance vertexTwoH2PieceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R (Fin 2))) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual H2 equals the original degree-two state piece for all nonpositive two-vertex twists. -/
noncomputable def vertexTwistTwoH2PieceLinearEquiv (d : Fin 2 → ℕ) :
    letI := vertexTwistTwoH2BaseModule R d
    (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2 ≃ₗ[R] twoTopStatePiece R d :=
  (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))).symm.trans
    (twoRectangleStatePieceEquiv R d)

/-- Every original coefficient connecting representative retains its original state projection. -/
theorem vertexTwistTwoH2PieceLinearEquiv_representative (d : Fin 2 → ℕ)
    (x : FaceRing R twoTopFace) :
    vertexTwistTwoH2PieceLinearEquiv R d
      (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ)) (Submodule.Quotient.mk x)) =
      twoTopStatePieceProjection R d x := by
  change twoRectangleStatePieceEquiv R d
    ((vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))).symm
      (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ)) (Submodule.Quotient.mk x))) = _
  rw [LinearEquiv.symm_apply_apply,twoRectangleStatePieceEquiv_mk]

/-- The inverse retains the original inclusion, full-overlap frame and both connecting maps. -/
theorem vertexTwistTwoH2PieceLinearEquiv_symm (d : Fin 2 → ℕ) (s : twoTopStatePiece R d) :
    (vertexTwistTwoH2PieceLinearEquiv R d).symm s =
      vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))
        (Submodule.Quotient.mk (faceEquiv R ((contraction R d).i s) twoTopFace)) := by
  apply (vertexTwistTwoH2PieceLinearEquiv R d).injective
  rw [LinearEquiv.apply_symm_apply,vertexTwistTwoH2PieceLinearEquiv_representative,
    twoTopStatePieceProjection_inclusion]

/-- On strictly negative twists this is precisely the previous specified state comparison. -/
theorem vertexTwistTwoH2PieceLinearEquiv_coe (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) :
    (vertexTwistTwoH2PieceLinearEquiv R d x).val = vertexTwistTwoH2StateLinearEquiv R d hd x := by
  obtain ⟨q,rfl⟩ := (vertexTwistTwoCoefficientH2LinearEquiv R (fun v => -(d v : ℤ))).surjective x
  induction q using Submodule.Quotient.induction_on with
  | _ z =>
    rw [vertexTwistTwoH2PieceLinearEquiv_representative,vertexTwistTwoH2StateLinearEquiv_representative]
    rfl

/-- The actual original H2 is finite free even when a twist entry is zero. -/
theorem vertexTwistTwoH2_free_all (d : Fin 2 → ℕ) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.Free R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) := by
  let := vertexTwistTwoH2BaseModule R d
  exact Module.Free.of_equiv ((vertexTwistTwoH2PieceLinearEquiv R d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- Finiteness uses the finite original state basis and Mathlib's supported-Finsupp equivalence. -/
theorem vertexTwistTwoH2_finite_all (d : Fin 2 → ℕ) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.Finite R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) := by
  classical
  let := vertexTwistTwoH2BaseModule R d
  exact Module.Finite.equiv ((vertexTwistTwoH2PieceLinearEquiv R d).trans
    (supportedEquivFinsupp (R := R) (M := R) _)).symm

/-- A zero twist entry forces the original state degree below two, so actual H2 vanishes. -/
theorem vertexTwistTwoH2_eq_zero_of_zero (d : Fin 2 → ℕ) (v : Fin 2) (hv : d v = 0)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) : x = 0 := by
  apply (vertexTwistTwoH2PieceLinearEquiv R d).injective
  rw [map_zero]
  apply Subtype.ext
  apply Finsupp.ext
  intro κ
  apply (mem_supported' R _).mp (vertexTwistTwoH2PieceLinearEquiv R d x).property
  change (cohomologyDegree d : ℤ) ≠ 2
  have h : cohomologyDegree d ≠ 2 := by
    intro he
    have hh := (two_cohomologyDegree_iff d).mp he v
    omega
  exact_mod_cast h

/-- The original geometric H2 rank formula holds for every nonpositive two-vertex twist. -/
theorem vertexTwistTwoH2_finrank_all [Nontrivial R] (d : Fin 2 → ℕ) :
    letI := vertexTwistTwoH2BaseModule R d
    Module.finrank R ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) =
      (d 0-1)*(d 1-1) := by
  classical
  let := vertexTwistTwoH2BaseModule R d
  by_cases hd : ∀ v, 0 < d v
  · exact vertexTwistTwoH2_finrank R d hd
  · have hz : d 0 = 0 ∨ d 1 = 0 := by
      rw [Fin.forall_fin_two] at hd
      omega
    have hsub : Subsingleton ((vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) := by
      rcases hz with h | h
      · exact ⟨fun x y => (vertexTwistTwoH2_eq_zero_of_zero R d 0 h x).trans
          (vertexTwistTwoH2_eq_zero_of_zero R d 0 h y).symm⟩
      · exact ⟨fun x y => (vertexTwistTwoH2_eq_zero_of_zero R d 1 h x).trans
          (vertexTwistTwoH2_eq_zero_of_zero R d 1 h y).symm⟩
    rw [Module.finrank_zero_of_subsingleton]
    rcases hz with h | h <;> simp [h]

/-- A degree-one factor also annihilates H2 when the other twist entry is zero. -/
theorem vertexTwistTwoH2_eq_zero_of_one_all (d : Fin 2 → ℕ) (v : Fin 2) (hv : d v = 1)
    (x : (vertexTwistAbelianSheaf R (Fin 2) (fun v => -(d v : ℤ))).H 2) : x = 0 := by
  by_cases hd : ∀ v, 0 < d v
  · exact vertexTwistTwoH2_eq_zero_of_one R d hd v hv x
  · push Not at hd
    obtain ⟨w,hw⟩ := hd
    exact vertexTwistTwoH2_eq_zero_of_zero R d w (by omega) x

end BPFixedPoints.ProjectiveLine
