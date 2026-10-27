import BPFixedPoints.Incidence.CechTwoTopState

/-! # The original degree-two state piece for every nonpositive two-vertex twist -/

namespace BPFixedPoints.CechProduct
open Finsupp ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]

/-- The degree-two part of the original state module, with its original base action. -/
abbrev twoTopStatePiece (d : Fin 2 → ℕ) : Submodule R (H R d) :=
  supported R R {_κ : HBasis d | (cohomologyDegree d : ℤ) = 2}

/-- Two-vertex states have degree two exactly when both twists are strictly negative. -/
theorem two_cohomologyDegree_iff (d : Fin 2 → ℕ) :
    cohomologyDegree d = 2 ↔ ∀ v, 0 < d v := by
  constructor
  · intro h
    rw [Fin.forall_fin_two]
    have h' : (if d 0 = 0 then 0 else 1) + (if d 1 = 0 then 0 else 1) = (2 : ℕ) := by
      simpa [cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ] using h
    split_ifs at h' <;> omega
  · exact two_cohomologyDegree d

/-- The original full-overlap inclusion is homogeneous of degree two. -/
theorem twoTopInsert_degree (x : FaceRing R twoTopFace) :
    twoTopInsert R x ∈ supported R R {b | (cechDegree b : ℤ) = 2} := by
  rw [mem_supported_iff_faceEquiv,faceEquiv_twoTopInsert]
  intro q hq
  apply Pi.single_eq_of_ne
  intro h
  subst q
  exact hq (by rw [twoFaceDegree]; norm_num)

/-- The original state projection lands in its original degree-two piece. -/
theorem twoTopStateProjection_degree (d : Fin 2 → ℕ) (x : FaceRing R twoTopFace) :
    twoTopStateProjection R d x ∈ twoTopStatePiece R d := by
  exact contraction_p_degree R d 2 (twoTopInsert R x) (twoTopInsert_degree R x)

/-- Away from state degree two the original top projection vanishes. -/
theorem twoTopStateProjection_eq_zero_of_degree (d : Fin 2 → ℕ)
    (hd : cohomologyDegree d ≠ 2) (x : FaceRing R twoTopFace) :
    twoTopStateProjection R d x = 0 := by
  apply Finsupp.ext
  intro κ
  apply (mem_supported' R _).mp (twoTopStateProjection_degree R d x)
  change (cohomologyDegree d : ℤ) ≠ 2
  exact_mod_cast hd

/-- Every original rectangular boundary vanishes under the original projection, including zero twists. -/
theorem twoTopStateProjection_boundary_all (d : Fin 2 → ℕ) (x : TwoRectangleCoefficients R) :
    twoTopStateProjection R d (twoRectangleBoundary R (fun v => -(d v : ℤ)) x) = 0 := by
  by_cases hd : cohomologyDegree d = 2
  · exact twoTopStateProjection_boundary R d ((two_cohomologyDegree_iff d).mp hd) x
  · exact twoTopStateProjection_eq_zero_of_degree R d hd _

/-- Codomain restriction of the original projection; no action or representative is transported. -/
noncomputable def twoTopStatePieceProjection (d : Fin 2 → ℕ) :
    FaceRing R twoTopFace →ₗ[R] twoTopStatePiece R d :=
  (twoTopStateProjection R d).codRestrict _ (twoTopStateProjection_degree R d)

/-- The original inclusion supplies an original top-face representative for each degree-two state. -/
theorem twoTopStatePieceProjection_inclusion (d : Fin 2 → ℕ) (s : twoTopStatePiece R d) :
    twoTopStatePieceProjection R d (faceEquiv R ((contraction R d).i s) twoTopFace) = s := by
  apply Subtype.ext
  change (contraction R d).p (twoTopInsert R _) = _
  rw [twoTopInsert_of_degree R _ (by
    simpa only [add_zero] using contraction_i_degree R d 2 s.val s.property)]
  exact LinearMap.congr_fun (contraction R d).p_i s

/-- Surjectivity follows from the specified original inclusion, without a positivity hypothesis. -/
theorem twoTopStatePieceProjection_surjective (d : Fin 2 → ℕ) :
    Function.Surjective (twoTopStatePieceProjection R d) := by
  intro s
  exact ⟨_,twoTopStatePieceProjection_inclusion R d s⟩

/-- The original four restriction images are precisely the kernel in every nonpositive twist. -/
theorem twoRectangleBoundary_range_piece (d : Fin 2 → ℕ) :
    LinearMap.range (twoRectangleBoundary R (fun v => -(d v : ℤ))) =
      LinearMap.ker (twoTopStatePieceProjection R d) := by
  ext x
  change (∃ y, twoRectangleBoundary R (fun v => -(d v : ℤ)) y = x) ↔
    twoTopStatePieceProjection R d x = 0
  constructor
  · rintro ⟨y,rfl⟩
    apply Subtype.ext
    exact twoTopStateProjection_boundary_all R d y
  · intro h
    exact twoTopStateProjection_zero_isBoundary R d x (congrArg Subtype.val h)

/-- The native quotient by an image agrees with the target of a specified exact surjection. -/
noncomputable def quotientEquivOfExact {A : Type*} {B : Type*} {D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup D]
    [Module R A] [Module R B] [Module R D] (f : A →ₗ[R] B) (g : B →ₗ[R] D)
    (he : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g) :
    (B ⧸ LinearMap.range f) ≃ₗ[R] D :=
  (Submodule.quotEquivOfEq _ _ he).trans (g.quotKerEquivOfSurjective hg)

/-- The original rectangular quotient equals the original degree-two state piece for every nonpositive twist. -/
noncomputable def twoRectangleStatePieceEquiv (d : Fin 2 → ℕ) :
    (FaceRing R twoTopFace ⧸ LinearMap.range (twoRectangleBoundary R (fun v => -(d v : ℤ)))) ≃ₗ[R]
      twoTopStatePiece R d :=
  quotientEquivOfExact R (A := TwoRectangleCoefficients R) (B := FaceRing R twoTopFace)
    (D := twoTopStatePiece R d) (twoRectangleBoundary R (fun v => -(d v : ℤ)))
    (twoTopStatePieceProjection R d) (twoRectangleBoundary_range_piece R d)
    (twoTopStatePieceProjection_surjective R d)

/-- The comparison sends each original coefficient representative to the original projection. -/
theorem twoRectangleStatePieceEquiv_mk (d : Fin 2 → ℕ) (x : FaceRing R twoTopFace) :
    twoRectangleStatePieceEquiv R d (Submodule.Quotient.mk x) =
      twoTopStatePieceProjection R d x := rfl

end BPFixedPoints.CechProduct
