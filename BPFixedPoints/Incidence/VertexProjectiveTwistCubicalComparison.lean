import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalSections
import BPFixedPoints.Incidence.CechCupSigns
import BPFixedPoints.Incidence.CechFaceDegree

/-! # Specified chain comparison for the actual cubical section complex

Multiplication by degree parity reconciles the native left-minus-right
restriction convention with the original right-minus-left tensor convention.
The actual differential is defined before, and independently of, this comparison.
This result concerns cubical sections; comparison with higher sheaf Ext remains separate.
-/

namespace BPFixedPoints.CechProduct
variable (R : Type) [CommRing R] {V : Type} [Fintype V]

/-- The existing degree-parity involution as a linear equivalence. -/
noncomputable def cubicalParityEquiv : C R V ≃ₗ[R] C R V :=
  { parity R with
    invFun := parity R
    left_inv := parity_twice R
    right_inv := parity_twice R }

/-- Parity has its specified value on every original face component. -/
theorem faceEquiv_parity (x : C R V) (q : V → Fin 3) :
    faceEquiv R (parity R x) q = (-1 : R) ^ faceDegree q • faceEquiv R x q := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy,smul_add]
  | single b c =>
      obtain ⟨⟨r,m⟩,rfl⟩ := faceBasisEquiv.symm.surjective b
      change faceEquiv R (parity R (Finsupp.single (embedFace r m) c)) q =
        (-1 : R) ^ faceDegree q • faceEquiv R (Finsupp.single (embedFace r m) c) q
      rw [parity, contraction_sign_single, map_smul, Pi.smul_apply]
      by_cases hq : q = r
      · subst r
        rw [cechDegree_embedFace]
      · simp [faceEquiv_single_ne R hq]

end BPFixedPoints.CechProduct

namespace BPFixedPoints.ProjectiveLine
open CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- Specified signed original coordinates from actual sections to the original tensor complex. -/
noncomputable def vertexTwistCubicalChainEquiv (d : V → ℕ) :
    VertexTwistCubicalSections R V (fun v => -(d v : ℤ)) ≃ₗ[R] C R V :=
  ((vertexTwistCubicalCoordinates R V (fun v => -(d v : ℤ))).trans (faceEquiv R).symm).trans
    (cubicalParityEquiv R)

/-- Every face component of the comparison is the original frame coordinate times its degree parity. -/
theorem vertexTwistCubicalChainEquiv_face (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) (q : V → Fin 3) :
    faceEquiv R (vertexTwistCubicalChainEquiv R V d x) q =
      (-1 : R) ^ faceDegree q • vertexTwistSheafFaceSectionsEquiv R V (fun v => -(d v : ℤ)) q (x q) := by
  change faceEquiv R (parity R ((faceEquiv R).symm (vertexTwistCubicalCoordinates R V _ x))) q = _
  rw [faceEquiv_parity, LinearEquiv.apply_symm_apply]
  rfl

private theorem unsigned_d (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    (faceEquiv R).symm (vertexTwistCubicalCoordinates R V _ (vertexTwistCubicalD R V _ x)) =
      -(contraction R d).d ((faceEquiv R).symm (vertexTwistCubicalCoordinates R V _ x)) := by
  apply (faceEquiv R).injective
  rw [LinearEquiv.apply_symm_apply, map_neg, faceEquiv_d, LinearEquiv.apply_symm_apply,
    vertexTwistCubicalCoordinates_d]

/-- The specified map intertwines the independently defined native differential with the original tensor differential. -/
theorem vertexTwistCubicalChainEquiv_d (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    vertexTwistCubicalChainEquiv R V d (vertexTwistCubicalD R V _ x) =
      (contraction R d).d (vertexTwistCubicalChainEquiv R V d x) := by
  change parity R ((faceEquiv R).symm (vertexTwistCubicalCoordinates R V _ (vertexTwistCubicalD R V _ x))) =
    (contraction R d).d (parity R ((faceEquiv R).symm (vertexTwistCubicalCoordinates R V _ x)))
  rw [unsigned_d, map_neg, parity_d, neg_neg]

/-- Actual face-degree support, defined directly on the original native sections. -/
def VertexTwistCubicalHomogeneous (a : V → ℤ) (n : ℤ)
    (x : VertexTwistCubicalSections R V a) : Prop :=
  ∀ q, (faceDegree q : ℤ) ≠ n → x q = 0

/-- The specified comparison preserves every original face degree. -/
theorem vertexTwistCubicalChainEquiv_degree (d : V → ℕ) (n : ℤ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    vertexTwistCubicalChainEquiv R V d x ∈
      Finsupp.supported R R {b | (cechDegree b : ℤ) = n} ↔
        VertexTwistCubicalHomogeneous R V _ n x := by
  rw [mem_supported_iff_faceEquiv]
  have he (q : V → Fin 3) :
      faceEquiv R (vertexTwistCubicalChainEquiv R V d x) q = 0 ↔ x q = 0 := by
    rw [vertexTwistCubicalChainEquiv_face]
    rcases neg_one_pow_eq_or R (faceDegree q) with h | h <;>
      simp only [h, one_smul, neg_one_smul, neg_eq_zero, LinearEquiv.map_eq_zero_iff]
  simp only [he, VertexTwistCubicalHomogeneous]

/-- The native differential raises the original overlap degree by one. -/
theorem vertexTwistCubicalD_degree (d : V → ℕ) (n : ℤ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ)))
    (hx : VertexTwistCubicalHomogeneous R V _ n x) :
    VertexTwistCubicalHomogeneous R V _ (n+1) (vertexTwistCubicalD R V _ x) := by
  apply (vertexTwistCubicalChainEquiv_degree R V d (n+1) _).mp
  rw [vertexTwistCubicalChainEquiv_d]
  exact contraction_d_degree R d n _ ((vertexTwistCubicalChainEquiv_degree R V d n x).mpr hx)

/-- The actual cubical differential squares to zero, without any Noetherian or field hypothesis. -/
theorem vertexTwistCubicalD_square (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    vertexTwistCubicalD R V _ (vertexTwistCubicalD R V _ x) = 0 := by
  apply (vertexTwistCubicalChainEquiv R V d).injective
  rw [vertexTwistCubicalChainEquiv_d, vertexTwistCubicalChainEquiv_d, map_zero]
  exact LinearMap.congr_fun (contraction R d).d_sq _

/-- Reuse the established state contraction through the specified chain comparison. -/
noncomputable def vertexTwistCubicalContraction (d : V → ℕ) :
    GradedContraction R (VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) (H R d) :=
  (contraction R d).congr (vertexTwistCubicalChainEquiv R V d).symm (LinearEquiv.refl R _)

/-- The reused contraction has precisely the previously defined actual section differential. -/
theorem vertexTwistCubicalContraction_d (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ))) :
    (vertexTwistCubicalContraction R V d).d x = vertexTwistCubicalD R V _ x := by
  change ((contraction R d).congr (vertexTwistCubicalChainEquiv R V d).symm
    (LinearEquiv.refl R _)).d x = _
  rw [GradedContraction.congr_d_apply]
  apply (vertexTwistCubicalChainEquiv R V d).injective
  rw [LinearEquiv.apply_symm_apply, vertexTwistCubicalChainEquiv_d]
  rfl

/-- Every actual cubical cocycle decomposes into its native boundary and its specified state representative. -/
theorem vertexTwistCubical_cycle_decomposition (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ)))
    (hx : vertexTwistCubicalD R V _ x = 0) :
    x = vertexTwistCubicalD R V _ ((vertexTwistCubicalContraction R V d).h x) +
      (vertexTwistCubicalContraction R V d).i ((vertexTwistCubicalContraction R V d).p x) := by
  have hd : (vertexTwistCubicalContraction R V d).d x = 0 := by
    rw [vertexTwistCubicalContraction_d, hx]
  have h := GradedContraction.ChainPairing.cycle_decomposition hd
  rw [vertexTwistCubicalContraction_d] at h
  exact h

/-- The specified state inclusion gives native cocycles and the original state coordinates. -/
theorem vertexTwistCubical_state_representative (d : V → ℕ) (s : H R d) :
    vertexTwistCubicalD R V _ ((vertexTwistCubicalContraction R V d).i s) = 0 ∧
      (vertexTwistCubicalContraction R V d).p ((vertexTwistCubicalContraction R V d).i s) = s := by
  constructor
  · rw [← vertexTwistCubicalContraction_d]
    exact LinearMap.congr_fun (vertexTwistCubicalContraction R V d).d_i s
  · exact LinearMap.congr_fun (vertexTwistCubicalContraction R V d).p_i s

/-- A native cubical cocycle is an actual cubical boundary exactly when its specified state is zero. -/
theorem vertexTwistCubical_boundary_iff (d : V → ℕ)
    (x : VertexTwistCubicalSections R V (fun v => -(d v : ℤ)))
    (hx : vertexTwistCubicalD R V _ x = 0) :
    (∃ y, vertexTwistCubicalD R V _ y = x) ↔ (vertexTwistCubicalContraction R V d).p x = 0 := by
  constructor
  · rintro ⟨y,rfl⟩
    rw [← vertexTwistCubicalContraction_d]
    exact LinearMap.congr_fun (vertexTwistCubicalContraction R V d).p_d y
  · intro hp
    refine ⟨(vertexTwistCubicalContraction R V d).h x, ?_⟩
    have h := vertexTwistCubical_cycle_decomposition R V d x hx
    simpa only [hp, map_zero, add_zero] using h.symm

end BPFixedPoints.ProjectiveLine
