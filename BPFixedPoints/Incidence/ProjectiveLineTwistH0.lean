import BPFixedPoints.Incidence.ProjectiveLineTwistGlobalSections
import BPFixedPoints.Incidence.PolynomialCechLineComparison

/-! # Genuine degree-zero sections of the original nonpositive projective twists

The original coefficient contraction computes the genuine global section
kernel. This comparison needs no affine higher-vanishing hypothesis. The
original geometric base linearity is proved in `ProjectiveLineTwistBaseLinearity`.
Higher derived cohomology remains a separate comparison.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false

variable (R : Type) [CommRing R]

/-- The original polynomial coefficient equivalence maps exactly the matching kernel to the existing Cech kernel. -/
theorem polynomialCechCoefficientEquiv_map_ker (d : ℕ) :
    (LinearMap.ker (polynomialTwistDifference R (-(d : ℤ)))).map
      (polynomialCechCoefficientEquiv R).toLinearMap =
      LinearMap.ker (CechLine.differential R d) := by
  have hm (p : Polynomial R × Polynomial R) :
      polynomialCechCoefficientEquiv R p ∈ LinearMap.ker (CechLine.differential R d) ↔
        p ∈ LinearMap.ker (polynomialTwistDifference R (-(d : ℤ))) := by
    change CechLine.differential R d (polynomialCechCoefficientEquiv R p) = 0 ↔ _
    constructor
    · intro h
      apply (laurentCechCoefficientEquiv R).injective
      rw [map_zero, polynomialTwistDifference_cech, h, neg_zero]
    · intro h
      have hc := polynomialTwistDifference_cech R d p
      rw [h, map_zero, eq_comm, neg_eq_zero] at hc
      exact hc
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hm p).mpr hp
  · intro hx
    refine ⟨(polynomialCechCoefficientEquiv R).symm x, ?_,
      (polynomialCechCoefficientEquiv R).apply_symm_apply x⟩
    apply (hm _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hx

/-- The original polynomial matching kernel is linearly isomorphic to the existing coefficient Cech kernel. -/
noncomputable def polynomialTwistKernelCechEquiv (d : ℕ) :
    LinearMap.ker (polynomialTwistDifference R (-(d : ℤ))) ≃ₗ[R]
      LinearMap.ker (CechLine.differential R d) :=
  (polynomialCechCoefficientEquiv R).ofSubmodules _ _ (polynomialCechCoefficientEquiv_map_ker R d)

/-- The original contraction computes precisely all degree-zero Cech cocycles. -/
noncomputable def cechLineKernelH0Equiv (d : ℕ) :
    LinearMap.ker (CechLine.differential R d) ≃ₗ[R] CechLine.H0 R d where
  toFun x := CechLine.projectionZero R d x.val
  invFun x := ⟨CechLine.inclusionZero R d x,
    LinearMap.congr_fun (CechLine.differential_inclusionZero R d) x⟩
  left_inv x := by
    apply Subtype.ext
    have h := LinearMap.congr_fun (CechLine.homotopy_differential R d) x.val
    change CechLine.homotopy R d (CechLine.differential R d x.val) =
      x.val - CechLine.inclusionZero R d (CechLine.projectionZero R d x.val) at h
    rw [x.property, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm
  right_inv x := LinearMap.congr_fun (CechLine.projectionZero_inclusionZero R d) x
  map_add' x y := (CechLine.projectionZero R d).map_add x.val y.val
  map_smul' r x := (CechLine.projectionZero R d).map_smul r x.val

/-- Genuine global sections of the actual nonpositive twist are the original degree-zero state module. -/
noncomputable def twistSheafGlobalSectionsH0Equiv (d : ℕ) :
    Γ(twistSheaf R (-(d : ℤ)), ⊤) ≃+ CechLine.H0 R d :=
  (twistSheafGlobalSectionsPolynomialEquiv R _).trans
    ((polynomialTwistKernelCechEquiv R d).trans (cechLineKernelH0Equiv R d)).toAddEquiv

/-- Existence form of the genuine degree-zero section comparison with the original state module. -/
theorem twistSheafGlobalSectionsH0_comparison (d : ℕ) :
    Nonempty (Γ(twistSheaf R (-(d : ℤ)), ⊤) ≃+ CechLine.H0 R d) :=
  ⟨twistSheafGlobalSectionsH0Equiv R d⟩

/-- No nonzero genuine global sections exist for a strictly negative original twist. -/
theorem twistSheaf_negative_global_eq_zero (d : ℕ) (hd : 0 < d)
    (s : Γ(twistSheaf R (-(d : ℤ)), ⊤)) : s = 0 := by
  have : IsEmpty (CechLine.H0Index d) := by
    dsimp only [CechLine.H0Index]
    rw [ite_eq_right (Nat.ne_of_gt hd)]
    infer_instance
  apply (twistSheafGlobalSectionsH0Equiv R d).injective
  exact Subsingleton.elim _ _

end BPFixedPoints.ProjectiveLine
