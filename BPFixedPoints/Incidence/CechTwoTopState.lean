import BPFixedPoints.Incidence.CechTwoRectangleSigns
import BPFixedPoints.Incidence.CechFaceDegree
import BPFixedPoints.Incidence.CechCupSigns

/-! # Original state projection on the actual two-coordinate top face -/

namespace BPFixedPoints.CechProduct
open Finsupp ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]

/-- The original two-coordinate overlap count in the original vertex labels. -/
theorem twoFaceDegree (b c : Fin 3) : faceDegree (![b,c] : Fin 2 → Fin 3) =
    (if b = 2 then 1 else 0) + (if c = 2 then 1 else 0) := by
  unfold faceDegree
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp

/-- Include the original full-overlap coefficients as original top-degree Cech chains. -/
noncomputable def twoTopInsert : FaceRing R twoTopFace →ₗ[R] C R (Fin 2) :=
  (faceEquiv R).symm.toLinearMap.comp (LinearMap.single R (fun q => FaceRing R q) twoTopFace)

/-- The inclusion retains precisely its original full-overlap coefficient. -/
theorem faceEquiv_twoTopInsert (x : FaceRing R twoTopFace) :
    faceEquiv R (twoTopInsert R x) = Pi.single twoTopFace x :=
  (faceEquiv R).apply_symm_apply _

/-- The original top component determines every two-vertex degree-two chain. -/
theorem twoTopInsert_of_degree (x : C R (Fin 2))
    (hx : x ∈ supported R R {b | (cechDegree b : ℤ) = 2}) :
    twoTopInsert R (faceEquiv R x twoTopFace) = x := by
  apply (faceEquiv R).injective
  rw [faceEquiv_twoTopInsert]
  funext q
  by_cases hq : q = twoTopFace
  · subst q
    simp
  · rw [Pi.single_eq_of_ne hq]
    symm
    apply faceEquiv_eq_zero_of_degree R hx q
    obtain ⟨⟨b,c⟩,rfl⟩ := twoFacePairEquiv.symm.surjective q
    change (faceDegree (![b,c] : Fin 2 → Fin 3) : ℤ) ≠ 2
    change (![b,c] : Fin 2 → Fin 3) ≠ twoTopFace at hq
    rw [twoFaceDegree]
    fin_cases b <;> fin_cases c <;> simp_all [twoTopFace]

/-- Every original top-face chain is closed for the original fixed-enumeration differential. -/
theorem twoTopInsert_closed (d : Fin 2 → ℕ) (x : FaceRing R twoTopFace) :
    (contraction R d).d (twoTopInsert R x) = 0 := by
  apply (faceEquiv R).injective
  rw [faceEquiv_d,faceEquiv_twoTopInsert,cubicalCoefficientD_single,map_zero]
  simp [twoTopFace,Fin.sum_univ_succ]

/-- Strictly negative twists have the original state cohomology degree two, including empty degree-one states. -/
theorem two_cohomologyDegree (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) : cohomologyDegree d = 2 := by
  simp [cohomologyDegree,lineCohomologyDegree,Fin.sum_univ_succ,ne_of_gt (hd 0),ne_of_gt (hd 1)]

/-- Original state coordinates of an original top-face representative. -/
noncomputable def twoTopStateProjection (d : Fin 2 → ℕ) : FaceRing R twoTopFace →ₗ[R] H R d :=
  (contraction R d).p.comp (twoTopInsert R)

/-- The original state projection depends only on the top component for strictly negative twists. -/
theorem twoTopStateProjection_top (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) (x : C R (Fin 2)) :
    twoTopStateProjection R d (faceEquiv R x twoTopFace) = (contraction R d).p x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | single b c =>
      obtain ⟨⟨q,m⟩,rfl⟩ := faceBasisEquiv.symm.surjective b
      change twoTopStateProjection R d (faceEquiv R (single (embedFace q m) c) twoTopFace) =
        (contraction R d).p (single (embedFace q m) c)
      by_cases hq : q = twoTopFace
      · subst q
        have hh : twoTopInsert R (faceEquiv R (single (embedFace twoTopFace m) c) twoTopFace) =
            single (embedFace twoTopFace m) c := by
          apply twoTopInsert_of_degree R
          apply single_mem_supported
          change (cechDegree (embedFace twoTopFace m) : ℤ) = 2
          rw [cechDegree_embedFace,twoFaceDegree]
          norm_num
        exact congrArg (contraction R d).p hh
      · rw [faceEquiv_single_ne R (Ne.symm hq),map_zero]
        symm
        have hdeg := contraction_p_degree R d (cechDegree (embedFace q m) : ℤ)
          (single (embedFace q m) c) (single_mem_supported R c rfl)
        apply Finsupp.ext
        intro k
        apply (mem_supported' R _).mp hdeg
        change (cohomologyDegree d : ℤ) ≠ (cechDegree (embedFace q m) : ℤ) + 0
        rw [two_cohomologyDegree d hd,cechDegree_embedFace,add_zero]
        obtain ⟨⟨i,j⟩,rfl⟩ := twoFacePairEquiv.symm.surjective q
        change (![i,j] : Fin 2 → Fin 3) ≠ twoTopFace at hq
        change (2 : ℤ) ≠ (faceDegree (![i,j] : Fin 2 → Fin 3) : ℤ)
        rw [twoFaceDegree]
        fin_cases i <;> fin_cases j <;> simp_all [twoTopFace]

/-- Every original state is obtained from an original top-face representative. -/
theorem twoTopStateProjection_surjective (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    Function.Surjective (twoTopStateProjection R d) := by
  intro s
  refine ⟨faceEquiv R ((contraction R d).i s) twoTopFace, ?_⟩
  rw [twoTopStateProjection_top R d hd]
  exact LinearMap.congr_fun (contraction R d).p_i s

/-- The original rectangular coefficient boundary projects to the zero original state. -/
theorem twoTopStateProjection_boundary (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (x : TwoRectangleCoefficients R) :
    twoTopStateProjection R d (twoRectangleBoundary R (fun v => -(d v : ℤ)) x) = 0 := by
  obtain ⟨z,hz⟩ := twoRectangleComponents_surjective R x
  let s := -twoRectangleOrientation R
  have hs : s*s = 1 := by dsimp [s]; rw [neg_mul_neg,twoRectangleOrientation_sq]
  let c := (faceEquiv R).symm (s • z)
  have he : faceEquiv R ((contraction R d).d c) twoTopFace =
      twoRectangleBoundary R (fun v => -(d v : ℤ)) x := by
    rw [faceEquiv_d,cubicalCoefficientD_two_top]
    simp only [c,LinearEquiv.apply_symm_apply,map_smul,hz,smul_smul]
    change (s*s) • _ = _
    rw [hs,one_smul]
  rw [← he,twoTopStateProjection_top R d hd]
  exact LinearMap.congr_fun (contraction R d).p_d c

/-- A zero original top state gives a boundary through the original strong contraction, in every twist degree. -/
theorem twoTopStateProjection_zero_isBoundary (d : Fin 2 → ℕ) (x : FaceRing R twoTopFace)
    (hx : twoTopStateProjection R d x = 0) :
    ∃ y, twoRectangleBoundary R (fun v => -(d v : ℤ)) y = x := by
  have hp : (contraction R d).p (twoTopInsert R x) = 0 := hx
  have h := GradedContraction.ChainPairing.cycle_decomposition (twoTopInsert_closed R d x)
  rw [hp,map_zero,add_zero] at h
  have he := congrArg (fun c => faceEquiv R c twoTopFace) h
  rw [faceEquiv_twoTopInsert,Pi.single_eq_same,faceEquiv_d,cubicalCoefficientD_two_top] at he
  refine ⟨(-twoRectangleOrientation R) •
    twoRectangleComponents R (faceEquiv R ((contraction R d).h (twoTopInsert R x))), ?_⟩
  rw [map_smul]
  exact he.symm

/-- Every original top-face representative with zero state is a boundary of the original four restrictions. -/
theorem twoTopStateProjection_eq_zero_iff (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v)
    (x : FaceRing R twoTopFace) :
    twoTopStateProjection R d x = 0 ↔
      ∃ y, twoRectangleBoundary R (fun v => -(d v : ℤ)) y = x := by
  constructor
  · exact twoTopStateProjection_zero_isBoundary R d x
  · rintro ⟨y,rfl⟩
    exact twoTopStateProjection_boundary R d hd y

/-- The actual original boundary image is exactly the original state-projection kernel. -/
theorem twoRectangleBoundary_range (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    LinearMap.range (twoRectangleBoundary R (fun v => -(d v : ℤ))) =
      LinearMap.ker (twoTopStateProjection R d) := by
  ext x
  exact (twoTopStateProjection_eq_zero_iff R d hd x).symm

/-- The specified original rectangular coefficient quotient is the original state module for negative twists. -/
noncomputable def twoRectangleStateEquiv (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) :
    (FaceRing R twoTopFace ⧸ LinearMap.range (twoRectangleBoundary R (fun v => -(d v : ℤ)))) ≃ₗ[R]
      H R d :=
  (Submodule.quotEquivOfEq _ _ (twoRectangleBoundary_range R d hd)).trans
    ((twoTopStateProjection R d).quotKerEquivOfSurjective (twoTopStateProjection_surjective R d hd))

/-- Every original coefficient representative maps to its original state projection. -/
theorem twoRectangleStateEquiv_mk (d : Fin 2 → ℕ) (hd : ∀ v, 0 < d v) (x : FaceRing R twoTopFace) :
    twoRectangleStateEquiv R d hd (Submodule.Quotient.mk x) = twoTopStateProjection R d x := rfl

end BPFixedPoints.CechProduct
