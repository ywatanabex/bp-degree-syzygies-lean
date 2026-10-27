import BPFixedPoints.Incidence.CechTwoRectangleBoundary

/-! # Specified rectangular top differential and the original enumeration sign -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
variable (R : Type) [CommRing R]

/-- The original two-face decomposition with no change of vertex labels. -/
def twoFacePairEquiv : (Fin 2 → Fin 3) ≃ Fin 3 × Fin 3 where
  toFun q := (q 0,q 1)
  invFun p := ![p.1,p.2]
  left_inv q := by funext v; fin_cases v <;> rfl
  right_inv p := by cases p; rfl

private theorem sum_two_faces {M : Type*} [AddCommMonoid M] (f : (Fin 2 → Fin 3) → M) :
    ∑ q, f q = ∑ b : Fin 3, ∑ c : Fin 3, f ![b,c] := by
  calc
    _ = ∑ p : Fin 3 × Fin 3, f ![p.1,p.2] :=
      Fintype.sum_equiv twoFacePairEquiv _ _ (fun q => congrArg f (twoFacePairEquiv.symm_apply_apply q).symm)
    _ = _ := Fintype.sum_prod_type _

@[simp] theorem faceStep_two_zero (b c : Fin 3) : faceStep ![b,c] 0 = ![2,c] := by
  funext v
  fin_cases v <;> simp [faceStep]

@[simp] theorem faceStep_two_one (b c : Fin 3) : faceStep ![b,c] 1 = ![b,2] := by
  funext v
  fin_cases v <;> simp [faceStep]

/-- The original enumeration contributes this specified orientation to the coordinate order 0,1. -/
noncomputable def twoRectangleOrientation : R :=
  if Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0 then -1 else 1

/-- The orientation is invertible even over the zero ring and in characteristic two. -/
theorem twoRectangleOrientation_sq : twoRectangleOrientation R * twoRectangleOrientation R = 1 := by
  unfold twoRectangleOrientation
  split_ifs <;> simp

/-- Extract the four original one-overlap components. -/
noncomputable def twoRectangleComponents :
    ((q : Fin 2 → Fin 3) → FaceRing R q) →ₗ[R] TwoRectangleCoefficients R :=
  ((LinearMap.proj ![0,2]).prod (LinearMap.proj ![1,2])).prod
    ((LinearMap.proj ![2,0]).prod (LinearMap.proj ![2,1]))

/-- Arbitrary coefficients on the four original one-overlap faces extend to a full coefficient family. -/
theorem twoRectangleComponents_surjective : Function.Surjective (twoRectangleComponents R) := by
  intro x
  refine ⟨Pi.single (![0,2] : Fin 2 → Fin 3) x.1.1 + Pi.single ![1,2] x.1.2 +
    Pi.single ![2,0] x.2.1 + Pi.single ![2,1] x.2.2, ?_⟩
  ext <;> simp [twoRectangleComponents,Pi.single_apply,funext_iff,Fin.forall_fin_two]

private theorem edge_same (a : Fin 2 → ℤ) (q : Fin 2 → Fin 3) (v : Fin 2)
    (r : Fin 2 → Fin 3) (hv : q v ≠ 2) (ht : faceStep q v = r)
    (x : (q : Fin 2 → Fin 3) → FaceRing R q) :
    cubicalCoefficientEdge R a q v x r = faceBoundarySign R q v •
      multiTwistFaceRestriction R (by rw [← ht]; exact faceStep_refines q v) a (x q) := by
  subst r
  rw [cubicalCoefficientEdge,ite_eq_right hv]
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.single_apply,
    LinearMap.proj_apply,Pi.smul_apply,Pi.single_eq_same]

private theorem edge_ne (a : Fin 2 → ℤ) (q : Fin 2 → Fin 3) (v : Fin 2)
    (r : Fin 2 → Fin 3) (ht : r ≠ faceStep q v)
    (x : (q : Fin 2 → Fin 3) → FaceRing R q) : cubicalCoefficientEdge R a q v x r = 0 := by
  by_cases hv : q v = 2
  · simp only [cubicalCoefficientEdge,ite_eq_left hv,LinearMap.zero_apply,Pi.zero_apply]
  · rw [cubicalCoefficientEdge,ite_eq_right hv]
    change faceBoundarySign R q v • (Pi.single (faceStep q v)
      (multiTwistFaceRestriction R (faceStep_refines q v) a (x q)) r) = 0
    rw [Pi.single_eq_of_ne ht,smul_zero]

private theorem edge_two_zero (a : Fin 2 → ℤ) (b c : Fin 3)
    (x : (q : Fin 2 → Fin 3) → FaceRing R q) :
    cubicalCoefficientEdge R a ![b,c] 0 x twoTopFace =
      if b = 2 then 0 else if c = 2 then faceBoundarySign R ![b,c] 0 •
        multiTwistFaceRestriction R (twoFaceRefinesTop ![b,c]) a (x ![b,c]) else 0 := by
  by_cases hb : b = 2
  · have hv : (![b,c] : Fin 2 → Fin 3) 0 = 2 := hb
    rw [ite_eq_left hb,cubicalCoefficientEdge,ite_eq_left hv]
    rfl
  · rw [ite_eq_right hb]
    by_cases hc : c = 2
    · subst c
      rw [ite_eq_left rfl]
      exact edge_same R a ![b,2] 0 twoTopFace hb (faceStep_two_zero b 2) x
    · rw [ite_eq_right hc]
      apply edge_ne
      intro he
      have hh := congrFun he 1
      rw [faceStep_two_zero] at hh
      exact hc hh.symm

private theorem edge_two_one (a : Fin 2 → ℤ) (b c : Fin 3)
    (x : (q : Fin 2 → Fin 3) → FaceRing R q) :
    cubicalCoefficientEdge R a ![b,c] 1 x twoTopFace =
      if c = 2 then 0 else if b = 2 then faceBoundarySign R ![b,c] 1 •
        multiTwistFaceRestriction R (twoFaceRefinesTop ![b,c]) a (x ![b,c]) else 0 := by
  by_cases hc : c = 2
  · have hv : (![b,c] : Fin 2 → Fin 3) 1 = 2 := hc
    rw [ite_eq_left hc,cubicalCoefficientEdge,ite_eq_left hv]
    rfl
  · rw [ite_eq_right hc]
    by_cases hb : b = 2
    · subst b
      rw [ite_eq_left rfl]
      exact edge_same R a ![2,c] 1 twoTopFace hc (faceStep_two_one 2 c) x
    · rw [ite_eq_right hb]
      apply edge_ne
      intro he
      have hh := congrFun he 0
      rw [faceStep_two_one] at hh
      exact hb hh.symm

private theorem prefix_two_zero (b : Fin 3) : faceBoundaryPrefix (![b,2] : Fin 2 → Fin 3) 0 =
    if Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0 then 1 else 0 := by
  unfold faceBoundaryPrefix
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp

private theorem prefix_two_one (c : Fin 3) : faceBoundaryPrefix (![2,c] : Fin 2 → Fin 3) 1 =
    if Fintype.equivFin (Fin 2) 0 < Fintype.equivFin (Fin 2) 1 then 1 else 0 := by
  unfold faceBoundaryPrefix
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ,Fin.sum_univ_zero]
  simp

/-- The original full coefficient differential has precisely the specified rectangular top boundary and orientation. -/
theorem cubicalCoefficientD_two_top (a : Fin 2 → ℤ)
    (x : (q : Fin 2 → Fin 3) → FaceRing R q) :
    cubicalCoefficientD R a x twoTopFace =
      (-twoRectangleOrientation R) • twoRectangleBoundary R a (twoRectangleComponents R x) := by
  have hne : Fintype.equivFin (Fin 2) 0 ≠ Fintype.equivFin (Fin 2) 1 :=
    (Fintype.equivFin (Fin 2)).injective.ne (by decide)
  have hrev : (Fintype.equivFin (Fin 2) 0 < Fintype.equivFin (Fin 2) 1) ↔
      ¬ Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0 := by omega
  simp only [cubicalCoefficientD,LinearMap.sum_apply,Finset.sum_apply]
  rw [sum_two_faces]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  dsimp only [Fin.succ_zero_eq_one,Fin.succ_one_eq_two]
  simp only [edge_two_zero,edge_two_one]
  simp only [faceBoundarySign,prefix_two_zero,prefix_two_one]
  by_cases hor : Fintype.equivFin (Fin 2) 1 < Fintype.equivFin (Fin 2) 0
  all_goals
    simp [twoRectangleBoundary,twoRectangleComponents,twoRectangleOrientation,hor,hrev,smul_sub]
    abel

end BPFixedPoints.CechProduct
