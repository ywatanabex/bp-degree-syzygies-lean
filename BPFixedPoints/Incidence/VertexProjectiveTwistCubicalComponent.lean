import BPFixedPoints.Incidence.VertexProjectiveTwistCubicalSections
import BPFixedPoints.Incidence.BinaryCoverCellEndpoint

/-! # Each component of the original actual cubical differential

The independently defined full differential is evaluated at an arbitrary
original face. Exactly its original endpoint faces contribute, with the
original tensor prefix sign and actual restriction maps.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CechProduct CechCubicalCell SheafTools.BinaryCells
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1400000
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- An original face step determines its original source once the active endpoint is specified. -/
theorem faceStep_source {p q : V → Fin 3} (v : V) (h : faceStep q v = p) :
    q = Function.update p v (q v) := by
  rw [← h,faceStep,Function.update_idem,Function.update_eq_self]

private theorem single_restriction_at (a : V → ℤ) (p q r : V → Fin 3) (he : q = r)
    (hpq : FaceRefines p q) (hpr : FaceRefines p r) (c : R)
    (x : vertexTwistCubicalFace R V a p) :
    (Pi.single q (c • vertexTwistCubicalRestriction R V a hpq x) : VertexTwistCubicalSections R V a) r =
      c • vertexTwistCubicalRestriction R V a hpr x := by
  subst r
  rw [Pi.single_eq_same]

/-- The original endpoint edge contributes its original actual restriction with exactly its original boundary coefficient. -/
theorem vertexTwistCubicalEdge_endpoint (a : V → ℤ) (p : V → Fin 3) (v : V)
    (hp : p v = 2) (k : Fin 2) (x : VertexTwistCubicalSections R V a) :
    vertexTwistCubicalEdge R V a (Function.update p v k.castSucc) v x p =
      ((-1 : R)^faceBoundaryPrefix p v * (if k = 0 then 1 else -1)) •
        vertexTwistCubicalRestriction R V a
          (endpoint_refines (faceRefines_refl p) v hp k.castSucc)
          (x (Function.update p v k.castSucc)) := by
  rw [vertexTwistCubicalEdge,ite_eq_right (by simpa only [Function.update_self] using endpoint_ne_overlap k)]
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,LinearMap.single_apply,LinearMap.proj_apply]
  rw [← Pi.single_smul]
  rw [single_restriction_at R V a _ _ _ (endpoint_faceStep p v hp k)]
  rw [native_endpoint_boundary_sign R]

/-- At any original face, the full independently specified differential is exactly the original endpoint restriction sum. -/
theorem vertexTwistCubicalD_component (a : V → ℤ) (x : VertexTwistCubicalSections R V a)
    (p : V → Fin 3) :
    vertexTwistCubicalD R V a x p =
      ∑ v, if hp : p v = 2 then
        (-1 : R)^faceBoundaryPrefix p v •
          (vertexTwistCubicalRestriction R V a
              (endpoint_refines (faceRefines_refl p) v hp (0 : Fin 3))
              (x (Function.update p v 0)) -
            vertexTwistCubicalRestriction R V a
              (endpoint_refines (faceRefines_refl p) v hp (1 : Fin 3))
              (x (Function.update p v 1)))
        else 0 := by
  simp only [vertexTwistCubicalD,LinearMap.sum_apply,Finset.sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hp : p v = 2
  · rw [dite_eq_left hp]
    have hne : Function.update p v (0 : Fin 3) ≠ Function.update p v 1 := by
      intro he
      have hh := congrFun he v
      exact (by decide : (0 : Fin 3) ≠ 1) (by simpa only [Function.update_self] using hh)
    rw [← Finset.sum_subset (Finset.subset_univ
      ({Function.update p v 0,Function.update p v 1} : Finset (V → Fin 3))) ?_]
    · rw [Finset.sum_pair hne]
      have h₀ := vertexTwistCubicalEdge_endpoint R V a p v hp 0 x
      have h₁ := vertexTwistCubicalEdge_endpoint R V a p v hp 1 x
      change vertexTwistCubicalEdge R V a (Function.update p v 0) v x p = _ at h₀
      change vertexTwistCubicalEdge R V a (Function.update p v 1) v x p = _ at h₁
      rw [h₀,h₁]
      simp only [show (1 : Fin 2) ≠ 0 from by decide,ite_true,ite_false,
        mul_one,mul_neg_one,neg_smul,smul_sub,sub_eq_add_neg,smul_add,smul_neg]
      rfl
    · intro q _ hq
      by_cases hv : q v = 2
      · simp [vertexTwistCubicalEdge,hv]
      · simp only [vertexTwistCubicalEdge,hv,ite_false,LinearMap.smul_apply,
          LinearMap.comp_apply,LinearMap.single_apply,LinearMap.proj_apply,Pi.smul_apply]
        rw [Pi.single_eq_of_ne,smul_zero]
        intro he
        have hs := faceStep_source (V := V) v he.symm
        have hk : q v = 0 ∨ q v = 1 := by omega
        rcases hk with hk | hk
        · apply hq
          exact Finset.mem_insert.mpr (Or.inl (by simpa only [hk] using hs))
        · apply hq
          exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by simpa only [hk] using hs)))
  · rw [dite_eq_right hp]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hv : q v = 2
    · simp [vertexTwistCubicalEdge,hv]
    · simp only [vertexTwistCubicalEdge,hv,ite_false,LinearMap.smul_apply,
        LinearMap.comp_apply,LinearMap.single_apply,LinearMap.proj_apply,Pi.smul_apply]
      rw [Pi.single_eq_of_ne,smul_zero]
      intro he
      have hh := congrFun he v
      exact hp (by simpa only [faceStep,Function.update_self] using hh)

end BPFixedPoints.ProjectiveLine
