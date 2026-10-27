import BPFixedPoints.Incidence.BinaryCoverCellSections

/-! # Original endpoint faces, dimensions and actual open inclusions

Each original overlap cell has the two original endpoint faces one dimension
lower. Their actual open inclusions are the original binary-cover inclusions.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory TopologicalSpace Opposite Finsupp CechCubicalCell CechProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1200000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- Original face refinement is the original reverse inclusion of actual opens. -/
theorem faceOpen_refinement_le {q p : V → Fin 3} (h : FaceRefines q p) :
    binaryCoverFaceOpen U p ≤ binaryCoverFaceOpen U q := by
  apply le_iInf
  intro v
  refine (iInf_le (fun w => binaryCoverFaceFactor (U w) (p w)) v).trans ?_
  rcases h v with hv | hp
  · rw [hv]
  · rw [hp]
    generalize he : q v = k
    fin_cases k <;> simp [binaryCoverFaceFactor]

/-- An original endpoint is distinct from the original overlap cell. -/
theorem endpoint_ne_overlap (k : Fin 2) : k.castSucc ≠ (2 : Fin 3) := by
  fin_cases k <;> decide

/-- Replacing one original overlap by an endpoint lowers exactly the original overlap dimension. -/
theorem faceDegree_endpoint (p : V → Fin 3) (v : V) (hp : p v = 2) (k : Fin 2) :
    faceDegree (Function.update p v k.castSucc)+1 = faceDegree p := by
  have he : (∑ w ∈ Finset.univ.erase v, if Function.update p v k.castSucc w = 2 then 1 else 0 : ℕ) =
      ∑ w ∈ Finset.univ.erase v, if p w = 2 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw)]
  have h₀ := Finset.sum_erase_add (s := Finset.univ)
    (fun w => if p w = 2 then (1 : ℕ) else 0) (Finset.mem_univ v)
  have h₁ := Finset.sum_erase_add (s := Finset.univ)
    (fun w => if Function.update p v k.castSucc w = 2 then (1 : ℕ) else 0) (Finset.mem_univ v)
  simp only [Function.update_self,endpoint_ne_overlap,ite_false,add_zero,he] at h₁
  change (∑ w, if Function.update p v k.castSucc w = 2 then (1 : ℕ) else 0)+1 =
    ∑ w, if p w = 2 then (1 : ℕ) else 0
  rw [← h₁]
  simpa only [hp,ite_true] using h₀

/-- The original indexed endpoint face with its proved original lower dimension. -/
def endpoint {n : ℕ} (q : FaceIndex (V := V) (n+1)) (v : V) (hv : q.val v = 2) (k : Fin 2) :
    FaceIndex (V := V) n :=
  ⟨Function.update q.val v k.castSucc,by
    have he := faceDegree_endpoint q.val v hv k
    have hq := q.property
    dsimp only [cellDegree] at hq ⊢
    omega⟩

/-- The original overlap open is contained in each original endpoint open. -/
theorem endpointOpenLE {n : ℕ} (q : FaceIndex (V := V) (n+1)) (v : V)
    (hv : q.val v = 2) (k : Fin 2) :
    binaryCoverFaceOpen U q.val ≤ binaryCoverFaceOpen U (endpoint q v hv k).val :=
  faceOpen_refinement_le U (endpoint_refines (faceRefines_refl q.val) v hv k.castSucc)

/-- The original represented free-open map for an original actual open inclusion. -/
noncomputable def freeOpenPresheafMap {A B : Opens T} (h : A ≤ B) :
    (yoneda.obj A ⋙ AddCommGrpCat.free) ⟶ (yoneda.obj B ⋙ AddCommGrpCat.free) :=
  ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (yoneda.map (homOfLE h))

end BPFixedPoints.SheafTools.BinaryCells
