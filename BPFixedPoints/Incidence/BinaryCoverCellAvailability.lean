import BPFixedPoints.Incidence.CechCubicalCellComplex
import BPFixedPoints.Incidence.SheafCohomologyBinaryCover

/-! # Original cubical cells available on an actual open

On an actual open W, available cells are either empty or precisely the
subfaces of the original maximal available rectangular face. This retains
the original binary-cover opens and supplies local cell primitives even
when no original chart contains W. Empty opens are not excluded.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory TopologicalSpace CechProduct CechCubicalCell Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1300000
variable {T : Type} [TopologicalSpace T] {V : Type}
variable (U : V → Fin 2 → Opens T) (W : Opens T)

/-- Each direction has an original endpoint open containing the actual open W. -/
def HasVertex : Prop := ∀ v, ∃ b, W ≤ U v b

/-- The maximal original cell whose open contains W, when a vertex is available. -/
noncomputable def maximalFace : V → Fin 3 := by
  classical
  exact fun v => if W ≤ U v 0 ∧ W ≤ U v 1 then 2 else if W ≤ U v 0 then 0 else 1

/-- A specified original vertex of the maximal available cell. -/
noncomputable def baseVertex : V → Fin 2 := by
  classical
  exact fun v => if W ≤ U v 0 then 0 else 1

/-- Actual cell availability is exactly original face refinement, including all overlap coordinates. -/
theorem available_iff_refines (hv : HasVertex U W) (q : V → Fin 3) :
    W ≤ binaryCoverFaceOpen U q ↔ FaceRefines q (maximalFace U W) := by
  have hf (v : V) (k : Fin 3) : W ≤ binaryCoverFaceFactor (U v) k ↔
      k = maximalFace U W v ∨ maximalFace U W v = 2 := by
    classical
    by_cases hL : W ≤ U v 0
    · by_cases hR : W ≤ U v 1
      · fin_cases k <;> simp [maximalFace,binaryCoverFaceFactor,hL,hR,le_inf_iff]
      · fin_cases k <;> simp [maximalFace,binaryCoverFaceFactor,hL,hR,le_inf_iff]
    · have hR : W ≤ U v 1 := by
        obtain ⟨b,hb⟩ := hv v
        fin_cases b
        · exact (hL hb).elim
        · exact hb
      fin_cases k <;> simp [maximalFace,binaryCoverFaceFactor,hL,hR,le_inf_iff]
  constructor
  · intro h v
    exact (hf v (q v)).mp (h.trans (iInf_le _ v))
  · intro h
    exact le_iInf fun v => (hf v (q v)).mpr (h v)

/-- The specified original base vertex is actually inside the maximal available cell. -/
theorem baseVertex_refines (hv : HasVertex U W) :
    FaceRefines (fun v => (baseVertex U W v).castSucc) (maximalFace U W) := by
  intro v
  classical
  by_cases hL : W ≤ U v 0
  · by_cases hR : W ≤ U v 1 <;> simp [baseVertex,maximalFace,hL,hR]
  · have hR : W ≤ U v 1 := by
      obtain ⟨b,hb⟩ := hv v
      fin_cases b
      · exact (hL hb).elim
      · exact hb
    simp [baseVertex,maximalFace,hL,hR]

/-- Every original available cell supplies an original vertex on W. -/
theorem hasVertex_of_cell (q : V → Fin 3) (hq : W ≤ binaryCoverFaceOpen U q) : HasVertex U W := by
  intro v
  have hf : W ≤ binaryCoverFaceFactor (U v) (q v) := hq.trans (iInf_le _ v)
  generalize he : q v = k at hf
  fin_cases k
  · exact ⟨0,by simpa [binaryCoverFaceFactor] using hf⟩
  · exact ⟨1,by simpa [binaryCoverFaceFactor] using hf⟩
  · exact ⟨0,(by simpa [binaryCoverFaceFactor] using hf : W ≤ U v 0 ⊓ U v 1).trans inf_le_left⟩

/-- Free original cells whose original actual opens contain W. -/
noncomputable def available (R : Type*) [CommRing R] : Submodule R (Cells R V) :=
  supported R R {q | W ≤ binaryCoverFaceOpen U q}

/-- Whenever a vertex is available, the original available cells are exactly one original face's subcells. -/
theorem available_eq_subfaces (R : Type*) [CommRing R] (hv : HasVertex U W) :
    available U W R = subfaces R (maximalFace U W) := by
  unfold available subfaces
  congr 1
  ext q
  exact available_iff_refines U W hv q

/-- If no original vertex is available, every original cell term is actually zero. -/
theorem available_eq_bot (R : Type*) [CommRing R] (hv : ¬HasVertex U W) :
    available U W R = ⊥ := by
  have he : {q | W ≤ binaryCoverFaceOpen U q} = (∅ : Set (V → Fin 3)) := by
    ext q
    exact iff_false_intro (fun hq => hv (hasVertex_of_cell U W q hq))
  rw [available,he,supported_empty]

variable (R : Type*) [CommRing R] [Fintype V] [DecidableEq V]

/-- The original boundary preserves exactly the original cells available on W. -/
theorem available_boundary (b : V → Fin 2) (x : Cells R V) (hx : x ∈ available U W R) :
    (CechCubicalCell.contraction R b).d x ∈ available U W R := by
  by_cases hv : HasVertex U W
  · rw [available_eq_subfaces U W R hv] at hx ⊢
    exact contraction_d_subfaces R b _ x hx
  · rw [available_eq_bot U W R hv] at hx ⊢
    have hx0 : x = 0 := hx
    rw [hx0,map_zero]
    exact Submodule.zero_mem _

/-- Every positive original cycle on an actual open has a primitive on the same actual open.
The original boundary is fixed independently of the locally selected prism basepoint. -/
theorem available_positive_primitive (n : ℕ) (hn : 0 < n) (x : Cells R V)
    (hx : x ∈ available U W R)
    (hdeg : x ∈ supported R R {q | cellDegree q = -(n : ℤ)})
    (hd : (CechCubicalCell.contraction R (fun _ : V => 0)).d x = 0) :
    ∃ z : Cells R V, z ∈ available U W R ∧
      z ∈ supported R R {q | cellDegree q = -((n+1 : ℕ) : ℤ)} ∧
        (CechCubicalCell.contraction R (fun _ : V => 0)).d z = x := by
  by_cases hv : HasVertex U W
  · have hx' : x ∈ subfaces R (maximalFace U W) := by rwa [← available_eq_subfaces U W R hv]
    have hd' : (CechCubicalCell.contraction R (baseVertex U W)).d x = 0 := by
      rwa [contraction_d_eq R (baseVertex U W) (fun _ => 0)]
    obtain ⟨hs,hg,he⟩ := contraction_positive_primitive_in_face R (baseVertex U W) (maximalFace U W)
      (baseVertex_refines U W hv) n hn x hx' hdeg hd'
    refine ⟨(CechCubicalCell.contraction R (baseVertex U W)).h x,?_,hg,?_⟩
    · rwa [available_eq_subfaces U W R hv]
    · rwa [contraction_d_eq R (fun _ => 0) (baseVertex U W)]
  · have hx0 : x = 0 := by simpa only [available_eq_bot U W R hv,Submodule.mem_bot] using hx
    subst x
    exact ⟨0,Submodule.zero_mem _,Submodule.zero_mem _,map_zero _⟩

end BPFixedPoints.SheafTools.BinaryCells
