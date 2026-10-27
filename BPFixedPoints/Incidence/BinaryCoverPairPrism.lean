import BPFixedPoints.Incidence.CechCubicalPairSubface
import BPFixedPoints.Incidence.BinaryCoverCellDiagonal

/-! # The original tensor prism preserves actual pair availability and total degree -/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory TopologicalSpace Opposite Finsupp CechProduct CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000
noncomputable section
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type*) [CommRing R]

@[reducible] local instance pairedPrismChainsAddCommGroup (W : Opens T) (n : ℕ) : AddCommGroup (pairedChains U R W n) :=
  (pairedChains U R W n).addCommGroup
@[reducible] local instance pairedPrismChainsModule (W : Opens T) (n : ℕ) : Module R (pairedChains U R W n) :=
  (pairedChains U R W n).module

/-- The original summed pair overlap dimension is precisely the existing tensor cochain degree. -/
theorem pairedChains_degree (W : Opens T) (n : ℕ) (x : pairedChains U R W n) :
    x.val ∈ supported R R {z | pairCellDegree V z=-(n : ℤ)} := by
  intro z hz
  have h := (x.property hz).2.2
  change -(faceDegree z.1 : ℤ) + -(faceDegree z.2 : ℤ)=-(n : ℤ)
  omega

/-- Original available pairs are subface pairs of the same original maximal available rectangular face. -/
theorem pairedChains_subfaces (W : Opens T) (hv : HasVertex U W) (n : ℕ) (x : pairedChains U R W n) :
    x.val ∈ pairSubfaces R (maximalFace U W) := by
  intro z hz
  have h := x.property hz
  exact ⟨(available_iff_refines U W hv z.1).mp h.1,(available_iff_refines U W hv z.2).mp h.2.1⟩

/-- If no original vertex is available, every original tensor pair chain is zero. -/
theorem pairedChains_zero_of_noVertex (W : Opens T) (hv : ¬ HasVertex U W) (n : ℕ)
    (x : pairedChains U R W n) : x=0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro z
  change x.val z=0
  by_contra hz
  exact hv (hasVertex_of_cell U W z.1 (x.property (Finsupp.mem_support_iff.mpr hz)).1)

/-- The original tensor prism retains both original available opens and raises the original total dimension once. -/
theorem pairedPrism_mem (W : Opens T) (n : ℕ) (x : pairedChains U R W n) :
    (pairContraction R V (baseVertex U W)).h x.val ∈ pairedChains U R W (n+1) := by
  by_cases hv : HasVertex U W
  · have hs := pairContraction_h_subfaces R (baseVertex U W) (maximalFace U W)
      (baseVertex_refines U W hv) x.val (pairedChains_subfaces U R W hv n x)
    have hd := (pairContraction_degrees R V (baseVertex U W)).h (-(n : ℤ)) x.val (pairedChains_degree U R W n x)
    intro z hz
    refine ⟨(available_iff_refines U W hv z.1).mpr (hs hz).1,
      (available_iff_refines U W hv z.2).mpr (hs hz).2,?_⟩
    have h := hd hz
    change -(faceDegree z.1 : ℤ) + -(faceDegree z.2 : ℤ)=-(n : ℤ)+(-1) at h
    omega
  · have hx : x.val=0 := congrArg Subtype.val (pairedChains_zero_of_noVertex U R W hv n x)
    rw [hx,map_zero]
    exact Submodule.zero_mem _

/-- The same original tensor prism restricted to the original available pair modules and original degrees. -/
def pairedPrism (W : Opens T) (n : ℕ) : pairedChains U R W n →ₗ[R] pairedChains U R W (n+1) :=
  (((pairContraction R V (baseVertex U W)).h).comp (pairedChains U R W n).subtype).codRestrict _
    (pairedPrism_mem U R W n)

/-- Every original positive available pair cycle has the original same-open tensor-prism primitive. -/
theorem pairedDifferential_prism_of_closed (W : Opens T) (n : ℕ) (x : pairedChains U R W (n+1))
    (hx : pairedDifferential U R W n x=0) :
    pairedDifferential U R W (n+1) (pairedPrism U R W (n+1) x)=x := by
  apply Subtype.ext
  have hd : pairBoundary R V x.val=0 := congrArg Subtype.val hx
  exact (pairContraction_positive_primitive R V (baseVertex U W) (n+1) (by omega) x.val
    (pairedChains_degree U R W (n+1) x) hd).2

/-- Positive exactness of the original tensor pair differential on every actual open. -/
theorem pairedDifferential_range_eq_ker (W : Opens T) (n : ℕ) :
    LinearMap.range (pairedDifferential U R W (n+1))=LinearMap.ker (pairedDifferential U R W n) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (pairedDifferential_square U R W n) y
  · intro hx
    exact ⟨pairedPrism U R W (n+1) x,pairedDifferential_prism_of_closed U R W n x hx⟩

end
end BPFixedPoints.SheafTools.BinaryCells
