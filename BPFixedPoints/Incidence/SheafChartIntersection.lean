import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Ring.Subring.Basic

/-! # Global sections as an intersection of chart images

This is a comparison theorem for an actual Mathlib sheaf of commutative rings.
The cover and injective restrictions to a common open are hypotheses; this file
does not construct the incidence scheme or identify its line-bundle cohomology.
-/

namespace BPFixedPoints.SheafTools

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u
variable {X : TopCat.{u}} (F : TopCat.Sheaf CommRingCat.{u} X)

/-- Actual restriction homomorphism of the given sheaf. -/
def sectionRestrict {A B : Opens X} (h : B ≤ A) :
    F.obj.obj (op A) →+* F.obj.obj (op B) :=
  (F.obj.map (homOfLE h).op).hom

/-- Functoriality of actual restrictions, evaluated on a section. -/
theorem sectionRestrict_comp {A B C : Opens X} (hBA : B ≤ A) (hCB : C ≤ B)
    (x : F.obj.obj (op A)) :
    (sectionRestrict F) hCB ((sectionRestrict F) hBA x) =
      (sectionRestrict F) (hCB.trans hBA) x := by
  change F.obj.map (homOfLE hCB).op (F.obj.map (homOfLE hBA).op x) = _
  rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

variable {ι : Type u} [Nonempty ι] (U : ι → Opens X) (W : Opens X)
  (hW : ∀ i, W ≤ U i)

/-- Intersection of the images of the actual chart restriction maps. -/
def chartImageIntersection : Subring (F.obj.obj (op W)) :=
  ⨅ i, ((sectionRestrict F) (hW i)).range

/-- Restriction of a global section lands in every chart image. -/
def globalToChartIntersection : F.obj.obj (op (⊤ : Opens X)) →+*
    (chartImageIntersection F) U W hW :=
  ((sectionRestrict F) (show W ≤ ⊤ from le_top)).codRestrict _ fun x => by
    rw [chartImageIntersection, Subring.mem_iInf]
    intro i
    refine ⟨(sectionRestrict F) (show U i ≤ ⊤ from le_top) x, ?_⟩
    exact (sectionRestrict_comp F) le_top (hW i) x

/-- A common-open value in all chart images gives a compatible family on the
actual pairwise intersections, provided restriction from each intersection is injective. -/
theorem compatible_of_common_value
    (hoverlap : ∀ i j, Function.Injective
      ((sectionRestrict F) (show W ≤ U i ⊓ U j from le_inf (hW i) (hW j))))
    (s : ∀ i, F.obj.obj (op (U i))) (x : F.obj.obj (op W))
    (hs : ∀ i, (sectionRestrict F) (hW i) (s i) = x) :
    TopCat.Presheaf.IsCompatible F.obj U s := by
  intro i j
  apply hoverlap i j
  change (sectionRestrict F) (le_inf (hW i) (hW j))
      ((sectionRestrict F) inf_le_left (s i)) =
    (sectionRestrict F) (le_inf (hW i) (hW j))
      ((sectionRestrict F) inf_le_right (s j))
  rw [(sectionRestrict_comp F), (sectionRestrict_comp F), hs i, hs j]

/-- Actual sheaf gluing gives surjectivity onto the intersection of chart images. -/
theorem globalToChartIntersection_surjective (hcover : (⊤ : Opens X) ≤ iSup U)
    (hoverlap : ∀ i j, Function.Injective
      ((sectionRestrict F) (show W ≤ U i ⊓ U j from le_inf (hW i) (hW j)))) :
    Function.Surjective ((globalToChartIntersection F) U W hW) := by
  intro x
  have hx : ∀ i, ∃ s : F.obj.obj (op (U i)), (sectionRestrict F) (hW i) s = x.val := by
    intro i
    exact (Subring.mem_iInf.mp x.property) i
  choose s hs using hx
  have hc := (compatible_of_common_value F) U W hW hoverlap s x.val hs
  obtain ⟨z, hz, _⟩ := F.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hcover s hc
  refine ⟨z, Subtype.ext ?_⟩
  let i : ι := Classical.choice inferInstance
  have hr := (sectionRestrict_comp F) (show U i ≤ ⊤ from le_top) (hW i) z
  change (sectionRestrict F) (show W ≤ ⊤ from le_top) z = x.val
  rw [← hr]
  exact (congrArg ((sectionRestrict F) (hW i)) (hz i)).trans (hs i)

/-- Injective chart restrictions and sheaf separatedness give injectivity. -/
theorem globalToChartIntersection_injective (hcover : (⊤ : Opens X) ≤ iSup U)
    (hchart : ∀ i, Function.Injective ((sectionRestrict F) (hW i))) :
    Function.Injective ((globalToChartIntersection F) U W hW) := by
  intro x y h
  apply F.eq_of_locally_eq' U ⊤ (fun _ => homOfLE le_top) hcover
  intro i
  apply hchart i
  change (sectionRestrict F) (hW i) ((sectionRestrict F) le_top x) =
    (sectionRestrict F) (hW i) ((sectionRestrict F) le_top y)
  rw [(sectionRestrict_comp F), (sectionRestrict_comp F)]
  exact congrArg Subtype.val h

/-- Global sections of the given sheaf are the chart-image intersection.
All maps are actual sheaf restrictions and the inverse is supplied by gluing. -/
noncomputable def globalSectionsEquivChartIntersection
    (hcover : (⊤ : Opens X) ≤ iSup U)
    (hchart : ∀ i, Function.Injective ((sectionRestrict F) (hW i)))
    (hoverlap : ∀ i j, Function.Injective
      ((sectionRestrict F) (show W ≤ U i ⊓ U j from le_inf (hW i) (hW j)))) :
    F.obj.obj (op (⊤ : Opens X)) ≃+* (chartImageIntersection F) U W hW :=
  RingEquiv.ofBijective ((globalToChartIntersection F) U W hW)
    ⟨(globalToChartIntersection_injective F) U W hW hcover hchart,
      (globalToChartIntersection_surjective F) U W hW hcover hoverlap⟩

end BPFixedPoints.SheafTools
