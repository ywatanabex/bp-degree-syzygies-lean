import BPFixedPoints.Incidence.BinaryCoverRefinementComplex
import BPFixedPoints.Incidence.VertexPermutationCellChain
import BPFixedPoints.Incidence.AcyclicResolutionAugmentedSourceNaturality

/-!
# Face sections of relabelled cochains

For binary covers `C : K → Fin 2 → Opens T` and `U : I → Fin 2 → Opens T` and an injective map
`ι : I → K` with `C (ι i) b ≤ U i b`, the forgetful chain map `relabelSheafComplex C U hι hC`
(`BinaryCoverRefinementComplex`) sends the universal section of a face `q` of `K` to the signed
universal section of the restricted face `q ∘ ι` (`relabelFace`), and to zero when an overlap
direction of `q` lies outside the image of `ι` (`presheafGenerator_relabel`).

Proved here:
* the face sections of a relabelled cochain (`sectionsEquiv_relabel`): the sign
  `relabelCoefficient ℤ ι q` times the restricted face section of the cochain at `q ∘ ι`;
* the augmented Yoneda class of a relabelled cocycle is the class of the cocycle
  (`relabel_cocycleComparison`), since the forgetful chain map preserves the augmentation.

Nothing here involves schemes, twists or states.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite Finsupp
open SheafTools SheafTools.BinaryCells ExtResolutionTools CechCubicalCell

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1600000

section Relabel

variable {T : Type} [TopologicalSpace T] {I K : Type} [Fintype I] [DecidableEq I] [Fintype K]
  [DecidableEq K] (C : K → Fin 2 → Opens T) (U : I → Fin 2 → Opens T) {ι : I → K}
  (hι : Function.Injective ι) (hC : ∀ i b, C (ι i) b ≤ U i b)

/-- The restricted face of a face whose overlap directions lie in the image of `ι`, with the same
cell degree. -/
def relabelFace {n : ℕ} (q : FaceIndex (V := K) n) (h : ∀ k, q.val k = 2 → ∃ a, ι a = k) :
    FaceIndex (V := I) n :=
  ⟨q.val ∘ ι, by
    have hq := q.property
    dsimp only [cellDegree] at hq ⊢
    rw [faceDegree_comp_of_image ι hι q.val h]
    exact hq⟩

@[simp] theorem relabelFace_val {n : ℕ} (q : FaceIndex (V := K) n)
    (h : ∀ k, q.val k = 2 → ∃ a, ι a = k) : (relabelFace hι q h).val = q.val ∘ ι := rfl

/-- The forgetful map of cell presheaves on one free-open generator: the signed generator of the
restricted face, or zero when an overlap direction lies outside the image. -/
theorem presheafGenerator_relabel {n : ℕ} (q : FaceIndex (V := K) n) :
    presheafGenerator C q ≫ (toAbelianPresheaf (T := T)).map (relabelPresheaf C U hι hC ℤ n) =
      if h : ∀ k, q.val k = 2 → ∃ a, ι a = k then
        relabelCoefficient ℤ ι q.val •
          (freeOpenPresheafMap (binaryCoverFaceOpen_relabel_le C U hC q.val) ≫
            presheafGenerator U (relabelFace hι q h))
      else 0 := by
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro i
  apply Subtype.ext
  change coefficientEvaluation U n _ W.unop i
      (presheafGenerator C q ≫ (toAbelianPresheaf (T := T)).map (relabelPresheaf C U hι hC ℤ n)) =
    coefficientEvaluation U n _ W.unop i _
  have hl : coefficientEvaluation U n _ W.unop i
      (presheafGenerator C q ≫ (toAbelianPresheaf (T := T)).map (relabelPresheaf C U hι hC ℤ n)) =
        relabelCells ℤ ι (single q.val 1) := by
    change relabelCells ℤ ι ((presheafGenerator C q).app (op W.unop)
      (FreeAbelianGroup.of i) : chains C ℤ W.unop n).val = _
    rw [presheafGenerator_app_of_val]
  rw [hl, relabelCells_single, one_mul]
  by_cases h : ∀ k, q.val k = 2 → ∃ a, ι a = k
  · rw [dite_eq_left h]
    have hr := coefficientEvaluation_generator U (relabelFace hι q h) _ W.unop i
      (binaryCoverFaceOpen_relabel_le C U hC q.val)
    have hs := map_zsmul (coefficientEvaluation U n (binaryCoverFaceOpen C q.val) W.unop i)
      (relabelCoefficient ℤ ι q.val)
      (freeOpenPresheafMap (binaryCoverFaceOpen_relabel_le C U hC q.val) ≫
        presheafGenerator U (relabelFace hι q h))
    rw [hr, smul_single, smul_eq_mul, mul_one] at hs
    exact hs.symm
  · rw [dite_eq_right h, map_zero, relabelCoefficient, ite_eq_right h, single_zero]

/-- **Face sections of a relabelled cochain.** The face sections of the forgetful chain map
followed by a cochain of `U` are the signed restricted face sections of the cochain, and zero on
faces with an overlap direction outside the image. -/
theorem sectionsEquiv_relabel (n : ℕ) (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (y : sheafTerm U n ⟶ F) (q : FaceIndex (V := K) n) :
    sectionsEquiv C F n ((relabelSheafComplex C U hι hC).f n ≫ y) q =
      if h : ∀ k, q.val k = 2 → ∃ a, ι a = k then
        relabelCoefficient ℤ ι q.val •
          F.obj.map (homOfLE (binaryCoverFaceOpen_relabel_le C U hC q.val)).op
            (sectionsEquiv U F n y (relabelFace hι q h))
      else 0 := by
  rw [sectionsEquiv_apply, ← Category.assoc]
  have hg : generator C q ≫ (relabelSheafComplex C U hι hC).f n =
      (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).map
        (presheafGenerator C q ≫ (toAbelianPresheaf (T := T)).map (relabelPresheaf C U hι hC ℤ n)) := by
    rw [relabelSheafComplex_f, generator, ← Functor.map_comp]
  rw [hg, presheafGenerator_relabel]
  by_cases h : ∀ k, q.val k = 2 → ∃ a, ι a = k
  · rw [dite_eq_left h, dite_eq_left h, Functor.map_zsmul, Preadditive.zsmul_comp, map_zsmul,
      Functor.map_comp, Category.assoc]
    congr 1
    dsimp only [freeOpenPresheafMap]
    rw [freeSheafSectionsEquiv_naturality, sectionsEquiv_apply]
    rfl
  · rw [dite_eq_right h, dite_eq_right h, Functor.map_zero, zero_comp, map_zero]

/-- **Classes along the forgetful chain map.** The augmented Yoneda class of a cocycle of `U`
pulled back along the forgetful chain map is the class of the cocycle. -/
theorem relabel_cocycleComparison [HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})]
    (hcC : (⊤ : Opens T) ≤ ⨆ b, chartOpen C b) (hcU : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ)
    (w : (cubicalTower U).cycles F n) :
    letI := augmentation_epi C hcC
    letI := augmentation_epi U hcU
    augmentedComplexCocycleComparison (sheafComplex C) F (sheafComplex_exact C) (augmentation C)
        (augmentation_zero C) (augmentation_exact C) n
        ((complexSourceMap (relabelSheafComplex C U hι hC) (sheafComplex_exact C)
          (sheafComplex_exact U)).cycles F n w) =
      augmentedComplexCocycleComparison (sheafComplex U) F (sheafComplex_exact U) (augmentation U)
        (augmentation_zero U) (augmentation_exact U) n w := by
  let _ := augmentation_epi C hcC
  let _ := augmentation_epi U hcU
  rw [augmentedComplexCocycleComparison_source F (sheafComplex_exact C) (augmentation C)
    (augmentation_zero C) (augmentation_exact C) (relabelSheafComplex C U hι hC)
    (sheafComplex_exact U) (augmentation U) (augmentation_zero U) (augmentation_exact U) (𝟙 _)
    (by rw [relabelSheafComplex_augmentation, Category.comp_id]) n w]
  exact Ext.mk₀_id_comp _

end Relabel

end BPFixedPoints.Multigraph
