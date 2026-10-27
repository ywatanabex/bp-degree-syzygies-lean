import BPFixedPoints.Incidence.FreeAbelianCechSections
import BPFixedPoints.Incidence.SheafTerminalCohomology
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # The original augmentation of the free-open Čech complex

The augmentation maps each original tuple generator to its original inclusion
in the terminal free-open sheaf. Degree-zero cocycles retain the original
sections on individual cover members.
-/

namespace BPFixedPoints.SheafTools.FreeCech
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open scoped Simplicial BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000
variable {T : Type} [TopologicalSpace T] {ι : Type} (U : ι → Opens T)

/-- The original tuple forgets to the unique terminal-open section. -/
def tupleToTop (q : ℕ) : (tuplePresheaf (coverVertices U)).obj (op ⦋q⦌) ⟶
    yoneda.obj (⊤ : Opens T) where
  app W := ↾fun _ => homOfLE le_top

/-- The original augmentation on each tuple degree before taking the alternating sum. -/
noncomputable def augmentationAt (q : ℕ) : freeTerm U q ⟶
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) :=
  (presheafToSheaf _ AddCommGrpCat).map
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (tupleToTop U q))

/-- Every original generator retains the original inclusion in the terminal open. -/
theorem augmentation_generator {q : ℕ} (t : Fin (q+1) → ι) :
    generator U t ≫ augmentationAt U q =
      (presheafToSheaf _ AddCommGrpCat).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (yoneda.map (homOfLE (show intersection U t ≤ ⊤ from le_top)))) := by
  let G := (Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat
  change G.map (tupleEmbedding U t) ≫ G.map (tupleToTop U q) = G.map _
  rw [← G.map_comp]
  congr 1

/-- Every original face has the same original terminal augmentation. -/
theorem freeFace_augmentation (q : ℕ) (k : Fin (q+2)) :
    freeFace U q k ≫ augmentationAt U q = augmentationAt U (q+1) := by
  let G := (Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat
  change G.map ((tuplePresheaf (coverVertices U)).δ k) ≫ G.map (tupleToTop U q) = G.map _
  rw [← G.map_comp]
  rfl

/-- The original degree-one alternating differential is killed by the original augmentation. -/
theorem augmentation_zero :
    (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d 1 0 ≫
      augmentationAt U 0 = 0 := by
  rw [boundary_eq_sum, Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one, neg_smul,
    one_zsmul, ← sub_eq_add_neg, Preadditive.sub_comp, freeFace_augmentation, sub_self]

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- The actual singleton-tuple intersection is its original cover member. -/
theorem singletonIntersection (i : ι) : intersection U (fun _ : Fin 1 => i) = U i := by
  simp [intersection]

/-- Degree-zero original Hom cochains are precisely the original individual-open sections. -/
noncomputable def zeroSectionsEquiv : (freeTerm U 0 ⟶ F) ≃+ (∀ i, F.obj.obj (op (U i))) where
  toFun f i := F.obj.map (eqToHom (singletonIntersection U i).symm).op
    (sectionsEquiv U F 0 f (fun _ => i))
  invFun s := (sectionsEquiv U F 0).symm
    (fun t => F.obj.map (homOfLE (iInf_le (fun j => U (t j)) 0)).op (s (t 0)))
  left_inv f := by
    apply (sectionsEquiv U F 0).injective
    funext t
    obtain ⟨i, rfl⟩ : ∃ i, t = fun _ => i :=
      ⟨t 0, by funext j; fin_cases j; rfl⟩
    rw [(sectionsEquiv U F 0).apply_symm_apply]
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    change F.obj.map (𝟙 _) _ = _
    simp
  right_inv s := by
    funext i
    dsimp only
    rw [(sectionsEquiv U F 0).apply_symm_apply]
    rw [← ConcreteCategory.comp_apply, ← F.obj.map_comp]
    change F.obj.map (𝟙 _) _ = _
    simp
  map_add' f g := by
    funext i
    change F.obj.map _ (sectionsEquiv U F 0 (f+g) _) = _
    simp only [map_add, Pi.add_apply]

/-- Every original singleton-tuple section is the restriction of its original cover-member value. -/
theorem sectionsEquiv_zero (f : freeTerm U 0 ⟶ F) (t : Fin 1 → ι) :
    sectionsEquiv U F 0 f t =
      F.obj.map (homOfLE (iInf_le (fun j => U (t j)) 0)).op (zeroSectionsEquiv U F f (t 0)) := by
  have hh := congrArg (fun z => sectionsEquiv U F 0 z t) ((zeroSectionsEquiv U F).symm_apply_apply f)
  exact hh.symm.trans (congrFun ((sectionsEquiv U F 0).apply_symm_apply _) t)

/-- The original augmentation induces exactly the actual individual restrictions of the original global section. -/
theorem zeroSectionsEquiv_augmentation
    (g : (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶ F) (i : ι) :
    zeroSectionsEquiv U F (augmentationAt U 0 ≫ g) i =
      F.obj.map (homOfLE (show U i ≤ ⊤ from le_top)).op (freeSheafSectionsEquiv F ⊤ g) := by
  change F.obj.map _ (sectionsEquiv U F 0 (augmentationAt U 0 ≫ g) _) = _
  rw [sectionsEquiv_apply, ← Category.assoc, augmentation_generator, freeSheafSectionsEquiv_naturality,
    ← ConcreteCategory.comp_apply, ← F.obj.map_comp]
  rfl

/-- The original degree-zero cocycle equation is the actual pairwise sheaf matching condition. -/
theorem zeroSectionsEquiv_compatible (f : freeTerm U 0 ⟶ F)
    (hf : (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d 1 0 ≫ f = 0) :
    TopCat.Presheaf.IsCompatible (X := TopCat.of T) F.obj U (zeroSectionsEquiv U F f) := by
  intro i j
  have hh := congrArg (fun z => sectionsEquiv U F 1 z ![i,j]) hf
  rw [sectionsEquiv_boundary] at hh
  rw [map_zero, Pi.zero_apply, Fin.sum_univ_two] at hh
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_one, pow_one,
    neg_smul, one_zsmul, ← sub_eq_add_neg] at hh
  have he := sub_eq_zero.mp hh
  rw [sectionsEquiv_zero,sectionsEquiv_zero] at he
  have hp : U i ⊓ U j ≤ intersection U ![i,j] := by
    apply le_iInf
    intro k
    fin_cases k
    · exact inf_le_left
    · exact inf_le_right
  have hr := congrArg (fun s => F.obj.map (homOfLE hp).op s) he
  simp only [← ConcreteCategory.comp_apply, ← F.obj.map_comp] at hr
  exact hr.symm

/-- The actual sheaf gluing property is the original augmentation's cokernel universal property. -/
theorem augmentation_factor (hcover : (⊤ : Opens T) ≤ ⨆ i, U i)
    (f : freeTerm U 0 ⟶ F)
    (hf : (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d 1 0 ≫ f = 0) :
    ∃! g : (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (⊤ : Opens T) ⋙ AddCommGrpCat.free) ⟶ F,
      augmentationAt U 0 ≫ g = f := by
  obtain ⟨s,hs,hu⟩ := TopCat.Sheaf.existsUnique_gluing' (X := TopCat.of T) F U ⊤
    (fun _ => homOfLE le_top) hcover (zeroSectionsEquiv U F f) (zeroSectionsEquiv_compatible U F f hf)
  refine ⟨(freeSheafSectionsEquiv F ⊤).symm s, ?_, ?_⟩
  · apply (zeroSectionsEquiv U F).injective
    funext i
    rw [zeroSectionsEquiv_augmentation, AddEquiv.apply_symm_apply]
    exact hs i
  · intro m hm
    apply (freeSheafSectionsEquiv F ⊤).injective
    rw [AddEquiv.apply_symm_apply]
    apply hu
    intro i
    rw [← zeroSectionsEquiv_augmentation,hm]

/-- The specified original augmentation is a native cokernel of the original differential. -/
noncomputable def augmentationIsCokernel (hcover : (⊤ : Opens T) ≤ ⨆ i, U i) :
    IsColimit (CokernelCofork.ofπ (augmentationAt U 0) (augmentation_zero U)) :=
  CokernelCofork.IsColimit.ofπ _ _
    (fun {_} f hf => Classical.choose (augmentation_factor U _ hcover f hf))
    (fun {_} f hf => (Classical.choose_spec (augmentation_factor U _ hcover f hf)).1)
    (fun {_} f hf m hm => (Classical.choose_spec (augmentation_factor U _ hcover f hf)).2 m hm)

/-- Covering is exactly what supplies the previously separate augmentation epimorphism. -/
theorem augmentation_epi (hcover : (⊤ : Opens T) ≤ ⨆ i, U i) : Epi (augmentationAt U 0) :=
  Cofork.IsColimit.epi (augmentationIsCokernel U hcover)

/-- The actual cover gives original augmented degree-zero exactness in the original abelian sheaf category. -/
theorem augmentation_exact (hcover : (⊤ : Opens T) ≤ ⨆ i, U i) :
    (ShortComplex.mk
      ((freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d 1 0)
      (augmentationAt U 0) (augmentation_zero U)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (augmentationIsCokernel U hcover)

end BPFixedPoints.SheafTools.FreeCech
