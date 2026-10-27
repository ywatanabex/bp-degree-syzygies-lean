/-
Portions adapted from openai/math, FreeCechSections.lean,
commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, under Apache 2.0.
See THIRD_PARTY_NOTICES.md and LICENSE-APACHE-2.0.
Changes: work in the original abelian sheaf category and compare with actual
sections, retaining the alternating restrictions and their original signs.
-/
import BPFixedPoints.Incidence.FreeAbelianCechResolution
import BPFixedPoints.Incidence.SheafLocalCohomologyZero

/-! # The original free abelian Čech differential is the actual restriction sum

This compares all tuple cochains, with repetitions, to morphisms out of the
original free abelian complex. The comparison preserves each actual section,
each face restriction, and every alternating sign.
-/

namespace BPFixedPoints.SheafTools.FreeCech
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open scoped Simplicial BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {T : Type} [TopologicalSpace T] {ι : Type} (U : ι → Opens T)

/-- A vertex is available on precisely the opens contained in its original cover member. -/
def coverVertices : (Opens T)ᵒᵖ ⥤ Type where
  obj W := {i : ι // W.unop ≤ U i}
  map f := ↾fun i => ⟨i.val,(leOfHom f.unop).trans i.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The actual open attached to an original tuple. -/
abbrev intersection {q : ℕ} (t : Fin (q+1) → ι) : Opens T := ⨅ i, U (t i)

/-- The canonical tuple is defined on its actual intersection. -/
def canonicalTuple {q : ℕ} (t : Fin (q+1) → ι) :
    ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).obj (op (intersection U t)) :=
  fun i => ⟨t i,iInf_le (fun j => U (t j)) i⟩

/-- The tuple presheaf corepresents the original tuple-indexed sections. -/
def tupleNatEquiv (F : (Opens T)ᵒᵖ ⥤ Type) (q : ℕ) :
    (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)) ⟶ F) ≃
      (∀ t : Fin (q+1) → ι, F.obj (op (intersection U t))) where
  toFun a t := a.app _ (canonicalTuple U t)
  invFun s :=
    { app W := ↾fun v =>
        F.map (homOfLE (le_iInf fun i => (v i).property)).op (s (fun i => (v i).val))
      naturality W V f := by
        ext v
        let t : Fin (q+1) → ι := fun i => (v i).val
        let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
        exact F.map_comp_apply (homOfLE h).op f (s t) }
  left_inv a := by
    ext W v
    let t : Fin (q+1) → ι := fun i => (v i).val
    let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
    have he : (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).map
        (homOfLE h).op) (canonicalTuple U t) = v := by
      funext i
      apply Subtype.ext
      rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalTuple U t)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext t
    change F.map (𝟙 (op (intersection U t))) (s t) = s t
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- The term of the original sheafified free tuple complex. -/
noncomputable abbrev freeTerm (q : ℕ) : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0} :=
  (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).X q

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Original Hom cochains are the actual tuple intersection sections, additively. -/
noncomputable def sectionsEquiv (q : ℕ) : (freeTerm U q ⟶ F) ≃+
    (∀ t : Fin (q+1) → ι, F.obj.obj (op (intersection U t))) where
  toEquiv := ((sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F).trans
    (((AddCommGrpCat.adj.whiskerRight (Opens T)ᵒᵖ).homEquiv _ F.obj).trans
      (tupleNatEquiv U (F.obj ⋙ forget AddCommGrpCat) q))
  map_add' _ _ := rfl

/-- The original tuple is the Yoneda generator at its original intersection. -/
def tupleEmbedding {q : ℕ} (t : Fin (q+1) → ι) :
    yoneda.obj (intersection U t) ⟶ (tuplePresheaf (coverVertices U)).obj (op ⦋q⦌) :=
  yonedaEquiv.symm (canonicalTuple U t)

/-- The original represented free-open generator of the original free term. -/
noncomputable def generator {q : ℕ} (t : Fin (q+1) → ι) :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (intersection U t) ⋙ AddCommGrpCat.free) ⟶ freeTerm U q :=
  (presheafToSheaf _ AddCommGrpCat).map
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (tupleEmbedding U t))

/-- Every tuple coordinate is evaluation of its original represented generator. -/
theorem sectionsEquiv_apply (q : ℕ) (f : freeTerm U q ⟶ F) (t : Fin (q+1) → ι) :
    sectionsEquiv U F q f t = freeSheafSectionsEquiv F (intersection U t) (generator U t ≫ f) := by
  let g := (sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F f
  change ((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj g).app _ (canonicalTuple U t) = _
  symm
  have hs := congrArg (fun a => yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) a))
    ((sheafificationAdjunction _ AddCommGrpCat).homEquiv_naturality_left
      (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (tupleEmbedding U t)) f)
  have hf := congrArg yonedaEquiv
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv_naturality_left (tupleEmbedding U t) g)
  exact hs.trans (hf.trans (yonedaEquiv_comp (tupleEmbedding U t)
    (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) g)))

/-- Deleting a tuple entry enlarges its actual intersection. -/
theorem faceLE {q : ℕ} (t : Fin (q+2) → ι) (k : Fin (q+2)) :
    intersection U t ≤ intersection U (t ∘ k.succAbove) :=
  le_iInf fun i => iInf_le (fun j => U (t j)) (k.succAbove i)

/-- The original tuple face restricts along precisely the original intersection inclusion. -/
theorem tupleEmbedding_face {q : ℕ} (t : Fin (q+2) → ι) (k : Fin (q+2)) :
    tupleEmbedding U t ≫ (tuplePresheaf (coverVertices U)).δ k =
      yoneda.map (homOfLE (faceLE U t k)) ≫ tupleEmbedding U (t ∘ k.succAbove) := by
  ext W v
  funext i
  apply Subtype.ext
  rfl

/-- The original sheafified face map. -/
noncomputable def freeFace (q : ℕ) (k : Fin (q+2)) : freeTerm U (q+1) ⟶ freeTerm U q :=
  (presheafToSheaf _ AddCommGrpCat).map
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
      ((tuplePresheaf (coverVertices U)).δ k))

/-- The original free-open generator keeps the original face restriction. -/
theorem generator_face {q : ℕ} (t : Fin (q+2) → ι) (k : Fin (q+2)) :
    generator U t ≫ freeFace U q k =
      (presheafToSheaf _ AddCommGrpCat).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (yoneda.map (homOfLE (faceLE U t k)))) ≫ generator U (t ∘ k.succAbove) := by
  let G := (Functor.whiskeringRight (Opens T)ᵒᵖ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat
  change G.map (tupleEmbedding U t) ≫ G.map ((tuplePresheaf (coverVertices U)).δ k) =
    G.map (yoneda.map (homOfLE (faceLE U t k))) ≫ G.map (tupleEmbedding U (t ∘ k.succAbove))
  rw [← G.map_comp, tupleEmbedding_face, G.map_comp]

/-- The actual differential retains the original alternating signs on all faces. -/
theorem boundary_eq_sum (q : ℕ) :
    (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d (q+1) q =
      ∑ k : Fin (q+2), (-1 : ℤ)^k.val • freeFace U q k := by
  dsimp only [freeSheafComplex, Functor.mapHomologicalComplex_obj_d, freePresheafComplex]
  rw [AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Functor.map_zsmul]
  rfl

/-- The original differential on Hom cochains is exactly the actual signed restriction sum. -/
theorem sectionsEquiv_boundary (q : ℕ) (f : freeTerm U q ⟶ F) (t : Fin (q+2) → ι) :
    sectionsEquiv U F (q+1)
      ((freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)).d (q+1) q ≫ f) t =
      ∑ k : Fin (q+2), (-1 : ℤ)^k.val •
        F.obj.map (homOfLE (faceLE U t k)).op (sectionsEquiv U F q f (t ∘ k.succAbove)) := by
  rw [sectionsEquiv_apply, boundary_eq_sum, Preadditive.sum_comp, Preadditive.comp_sum,
    map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, map_zsmul, ← Category.assoc,
    generator_face, Category.assoc,
    freeSheafSectionsEquiv_naturality, sectionsEquiv_apply]

end BPFixedPoints.SheafTools.FreeCech
