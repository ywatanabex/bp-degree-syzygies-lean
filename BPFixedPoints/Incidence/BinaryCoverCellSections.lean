import BPFixedPoints.Incidence.BinaryCoverCellFree
import BPFixedPoints.Incidence.SheafLocalCohomologyZero

/-! # Hom from the original cell sheaf terms is actual original face sections

The original free-cell generators, native free-abelian adjunction, Yoneda
and sheafification adjunction identify the original terms with their actual
face-section functors. No state action or cohomology comparison is used.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp CechCubicalCell
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)

/-- An original face is available on its own original open. -/
def canonicalCell {n : ℕ} (q : FaceIndex (V := V) n) :
    (cellIndices U n).obj (op (binaryCoverFaceOpen U q.val)) :=
  ⟨q.val,le_rfl,q.property⟩

/-- The original cell index presheaf corepresents actual sections on the original face opens. -/
def cellNatEquiv (F : (Opens T)ᵒᵖ ⥤ Type) (n : ℕ) :
    (cellIndices U n ⟶ F) ≃
      (∀ q : FaceIndex (V := V) n, F.obj (op (binaryCoverFaceOpen U q.val))) where
  toFun a q := a.app _ (canonicalCell U q)
  invFun s :=
    { app W := ↾fun q => F.map (homOfLE q.property.1).op (s ⟨q.val,q.property.2⟩)
      naturality W Z f := by
        ext q
        exact F.map_comp_apply (homOfLE q.property.1).op f (s ⟨q.val,q.property.2⟩) }
  left_inv a := by
    ext W q
    let p : FaceIndex (V := V) n := ⟨q.val,q.property.2⟩
    let h : W.unop ≤ binaryCoverFaceOpen U p.val := q.property.1
    have he : (cellIndices U n).map (homOfLE h).op (canonicalCell U p) = q := Subtype.ext rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalCell U p)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext q
    change F.map (𝟙 (op (binaryCoverFaceOpen U q.val))) (s q) = s q
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- The original actual cell sheaf term. -/
noncomputable abbrev sheafTerm (n : ℕ) := (sheafComplex U).X n

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Hom from the original term is the actual original degreewise face-section family, additively. -/
noncomputable def sectionsEquiv (n : ℕ) : (sheafTerm U n ⟶ F) ≃+
    (∀ q : FaceIndex (V := V) n, F.obj.obj (op (binaryCoverFaceOpen U q.val))) where
  toEquiv := ((sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F).trans
    (((freeCellPresheafIso U n).symm.homCongr (Iso.refl F.obj)).trans
      (((AddCommGrpCat.adj.whiskerRight (Opens T)ᵒᵖ).homEquiv _ F.obj).trans
        (cellNatEquiv U (F.obj ⋙ forget AddCommGrpCat) n)))
  map_add' f g := by funext q; rfl

/-- The original Yoneda embedding of one original cell on its original face open. -/
def cellEmbedding {n : ℕ} (q : FaceIndex (V := V) n) :
    yoneda.obj (binaryCoverFaceOpen U q.val) ⟶ cellIndices U n :=
  yonedaEquiv.symm (canonicalCell U q)

/-- The original represented free-open generator of the original cell presheaf term. -/
noncomputable def presheafGenerator {n : ℕ} (q : FaceIndex (V := V) n) :
    (yoneda.obj (binaryCoverFaceOpen U q.val) ⋙ AddCommGrpCat.free) ⟶ presheafTerm U n :=
  ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (cellEmbedding U q) ≫
    (freeCellPresheafIso U n).hom

/-- Each original represented generator is the same original cell with coefficient one on every original open. -/
theorem presheafGenerator_app_of_val {n : ℕ} (q : FaceIndex (V := V) n) (W : Opens T)
    (i : W ⟶ binaryCoverFaceOpen U q.val) :
    let x : chains U ℤ W n := (presheafGenerator U q).app (op W) (FreeAbelianGroup.of i)
    x.val = single q.val 1 := by
  change (chainFreeEquiv U W n (FreeAbelianGroup.map _ (FreeAbelianGroup.of i))).val = _
  rw [FreeAbelianGroup.map_of_apply,chainFreeEquiv_of_val]
  rfl

/-- The actual original free-open generator after the original sheafification. -/
noncomputable def generator {n : ℕ} (q : FaceIndex (V := V) n) :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (binaryCoverFaceOpen U q.val) ⋙ AddCommGrpCat.free) ⟶ sheafTerm U n :=
  (presheafToSheaf _ AddCommGrpCat).map (presheafGenerator U q)

/-- Every original section coordinate is evaluation on its specified original free-open generator. -/
theorem sectionsEquiv_apply (n : ℕ) (f : sheafTerm U n ⟶ F) (q : FaceIndex (V := V) n) :
    sectionsEquiv U F n f q =
      freeSheafSectionsEquiv F (binaryCoverFaceOpen U q.val) (generator U q ≫ f) := by
  let g := (sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F f
  change ((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj
    ((freeCellPresheafIso U n).hom ≫ g)).app _ (canonicalCell U q) = _
  symm
  have hs := congrArg (fun a => yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) a))
    ((sheafificationAdjunction _ AddCommGrpCat).homEquiv_naturality_left (presheafGenerator U q) f)
  have hf := congrArg yonedaEquiv
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv_naturality_left (cellEmbedding U q)
      ((freeCellPresheafIso U n).hom ≫ g))
  exact hs.trans (hf.trans (yonedaEquiv_comp (cellEmbedding U q)
    (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) ((freeCellPresheafIso U n).hom ≫ g))))

end BPFixedPoints.SheafTools.BinaryCells
