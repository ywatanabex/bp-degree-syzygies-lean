import BPFixedPoints.Incidence.BinaryCoverPairFree
import BPFixedPoints.Incidence.SheafLocalCohomologyZero

/-! # Hom from the original cell sheaf terms is actual original face sections

The original free-cell pairedGenerators, native free-abelian adjunction, Yoneda
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
def canonicalPairCell {n : ℕ} (q : PairFaceIndex (V := V) n) :
    (pairedCellIndices U n).obj (op (pairedFaceOpen U q.val)) :=
  ⟨q.val,inf_le_left,inf_le_right,q.property⟩

/-- The original cell index presheaf corepresents actual sections on the original face opens. -/
def pairedCellNatEquiv (F : (Opens T)ᵒᵖ ⥤ Type) (n : ℕ) :
    (pairedCellIndices U n ⟶ F) ≃
      (∀ q : PairFaceIndex (V := V) n, F.obj (op (pairedFaceOpen U q.val))) where
  toFun a q := a.app _ (canonicalPairCell U q)
  invFun s :=
    { app W := ↾fun q => F.map (homOfLE (le_inf q.property.1 q.property.2.1)).op (s ⟨q.val,q.property.2.2⟩)
      naturality W Z f := by
        ext q
        exact F.map_comp_apply (homOfLE (le_inf q.property.1 q.property.2.1)).op f (s ⟨q.val,q.property.2.2⟩) }
  left_inv a := by
    ext W q
    let p : PairFaceIndex (V := V) n := ⟨q.val,q.property.2.2⟩
    let h : W.unop ≤ pairedFaceOpen U p.val := le_inf q.property.1 q.property.2.1
    have he : (pairedCellIndices U n).map (homOfLE h).op (canonicalPairCell U p) = q := Subtype.ext rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalPairCell U p)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext q
    change F.map (𝟙 (op (pairedFaceOpen U q.val))) (s q) = s q
    rw [CategoryTheory.Functor.map_id]
    rfl

/-- The original actual cell sheaf term. -/
noncomputable abbrev pairedSheafTerm (n : ℕ) := (pairedSheafComplex U).X n

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Hom from the original term is the actual original degreewise face-section family, additively. -/
noncomputable def pairedSectionsEquiv (n : ℕ) : (pairedSheafTerm U n ⟶ F) ≃+
    (∀ q : PairFaceIndex (V := V) n, F.obj.obj (op (pairedFaceOpen U q.val))) where
  toEquiv := ((sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F).trans
    (((freePairPresheafIso U n).symm.homCongr (Iso.refl F.obj)).trans
      (((AddCommGrpCat.adj.whiskerRight (Opens T)ᵒᵖ).homEquiv _ F.obj).trans
        (pairedCellNatEquiv U (F.obj ⋙ forget AddCommGrpCat) n)))
  map_add' f g := by funext q; rfl

/-- The original Yoneda embedding of one original cell on its original face open. -/
def pairedCellEmbedding {n : ℕ} (q : PairFaceIndex (V := V) n) :
    yoneda.obj (pairedFaceOpen U q.val) ⟶ pairedCellIndices U n :=
  yonedaEquiv.symm (canonicalPairCell U q)

/-- The original represented free-open generator of the original cell presheaf term. -/
noncomputable def pairedPresheafGenerator {n : ℕ} (q : PairFaceIndex (V := V) n) :
    (yoneda.obj (pairedFaceOpen U q.val) ⋙ AddCommGrpCat.free) ⟶ pairedPresheafTerm U n :=
  ((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (pairedCellEmbedding U q) ≫
    (freePairPresheafIso U n).hom

/-- Each original represented generator is the same original cell with coefficient one on every original open. -/
theorem pairedPresheafGenerator_app_of_val {n : ℕ} (q : PairFaceIndex (V := V) n) (W : Opens T)
    (i : W ⟶ pairedFaceOpen U q.val) :
    let x : pairedChains U ℤ W n := (pairedPresheafGenerator U q).app (op W) (FreeAbelianGroup.of i)
    x.val = single q.val 1 := by
  change (pairedChainFreeEquiv U W n (FreeAbelianGroup.map _ (FreeAbelianGroup.of i))).val = _
  rw [FreeAbelianGroup.map_of_apply,pairedChainFreeEquiv_of_val]
  rfl

/-- The actual original free-open generator after the original sheafification. -/
noncomputable def pairedGenerator {n : ℕ} (q : PairFaceIndex (V := V) n) :
    (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
      (yoneda.obj (pairedFaceOpen U q.val) ⋙ AddCommGrpCat.free) ⟶ pairedSheafTerm U n :=
  (presheafToSheaf _ AddCommGrpCat).map (pairedPresheafGenerator U q)

/-- Every original section coordinate is evaluation on its specified original free-open generator. -/
theorem pairedSectionsEquiv_apply (n : ℕ) (f : pairedSheafTerm U n ⟶ F) (q : PairFaceIndex (V := V) n) :
    pairedSectionsEquiv U F n f q =
      freeSheafSectionsEquiv F (pairedFaceOpen U q.val) (pairedGenerator U q ≫ f) := by
  let g := (sheafificationAdjunction _ AddCommGrpCat).homEquiv _ F f
  change ((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj
    ((freePairPresheafIso U n).hom ≫ g)).app _ (canonicalPairCell U q) = _
  symm
  have hs := congrArg (fun a => yonedaEquiv
      (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) a))
    ((sheafificationAdjunction _ AddCommGrpCat).homEquiv_naturality_left (pairedPresheafGenerator U q) f)
  have hf := congrArg yonedaEquiv
    ((AddCommGrpCat.adj.whiskerRight _).homEquiv_naturality_left (pairedCellEmbedding U q)
      ((freePairPresheafIso U n).hom ≫ g))
  exact hs.trans (hf.trans (yonedaEquiv_comp (pairedCellEmbedding U q)
    (((AddCommGrpCat.adj.whiskerRight _).homEquiv _ F.obj) ((freePairPresheafIso U n).hom ≫ g))))

end BPFixedPoints.SheafTools.BinaryCells
