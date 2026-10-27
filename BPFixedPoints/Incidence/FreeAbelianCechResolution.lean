/-
Portions adapted from openai/math, FreeCechResolution.lean,
commit 1581d4cbdd69a0faf34b2089614fe2a814316a6a, under Apache 2.0.
See THIRD_PARTY_NOTICES.md and LICENSE-APACHE-2.0.
Changes: use underlying abelian sheaves, narrow the imports, and retain
the original alternating-face differential and objectwise evaluations.
-/
import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Positive exactness of the original free abelian tuple Čech complex

The tuple indices include repetitions. This is the ordinary tuple Čech
resolution, not the finite cubical model. Positive exactness does not require
a cover; degree-zero augmented exactness remains a separate cover condition.
-/

namespace BPFixedPoints.SheafTools.FreeCech
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
universe u

/-- The original simplicial set of all vertex tuples, including repeated vertices. -/
def tupleSimplex (V : Type u) : SimplicialObject (Type u) where
  obj n := ToType n.unop → V
  map f := ↾fun t => t ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The canonical augmentation to one point. -/
def tupleAugmented (V : Type u) : SimplicialObject.Augmented (Type u) :=
  (tupleSimplex V).augmentOfIsTerminal Types.isTerminalPUnit

/-- Inserting an original vertex supplies the standard extra degeneracy. -/
def tupleExtraDegeneracy {V : Type u} (p : V) :
    (tupleAugmented V).ExtraDegeneracy where
  s' := ↾fun _ _ => p
  s n := ↾fun t => Fin.cons p t
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext t
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    ext t
    funext i
    rfl
  s_comp_δ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n+3) → V) (i.succ.succAbove j.succ) = t (i.succAbove j)
      simp only [Fin.succ_succAbove_succ]
      rfl
  s_comp_σ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n+2) → V) (i.succ.predAbove j.succ) = t (i.predAbove j)
      simp only [Fin.succ_predAbove_succ]
      rfl

/-- The free abelian complex with the original alternating-face differential. -/
noncomputable def freeTupleComplex (V : Type u) : ChainComplex AddCommGrpCat.{u} ℕ :=
  AlternatingFaceMapComplex.obj (tupleSimplex V ⋙ AddCommGrpCat.free)

/-- Positive exactness also holds for an empty vertex set, where every term is zero. -/
theorem freeTupleComplex_exact (V : Type u) (q : ℕ) :
    (freeTupleComplex V).ExactAt (q+1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    letI : IsEmpty (Fin (q+2) → V) := ⟨fun t => isEmptyElim (t 0)⟩
    change ((freeTupleComplex V).sc (q+1)).Exact
    apply ShortComplex.exact_of_isZero_X₂
    exact AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (FreeAbelianGroup (Fin (q+2) → V)))
  | inr h =>
    let p : V := Classical.choice h
    let e := ((tupleExtraDegeneracy p).map AddCommGrpCat.free).homotopyEquiv
    apply (exactAt_iff_of_quasiIsoAt e.hom (q+1)).2
    exact HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 _ (q+1) (by omega)

variable {C : Type u} [Category.{u} C]

/-- Tuples of vertices form a presheaf with the original vertex restrictions. -/
def tuplePresheaf (V : Cᵒᵖ ⥤ Type u) : SimplicialObject (Cᵒᵖ ⥤ Type u) where
  obj n :=
    { obj W := ToType n.unop → V.obj W
      map f := ↾fun t i => V.map f (t i)
      map_id W := by ext t i; simp
      map_comp f g := by ext t i; simp }
  map f := { app W := ↾fun t => t ∘ f.unop.toOrderHom }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The original free abelian presheaf complex. -/
noncomputable def freePresheafComplex (V : Cᵒᵖ ⥤ Type u) :
    ChainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ℕ :=
  AlternatingFaceMapComplex.obj
    (tuplePresheaf V ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)

/-- Evaluation keeps precisely the original free tuple complex and its differential. -/
theorem evaluation_freePresheafComplex (V : Cᵒᵖ ⥤ Type u) (W : Cᵒᵖ) :
    (((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj W).mapHomologicalComplex _).obj
      (freePresheafComplex V) = freeTupleComplex (V.obj W) := by
  change ((alternatingFaceMapComplex _ ⋙
    ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj W).mapHomologicalComplex _).obj _) = _
  rw [map_alternatingFaceMapComplex]
  rfl

/-- Objectwise extra degeneracies prove positive exactness of the original presheaf complex. -/
theorem freePresheafComplex_exact (V : Cᵒᵖ ⥤ Type u) (q : ℕ) :
    (freePresheafComplex V).ExactAt (q+1) := by
  change ((freePresheafComplex V).sc (q+1)).Exact
  rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext W
  have h := freeTupleComplex_exact (V.obj W) q
  rw [← evaluation_freePresheafComplex V W] at h
  exact (IsZero.of_iso h.isZero_homology
    (((freePresheafComplex V).sc (q+1)).mapHomologyIso
      ((evaluation Cᵒᵖ AddCommGrpCat.{u}).obj W)).symm).eq_of_src _ _

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{u}]

/-- Sheafification is taken in the same underlying abelian sheaf category as actual sheaf Ext. -/
noncomputable def freeSheafComplex (V : Cᵒᵖ ⥤ Type u) :
    ChainComplex (Sheaf J AddCommGrpCat.{u}) ℕ :=
  ((presheafToSheaf J AddCommGrpCat.{u}).mapHomologicalComplex _).obj (freePresheafComplex V)

/-- Exact sheafification preserves positive exactness of the original free abelian complex. -/
theorem freeSheafComplex_exact (V : Cᵒᵖ ⥤ Type u) (q : ℕ) :
    (freeSheafComplex J V).ExactAt (q+1) := by
  change (((freePresheafComplex V).sc (q+1)).map (presheafToSheaf J AddCommGrpCat.{u})).Exact
  exact (freePresheafComplex_exact V q).map _

end BPFixedPoints.SheafTools.FreeCech
