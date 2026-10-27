import BPFixedPoints.Incidence.BinaryCoverCellSections
import BPFixedPoints.Incidence.AcyclicResolutionComplex

/-! # Actual Ext acyclicity of the original cubical cell sheaf terms

The specified original free-open generators exhibit the original term as
their finite biproduct. Mathlib's native Ext biproduct equivalence retains
each original generator on every local Ext coordinate.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000
attribute [local instance] Abelian.hasFiniteBiproducts
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T)
noncomputable local instance cellTermHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
noncomputable local instance faceIndexFintype (n : ℕ) : Fintype (FaceIndex (V := V) n) := by
  classical
  unfold FaceIndex
  infer_instance

/-- The original free abelian sheaf at an original degree-n face. -/
noncomputable abbrev faceFreeOpen (n : ℕ) (q : FaceIndex (V := V) n) :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
    (yoneda.obj (binaryCoverFaceOpen U q.val) ⋙ AddCommGrpCat.free)

/-- The finite biproduct map consists of the original specified free-open generators. -/
noncomputable def termBiproductMap (n : ℕ) : (⨁ (faceFreeOpen U n)) ⟶ sheafTerm U n :=
  biproduct.desc (fun q => generator U q)

/-- The original generators give an actual finite-biproduct presentation of the original sheaf term. -/
theorem termBiproductMap_isIso (n : ℕ) : IsIso (termBiproductMap U n) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  constructor
  · intro f g he
    apply (sectionsEquiv U F n).injective
    funext q
    rw [sectionsEquiv_apply,sectionsEquiv_apply]
    congr 1
    have hh := congrArg (fun k => biproduct.ι (faceFreeOpen U n) q ≫ k) he
    simpa only [termBiproductMap,biproduct.ι_desc_assoc] using hh
  · intro g
    let f := (sectionsEquiv U F n).symm
      (fun q => freeSheafSectionsEquiv F (binaryCoverFaceOpen U q.val) (biproduct.ι (faceFreeOpen U n) q ≫ g))
    refine ⟨f,?_⟩
    apply biproduct.hom_ext'
    intro q
    rw [termBiproductMap,biproduct.ι_desc_assoc]
    apply (freeSheafSectionsEquiv F (binaryCoverFaceOpen U q.val)).injective
    rw [← sectionsEquiv_apply]
    exact congrFun ((sectionsEquiv U F n).apply_symm_apply _) q

/-- The specified finite-biproduct isomorphism retains all original generators. -/
noncomputable def termBiproductIso (n : ℕ) : (⨁ (faceFreeOpen U n)) ≅ sheafTerm U n := by
  letI := termBiproductMap_isIso U n
  exact asIso (termBiproductMap U n)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Actual Ext of the original term is the actual local Ext family on the original faces. -/
noncomputable def termExtEquiv (n k : ℕ) :
    Ext.{1} (sheafTerm U n) F k ≃+
      (∀ q : FaceIndex (V := V) n, F.H' k (binaryCoverFaceOpen U q.val)) :=
  ((((extFunctor k).mapIso (termBiproductIso U n).op).app F).addCommGroupIsoToAddEquiv).trans
    (Ext.biproductAddEquiv (biproduct.isBilimit (faceFreeOpen U n)) F k)

/-- Every actual local Ext coordinate is restriction along its originally specified generator. -/
theorem termExtEquiv_apply (n k : ℕ) (x : Ext.{1} (sheafTerm U n) F k) (q : FaceIndex (V := V) n) :
    termExtEquiv U F n k x q = (Ext.mk₀ (generator U q)).comp x (zero_add k) := by
  change (Ext.mk₀ (biproduct.ι (faceFreeOpen U n) q)).comp
    ((Ext.mk₀ (termBiproductMap U n)).comp x (zero_add k)) (zero_add k) = _
  rw [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,termBiproductMap,biproduct.ι_desc]

/-- Actual local vanishing supplies actual relative acyclicity of the original cell sheaf complex terms. -/
theorem sheafComplex_acyclic
    (h : ∀ (n : ℕ) (q : FaceIndex (V := V) n) (k : ℕ)
      (x : F.H' (k+1) (binaryCoverFaceOpen U q.val)), x = 0) :
    ExtResolutionTools.ComplexAcyclicAgainst (sheafComplex U) F := by
  intro n k x
  apply (termExtEquiv U F n (k+1)).injective
  ext q
  exact (h n q k _).trans (by simp)

end BPFixedPoints.SheafTools.BinaryCells
