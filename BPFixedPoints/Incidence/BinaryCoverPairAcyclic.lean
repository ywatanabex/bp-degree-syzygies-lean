import BPFixedPoints.Incidence.BinaryCoverPairSections
import BPFixedPoints.Incidence.AcyclicResolutionComplex
import BPFixedPoints.Incidence.BinaryCoverCellActualTensorComplex

/-! # Actual Ext acyclicity of the original cubical cell sheaf terms

The specified original free-open pairedGenerators exhibit the original term as
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
noncomputable local instance pairedTermHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
noncomputable local instance pairedFaceIndexFintype (n : ℕ) : Fintype (PairFaceIndex (V := V) n) := by
  classical
  unfold PairFaceIndex
  infer_instance

/-- The original free abelian sheaf at an original degree-n face. -/
noncomputable abbrev pairedFaceFreeOpen (n : ℕ) (q : PairFaceIndex (V := V) n) :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
    (yoneda.obj (pairedFaceOpen U q.val) ⋙ AddCommGrpCat.free)

/-- The finite biproduct map consists of the original specified free-open pairedGenerators. -/
noncomputable def pairedTermBiproductMap (n : ℕ) : (⨁ (pairedFaceFreeOpen U n)) ⟶ pairedSheafTerm U n :=
  biproduct.desc (fun q => pairedGenerator U q)

/-- The original generators give an actual finite-biproduct presentation of the original sheaf term. -/
theorem pairedTermBiproductMap_isIso (n : ℕ) : IsIso (pairedTermBiproductMap U n) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  constructor
  · intro f g he
    apply (pairedSectionsEquiv U F n).injective
    funext q
    rw [pairedSectionsEquiv_apply,pairedSectionsEquiv_apply]
    congr 1
    have hh := congrArg (fun k => biproduct.ι (pairedFaceFreeOpen U n) q ≫ k) he
    simpa only [pairedTermBiproductMap,biproduct.ι_desc_assoc] using hh
  · intro g
    let f := (pairedSectionsEquiv U F n).symm
      (fun q => freeSheafSectionsEquiv F (pairedFaceOpen U q.val) (biproduct.ι (pairedFaceFreeOpen U n) q ≫ g))
    refine ⟨f,?_⟩
    apply biproduct.hom_ext'
    intro q
    rw [pairedTermBiproductMap,biproduct.ι_desc_assoc]
    apply (freeSheafSectionsEquiv F (pairedFaceOpen U q.val)).injective
    rw [← pairedSectionsEquiv_apply]
    exact congrFun ((pairedSectionsEquiv U F n).apply_symm_apply _) q

/-- The specified finite-biproduct isomorphism retains all original generators. -/
noncomputable def pairedTermBiproductIso (n : ℕ) : (⨁ (pairedFaceFreeOpen U n)) ≅ pairedSheafTerm U n := by
  letI := pairedTermBiproductMap_isIso U n
  exact asIso (pairedTermBiproductMap U n)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Actual Ext of the original term is the actual local Ext family on the original faces. -/
noncomputable def pairedTermExtEquiv (n k : ℕ) :
    Ext.{1} (pairedSheafTerm U n) F k ≃+
      (∀ q : PairFaceIndex (V := V) n, F.H' k (pairedFaceOpen U q.val)) :=
  ((((extFunctor k).mapIso (pairedTermBiproductIso U n).op).app F).addCommGroupIsoToAddEquiv).trans
    (Ext.biproductAddEquiv (biproduct.isBilimit (pairedFaceFreeOpen U n)) F k)

/-- Every actual local Ext coordinate is restriction along its originally specified pairedGenerator. -/
theorem pairedTermExtEquiv_apply (n k : ℕ) (x : Ext.{1} (pairedSheafTerm U n) F k) (q : PairFaceIndex (V := V) n) :
    pairedTermExtEquiv U F n k x q = (Ext.mk₀ (pairedGenerator U q)).comp x (zero_add k) := by
  change (Ext.mk₀ (biproduct.ι (pairedFaceFreeOpen U n) q)).comp
    ((Ext.mk₀ (pairedTermBiproductMap U n)).comp x (zero_add k)) (zero_add k) = _
  rw [← Ext.comp_assoc_of_second_deg_zero,Ext.mk₀_comp_mk₀,pairedTermBiproductMap,biproduct.ι_desc]

/-- Actual local vanishing supplies actual relative acyclicity of the original cell sheaf complex terms. -/
theorem pairedSheafComplex_acyclic
    (h : ∀ (n : ℕ) (q : PairFaceIndex (V := V) n) (k : ℕ)
      (x : F.H' (k+1) (pairedFaceOpen U q.val)), x = 0) :
    ExtResolutionTools.ComplexAcyclicAgainst (pairedSheafComplex U) F := by
  intro n k x
  apply (pairedTermExtEquiv U F n (k+1)).injective
  ext q
  exact (h n q k _).trans (by simp)

/-- The independently specified actual tensor terms have the same actual local Ext vanishing. -/
theorem actualTensorSheafComplex_acyclic
    (h : ∀ (n : ℕ) (q : PairFaceIndex (V := V) n) (k : ℕ)
      (x : F.H' (k+1) (pairedFaceOpen U q.val)), x = 0) :
    ExtResolutionTools.ComplexAcyclicAgainst (actualTensorSheafComplex U) F := by
  have ha := pairedSheafComplex_acyclic U F h
  intro n k x
  let E := (((extFunctor (k+1)).mapIso
    (HomologicalComplex.Hom.isoApp (actualTensorPairComplexIso U) n).symm.op).app F).addCommGroupIsoToAddEquiv
  apply E.injective
  exact (ha n k (E x)).trans (map_zero E).symm

end BPFixedPoints.SheafTools.BinaryCells
