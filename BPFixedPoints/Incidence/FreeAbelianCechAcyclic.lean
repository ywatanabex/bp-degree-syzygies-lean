import BPFixedPoints.Incidence.FreeAbelianCechSections
import BPFixedPoints.Incidence.AcyclicResolutionComplex

/-! # Actual relative acyclicity of finite free-open Čech terms

The original generators exhibit each term as the finite biproduct of the
original free-open sheaves. Mathlib's native Ext biproduct comparison then
reduces actual term Ext to actual local cohomology on the original intersections.
-/

namespace BPFixedPoints.SheafTools.FreeCech
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
attribute [local instance] Abelian.hasFiniteBiproducts
variable {T : Type} [TopologicalSpace T] {ι : Type} [Fintype ι] (U : ι → Opens T)
noncomputable local instance finiteFreeCechHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The original free-open term at a tuple intersection. -/
noncomputable abbrev tupleFreeOpen (q : ℕ) (t : Fin (q+1) → ι) :=
  (presheafToSheaf (Opens.grothendieckTopology T) AddCommGrpCat).obj
    (yoneda.obj (intersection U t) ⋙ AddCommGrpCat.free)

/-- The specified biproduct map is built from the original tuple generators. -/
noncomputable def termBiproductMap (q : ℕ) : (⨁ (tupleFreeOpen U q)) ⟶ freeTerm U q :=
  biproduct.desc (fun t => generator U t)

/-- The original generators exhibit precisely the original term as their finite biproduct. -/
theorem termBiproductMap_isIso (q : ℕ) : IsIso (termBiproductMap U q) := by
  apply isIso_of_coyoneda_map_bijective
  intro F
  constructor
  · intro f g he
    apply (sectionsEquiv U F q).injective
    funext t
    rw [sectionsEquiv_apply, sectionsEquiv_apply]
    congr 1
    have hh := congrArg (fun k => biproduct.ι (tupleFreeOpen U q) t ≫ k) he
    simpa only [termBiproductMap, biproduct.ι_desc_assoc] using hh
  · intro g
    let f := (sectionsEquiv U F q).symm
      (fun t => freeSheafSectionsEquiv F (intersection U t) (biproduct.ι (tupleFreeOpen U q) t ≫ g))
    refine ⟨f, ?_⟩
    apply biproduct.hom_ext'
    intro t
    rw [termBiproductMap, biproduct.ι_desc_assoc]
    apply (freeSheafSectionsEquiv F (intersection U t)).injective
    rw [← sectionsEquiv_apply]
    exact congrFun ((sectionsEquiv U F q).apply_symm_apply _) t

/-- The canonical finite-sum comparison keeps the original generators. -/
noncomputable def termBiproductIso (q : ℕ) : (⨁ (tupleFreeOpen U q)) ≅ freeTerm U q := by
  letI := termBiproductMap_isIso U q
  exact asIso (termBiproductMap U q)

variable (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})

/-- Native Ext of an original finite tuple term is the tuple family of native local Ext groups. -/
noncomputable def termExtEquiv (q n : ℕ) :
    Ext.{1} (freeTerm U q) F n ≃+ (∀ t : Fin (q+1) → ι, F.H' n (intersection U t)) :=
  ((((extFunctor n).mapIso (termBiproductIso U q).op).app F).addCommGroupIsoToAddEquiv).trans
    (Ext.biproductAddEquiv (biproduct.isBilimit (tupleFreeOpen U q)) F n)

/-- Every native local Ext coordinate is restriction along the original free-open generator. -/
theorem termExtEquiv_apply (q n : ℕ) (x : Ext.{1} (freeTerm U q) F n) (t : Fin (q+1) → ι) :
    termExtEquiv U F q n x t = (Ext.mk₀ (generator U t)).comp x (zero_add n) := by
  change (Ext.mk₀ (biproduct.ι (tupleFreeOpen U q) t)).comp
    ((Ext.mk₀ (termBiproductMap U q)).comp x (zero_add n)) (zero_add n) = _
  rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, termBiproductMap, biproduct.ι_desc]

/-- Actual local cohomology vanishing supplies actual relative acyclicity of every original Čech term. -/
theorem freeSheafComplex_acyclic
    (h : ∀ (q : ℕ) (t : Fin (q+1) → ι) (k : ℕ) (x : F.H' (k+1) (intersection U t)), x = 0) :
    ExtResolutionTools.ComplexAcyclicAgainst
      (freeSheafComplex (Opens.grothendieckTopology T) (coverVertices U)) F := by
  intro q k x
  apply (termExtEquiv U F q (k+1)).injective
  ext t
  exact (h q t k _).trans (by simp)

end BPFixedPoints.SheafTools.FreeCech
