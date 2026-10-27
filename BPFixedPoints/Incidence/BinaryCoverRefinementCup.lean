import BPFixedPoints.Incidence.BinaryCoverRefinementComplex
import BPFixedPoints.Incidence.BinaryCoverStandardCupSource
import BPFixedPoints.Incidence.BinaryCoverCellAcyclic

/-! # The standard cup does not depend on the binary cover, under explicit acyclicity

Two binary cover families `U : I → Fin 2 → Opens T` and `W : J → Fin 2 → Opens T`
on the same space have the concatenated family `Sum.elim U W` on `I ⊕ J`. Its
cell opens are the intersections of a `U`-cell open and a `W`-cell open, and its
charts cover whenever those of `U` and of `W` do. The forgetful chain maps of
`BinaryCoverRefinementComplex` along `Sum.inl` and `Sum.inr` are
augmentation-preserving chain maps from its cell complex to those of `U` and
of `W`. Applying `actualStandardClassCup_source` to both shows:

* `actualStandardClassCup_common_refinement`: for any family `C` on `K` with
  injections `I → K`, `J → K` along which the opens of `C` are smaller, the
  standard products through `U` and through `W` agree;
* `actualStandardClassCup_concat`: the same for the concatenated family.

The hypotheses are exactly those of the existing statements: the three chart
covers, and relative Ext acyclicity of the three cell complexes against both
input sheaves. For the concatenated family the cover is proved
(`chartOpen_sum_cover`), and acyclicity is reduced to local vanishing on the
pairwise intersections of cell opens (`sheafComplex_sum_acyclic`,
`actualStandardClassCup_concat_of_vanishing`). Acyclicity is not claimed in
general.

For a family `U ∘ τ` along a surjective relabelling `τ : K → I` of directions
(including reorderings and repetitions), every cell open is a cell open of `U`
(`binaryCoverFaceOpen_comp_surjective`), and the charts of `U ∘ τ` cover when
those of `U` do, for any `τ` (`chartOpen_comp_cover`).
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite Function
open ExtResolutionTools AbelianTensor
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
noncomputable section
variable {T : Type} [TopologicalSpace T]

local instance refinementCupSmallColimits :
    HasColimitsOfSize.{0,0} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  CategoryTheory.Sheaf.instHasColimitsOfSize
local instance refinementCupDerivedCategory :
    HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _
local instance refinementCupHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

variable {I J K : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype K] [DecidableEq K]
variable {F G H : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}} (b : SectionPairing F G H)

/-- Along a common refinement `C` of `U` and `W` by injective relabellings of directions, the
standard products computed through `U` and through `W` agree, provided the cell complexes of all
three families are acyclic against both input sheaves. -/
theorem actualStandardClassCup_common_refinement (C : K → Fin 2 → Opens T)
    (U : I → Fin 2 → Opens T) (W : J → Fin 2 → Opens T) {ι : I → K} {κ : J → K}
    (hι : Injective ι) (hκ : Injective κ) (hCU : ∀ i c, C (ι i) c ≤ U i c)
    (hCW : ∀ j c, C (κ j) c ≤ W j c) (hC : (⊤ : Opens T) ≤ ⨆ k, chartOpen C k)
    (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k) (hW : (⊤ : Opens T) ≤ ⨆ k, chartOpen W k)
    (aCF : ComplexAcyclicAgainst (sheafComplex C) F) (aCG : ComplexAcyclicAgainst (sheafComplex C) G)
    (aUF : ComplexAcyclicAgainst (sheafComplex U) F) (aUG : ComplexAcyclicAgainst (sheafComplex U) G)
    (aWF : ComplexAcyclicAgainst (sheafComplex W) F) (aWG : ComplexAcyclicAgainst (sheafComplex W) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hU b aUF aUG i j a c = actualStandardClassCup W hW b aWF aWG i j a c := by
  rw [← actualStandardClassCup_source C U hC hU (relabelSheafComplex C U hι hCU)
      (relabelSheafComplex_augmentation C U hι hCU) b aCF aUF aCG aUG i j a c,
    actualStandardClassCup_source C W hC hW (relabelSheafComplex C W hκ hCW)
      (relabelSheafComplex_augmentation C W hκ hCW) b aCF aWF aCG aWG i j a c]

variable (U : I → Fin 2 → Opens T) (W : J → Fin 2 → Opens T)

/-- A cell open of the concatenated family is the intersection of the two cell opens. -/
theorem binaryCoverFaceOpen_sum (q : I ⊕ J → Fin 3) :
    binaryCoverFaceOpen (Sum.elim U W) q =
      binaryCoverFaceOpen U (q ∘ Sum.inl) ⊓ binaryCoverFaceOpen W (q ∘ Sum.inr) := by
  apply le_antisymm
  · exact le_inf (le_iInf fun i => iInf_le _ (Sum.inl i)) (le_iInf fun j => iInf_le _ (Sum.inr j))
  · apply le_iInf
    intro k
    cases k with
    | inl i => exact inf_le_left.trans (iInf_le _ i)
    | inr j => exact inf_le_right.trans (iInf_le _ j)

/-- The charts of the concatenated family cover when those of both families do. -/
theorem chartOpen_sum_cover (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
    (hW : (⊤ : Opens T) ≤ ⨆ k, chartOpen W k) :
    (⊤ : Opens T) ≤ ⨆ k, chartOpen (Sum.elim U W) k := by
  calc (⊤ : Opens T) ≤ (⨆ k, chartOpen U k) ⊓ ⨆ k, chartOpen W k := le_inf hU hW
    _ = ⨆ p : (I → Fin 2) × (J → Fin 2), chartOpen U p.1 ⊓ chartOpen W p.2 := iSup_inf_iSup
    _ ≤ ⨆ k, chartOpen (Sum.elim U W) k := by
      apply iSup_le
      intro p
      refine le_iSup_of_le (Sum.elim p.1 p.2) ?_
      apply le_iInf
      intro k
      cases k with
      | inl i => exact inf_le_left.trans (iInf_le _ i)
      | inr j => exact inf_le_right.trans (iInf_le _ j)

/-- Local vanishing on every intersection of a `U`-cell open and a `W`-cell open makes the cell
complex of the concatenated family acyclic. -/
theorem sheafComplex_sum_acyclic (K' : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (h : ∀ (p : I → Fin 3) (p' : J → Fin 3) (k : ℕ)
      (x : K'.H' (k+1) (binaryCoverFaceOpen U p ⊓ binaryCoverFaceOpen W p')), x = 0) :
    ComplexAcyclicAgainst (sheafComplex (Sum.elim U W)) K' := by
  apply sheafComplex_acyclic
  intro n q k x
  have hx := h (q.val ∘ Sum.inl) (q.val ∘ Sum.inr) k
  rw [← binaryCoverFaceOpen_sum] at hx
  exact hx x

/-- The standard products computed through two binary covers agree, provided the cell complexes
of both covers and of their concatenation are acyclic against both input sheaves. -/
theorem actualStandardClassCup_concat (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
    (hW : (⊤ : Opens T) ≤ ⨆ k, chartOpen W k)
    (aF : ComplexAcyclicAgainst (sheafComplex (Sum.elim U W)) F)
    (aG : ComplexAcyclicAgainst (sheafComplex (Sum.elim U W)) G)
    (aUF : ComplexAcyclicAgainst (sheafComplex U) F) (aUG : ComplexAcyclicAgainst (sheafComplex U) G)
    (aWF : ComplexAcyclicAgainst (sheafComplex W) F) (aWG : ComplexAcyclicAgainst (sheafComplex W) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hU b aUF aUG i j a c = actualStandardClassCup W hW b aWF aWG i j a c :=
  actualStandardClassCup_common_refinement b (Sum.elim U W) U W Sum.inl_injective Sum.inr_injective
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (chartOpen_sum_cover U W hU hW) hU hW aF aG aUF aUG
    aWF aWG i j a c

/-- The standard products computed through two binary covers agree when both input sheaves have
vanishing higher local cohomology on every intersection of a `U`-cell open and a `W`-cell open;
the acyclicity of the cell complexes of `U` and of `W` is the one the two products already use. -/
theorem actualStandardClassCup_concat_of_vanishing (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k)
    (hW : (⊤ : Opens T) ≤ ⨆ k, chartOpen W k)
    (hF : ∀ (p : I → Fin 3) (p' : J → Fin 3) (k : ℕ)
      (x : F.H' (k+1) (binaryCoverFaceOpen U p ⊓ binaryCoverFaceOpen W p')), x = 0)
    (hG : ∀ (p : I → Fin 3) (p' : J → Fin 3) (k : ℕ)
      (x : G.H' (k+1) (binaryCoverFaceOpen U p ⊓ binaryCoverFaceOpen W p')), x = 0)
    (aUF : ComplexAcyclicAgainst (sheafComplex U) F) (aUG : ComplexAcyclicAgainst (sheafComplex U) G)
    (aWF : ComplexAcyclicAgainst (sheafComplex W) F) (aWG : ComplexAcyclicAgainst (sheafComplex W) G)
    (i j : ℕ) (a : F.H i) (c : G.H j) :
    actualStandardClassCup U hU b aUF aUG i j a c = actualStandardClassCup W hW b aWF aWG i j a c :=
  actualStandardClassCup_concat b U W hU hW (sheafComplex_sum_acyclic U W F hF)
    (sheafComplex_sum_acyclic U W G hG) aUF aUG aWF aWG i j a c

/-- Charts pull back along any relabelling of directions: the charts of `U ∘ τ` cover when those
of `U` do. -/
theorem chartOpen_comp_cover (τ : K → I) (hU : (⊤ : Opens T) ≤ ⨆ k, chartOpen U k) :
    (⊤ : Opens T) ≤ ⨆ k, chartOpen (fun k => U (τ k)) k := by
  refine hU.trans (iSup_le fun e => le_iSup_of_le (e ∘ τ) ?_)
  exact le_iInf fun k => iInf_le _ (τ k)

/-- The merged label of all coordinates over one direction of `U`: the common endpoint if all
of them are that endpoint, and the overlap otherwise. -/
def mergeLabel (τ : K → I) (q : K → Fin 3) (i : I) : Fin 3 :=
  if ∀ k, τ k = i → q k = 0 then 0 else if ∀ k, τ k = i → q k = 1 then 1 else 2

/-- Along a surjective relabelling of directions, every cell open of `U ∘ τ` is a cell open of
`U`. -/
theorem binaryCoverFaceOpen_comp_surjective {τ : K → I} (hτ : Surjective τ) (q : K → Fin 3) :
    binaryCoverFaceOpen (fun k => U (τ k)) q = binaryCoverFaceOpen U (mergeLabel τ q) := by
  apply le_antisymm
  · apply le_iInf
    intro i
    obtain ⟨k₀, hk₀⟩ := hτ i
    unfold mergeLabel
    by_cases h0 : ∀ k, τ k = i → q k = 0
    · rw [ite_eq_left h0]
      refine (iInf_le _ k₀).trans ?_
      rw [h0 k₀ hk₀, ← hk₀]
    · rw [ite_eq_right h0]
      by_cases h1 : ∀ k, τ k = i → q k = 1
      · rw [ite_eq_left h1]
        refine (iInf_le _ k₀).trans ?_
        rw [h1 k₀ hk₀, ← hk₀]
      · rw [ite_eq_right h1]
        push Not at h0 h1
        obtain ⟨k, hk, hk0⟩ := h0
        obtain ⟨k', hk', hk1⟩ := h1
        apply le_inf
        · refine (iInf_le _ k').trans ?_
          change binaryCoverFaceFactor (U (τ k')) (q k') ≤ U i 0
          rw [hk']
          generalize q k' = e at hk1
          fin_cases e
          · exact le_rfl
          · exact (hk1 rfl).elim
          · exact inf_le_left
        · refine (iInf_le _ k).trans ?_
          change binaryCoverFaceFactor (U (τ k)) (q k) ≤ U i 1
          rw [hk]
          generalize q k = e at hk0
          fin_cases e
          · exact (hk0 rfl).elim
          · exact le_rfl
          · exact inf_le_right
  · apply le_iInf
    intro k
    refine (iInf_le _ (τ k)).trans ?_
    change binaryCoverFaceFactor (U (τ k)) (mergeLabel τ q (τ k)) ≤
      binaryCoverFaceFactor (U (τ k)) (q k)
    unfold mergeLabel
    by_cases h0 : ∀ k', τ k' = τ k → q k' = 0
    · rw [ite_eq_left h0, h0 k rfl]
    · rw [ite_eq_right h0]
      by_cases h1 : ∀ k', τ k' = τ k → q k' = 1
      · rw [ite_eq_left h1, h1 k rfl]
      · rw [ite_eq_right h1]
        generalize q k = e
        fin_cases e
        · exact inf_le_left
        · exact inf_le_right
        · exact le_rfl

/-- Along a surjective relabelling of directions, local vanishing on the cell opens of `U` makes
the cell complex of `U ∘ τ` acyclic. -/
theorem sheafComplex_comp_surjective_acyclic {τ : K → I} (hτ : Surjective τ)
    (K' : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (h : ∀ (p : I → Fin 3) (k : ℕ) (x : K'.H' (k+1) (binaryCoverFaceOpen U p)), x = 0) :
    ComplexAcyclicAgainst (sheafComplex (fun k => U (τ k))) K' := by
  apply sheafComplex_acyclic
  intro n q k x
  have hx := h (mergeLabel τ q.val) k
  rw [← binaryCoverFaceOpen_comp_surjective U hτ] at hx
  exact hx x

/-- The concatenation of `U` with `U ∘ σ` is the relabelled family along `Sum.elim id σ`. -/
theorem sum_elim_comp (σ : J → I) :
    Sum.elim U (fun j => U (σ j)) = fun k => U (Sum.elim id σ k) := by
  funext k
  cases k <;> rfl

end
end BPFixedPoints.SheafTools.BinaryCells
