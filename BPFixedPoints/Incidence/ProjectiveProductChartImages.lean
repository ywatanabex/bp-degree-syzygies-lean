import BPFixedPoints.Incidence.ProjectivePowerCoordinates
import BPFixedPoints.Incidence.ProjectiveLineChartPreimages

/-! # Exact images of the original polynomial projective-product charts

The actual chart image is the intersection of the original standard opens
under every vertex projection. Mathlib's pullback image theorem includes
all scheme points and is applied over the original coefficient base.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

private theorem overIso_left_surjective {S : Scheme} {X Y : Over S} (e : X ≅ Y) :
    Function.Surjective e.hom.left := by
  intro y
  refine ⟨e.inv.left y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, Iso.inv_hom_id]
  rfl

theorem affineLineChartOver_range (i : Fin 2) :
    Set.range (affineLineChartOver R i).left = (standardOpen R i : Set (projectiveLine R)) := by
  change Set.range (chartι R i ∘ (affineLineOverIso R).hom.left) = _
  rw [Set.range_comp, Set.range_eq_univ.mpr (overIso_left_surjective (affineLineOverIso R)),
    Set.image_univ, ← Scheme.Hom.coe_opensRange, chartι_opensRange]

/-- An original product chart has exactly the prescribed opens in every actual factor. -/
theorem affinePowerChartOver_mem_range (n : ℕ) (σ : Fin n → Fin 2) (x : powerScheme R n) :
    x ∈ Set.range (affinePowerChartOver R n σ).left ↔
      ∀ i, (powerProjectionOver R n i).left x ∈ standardOpen R (σ i) := by
  induction n with
  | zero =>
    constructor
    · intro _ i
      exact Fin.elim0 i
    · intro _
      exact ⟨x, rfl⟩
  | succ n ih =>
    change x ∈ Set.range (prod.map (affineLineChartOver R (σ 0))
      (affinePowerChartOver R n (fun j => σ j.succ))).left ↔ _
    rw [SchemeTools.overProdMap_range]
    change ((prod.fst : overBase R ⨯ powerOverBase R n ⟶ overBase R).left x ∈
      Set.range (affineLineChartOver R (σ 0)).left ∧
      (prod.snd : overBase R ⨯ powerOverBase R n ⟶ powerOverBase R n).left x ∈
        Set.range (affinePowerChartOver R n (fun j => σ j.succ)).left) ↔ _
    rw [affineLineChartOver_range, ih]
    constructor
    · rintro ⟨h₀, hs⟩ i
      refine Fin.cases h₀ (fun j => ?_) i
      exact hs j
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

/-- The independently specified polynomial chart has that same actual image. -/
theorem powerChartι_mem_range (n : ℕ) (σ : Fin n → Fin 2) (x : powerScheme R n) :
    x ∈ Set.range (powerChartι R n σ) ↔
      ∀ i, (powerProjectionOver R n i).left x ∈ standardOpen R (σ i) := by
  have hr : Set.range (powerChartι R n σ) =
      Set.range (affinePowerChartOver R n σ).left := by
    change Set.range ((affinePowerChartOver R n σ).left ∘ (affinePowerIso R n).hom.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr (overIso_left_surjective (affinePowerIso R n)),
      Set.image_univ]
  rw [hr, affinePowerChartOver_mem_range]

variable (V : Type) [Fintype V]

/-- Exact chart-image criterion in the original vertex labels, including the empty product. -/
theorem vertexChartι_mem_range (σ : V → Fin 2) (x : vertexScheme R V) :
    x ∈ Set.range (vertexChartι R V σ) ↔
      ∀ v, (vertexProjectionOver R V v).left x ∈ standardOpen R (σ v) := by
  have hr : Set.range (vertexChartι R V σ) =
      Set.range (powerChartι R (Fintype.card V) (fun j => σ ((Fintype.equivFin V).symm j))) := by
    change Set.range ((powerChartι R (Fintype.card V)
      (fun j => σ ((Fintype.equivFin V).symm j))) ∘ (vertexAffineIso R V).hom.left) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr (overIso_left_surjective (vertexAffineIso R V)),
      Set.image_univ]
  rw [hr, powerChartι_mem_range]
  change (∀ j, (powerProjectionOver R (Fintype.card V) j).left x ∈
    standardOpen R (σ ((Fintype.equivFin V).symm j))) ↔
      ∀ v, (powerProjectionOver R (Fintype.card V) (Fintype.equivFin V v)).left x ∈
        standardOpen R (σ v)
  constructor
  · intro h v
    simpa only [Equiv.symm_apply_apply] using h (Fintype.equivFin V v)
  · intro h j
    simpa only [Equiv.apply_symm_apply] using
      h ((Fintype.equivFin V).symm j)

/-- The actual original vertex polynomial chart as an open of the projective product. -/
noncomputable def vertexChartOpen (σ : V → Fin 2) : (vertexScheme R V).Opens :=
  (vertexChartι R V σ).opensRange

/-- The originally specified polynomial chart images cover the actual terminal open. -/
theorem vertexChartOpen_iSup_top :
    (⊤ : (vertexScheme R V).Opens) ≤ ⨆ σ, vertexChartOpen R V σ := by
  intro x _
  obtain ⟨σ,y,hy⟩ := vertexChart_covers R V x
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨σ,⟨y,hy⟩⟩

/-- Membership in the actual product chart is tested in every original factor. -/
theorem mem_vertexChartOpen (σ : V → Fin 2) (x : vertexScheme R V) :
    x ∈ vertexChartOpen R V σ ↔
      ∀ v, (vertexProjectionOver R V v).left x ∈ standardOpen R (σ v) :=
  vertexChartι_mem_range R V σ x

end BPFixedPoints.ProjectiveLine
