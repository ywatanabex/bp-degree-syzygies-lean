import BPFixedPoints.Incidence.VertexPermutationCellTransport
import BPFixedPoints.Incidence.VertexPermutationTwistStateCoefficients
import BPFixedPoints.Incidence.IncidenceVertexRelabelExterior

/-!
# The state formula for vertex bijections

For a bijection `ψ : V ≃ W` the geometric map of multi-twist cohomology `vertexTwistHPerm` is the
transport of Ext-defined cohomology along the scheme isomorphism of vertex projective products,
followed by the transport `g_* O(-d) ≅ O(-d ∘ ψ⁻¹)` of the twist sheaves. It is defined without
states (`VertexPermutationTwistCohomology.lean`).

Proved here, in every degree including degree zero:
* on the class of a cubical cocycle, the geometric map gives the class of the transported cocycle
  (`vertexSheafHPerm_cellClass`, `vertexTwistHPerm_cellClass`), from the naturality of the cubical
  cell route along the homeomorphism (`cellTransport_class`);
* **the multi-twist state formula** `vertexTwistStateFormula : VertexTwistStateFormula R ψ`: the
  state coordinates of the geometric image are the signed relabeling `hVertexPerm` of the state
  coordinates, from the coefficients of transported cochains
  (`vertexCellCochainPerm_coefficient`) and `contraction_p_cechVertexPerm`;
* the unconditional exterior consequences: the exterior state formula
  (`VertexRelabel.exteriorCohomologyState_vertexRelabel`), the naturality square of
  `incidenceTorExteriorEquiv` (`VertexRelabel.incidenceTorExteriorEquiv_vertexRelabel`), and the
  preservation of the exterior products and unit.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open Opposite SheafTools SheafTools.BinaryCells ExtResolutionTools ProjectiveLine CechProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000

noncomputable local instance stateFormulaHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

noncomputable local instance stateFormulaTopHasExt (S : TopCat.{0}) :
    HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} S) := HasExt.standard _

variable (R : Type) [CommRing R] {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
  [DecidableEq W] (ψ : V ≃ W)

/-- **Transport of cubical classes along the vertex permutation.** The transport of
Ext-defined cohomology `vertexSheafHPerm` sends the class of a cubical cocycle of `(P¹)^V` to the
class of the pulled back image cocycle of `(P¹)^W`. -/
theorem vertexSheafHPerm_cellClass (F : Sheaf (Opens.grothendieckTopology (vertexScheme R V))
    AddCommGrpCat.{0}) (n : ℕ) (z : (cubicalTower (vertexCoordinateOpen R V)).cycles F n) :
    letI := augmentation_epi (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
    letI := augmentation_epi (vertexCoordinateOpen R W) (vertexCellChartOpen_cover R W)
    vertexSheafHPerm R ψ F n (localSheafTopEquiv F n
        ((Ext.mk₀ (complexAugmentationIso _ (augmentation (vertexCoordinateOpen R V))
          (augmentation_zero _) (augmentation_exact _)).inv).comp
            ((cubicalTower (vertexCoordinateOpen R V)).cocycleComparison F n z) (zero_add n))) =
      localSheafTopEquiv ((vertexSheafPerm R ψ).functor.obj F) n
        ((Ext.mk₀ (complexAugmentationIso _ (augmentation (vertexCoordinateOpen R W))
          (augmentation_zero _) (augmentation_exact _)).inv).comp
            ((cubicalTower (vertexCoordinateOpen R W)).cocycleComparison _ n
              ((complexMapSourceMap (vertexSheafPerm R ψ).functor
                (sheafComplex_exact (vertexCoordinateOpen R V))
                (sheafComplex_exact (vertexCoordinateOpen R W)) (vertexCellChainMap R ψ)).cycles _ n
                  (towerMapCycles (vertexSheafPerm R ψ).functor n z))) (zero_add n)) :=
  cellTransport_class (vertexSchemePermHomeo R ψ) ψ (vertexCoordinateOpen R V)
    (vertexCoordinateOpen R W) (vertexCoordinateOpen_map R ψ) (vertexCellChartOpen_cover R V)
    (vertexCellChartOpen_cover R W) F n z

/-- The transported cocycle of a cubical cocycle of `O(-d)`. -/
noncomputable def vertexCellCyclePerm (d : V → ℕ) (n : ℕ) (z : vertexTwistCellCycles R V d n) :
    vertexTwistCellCycles R W (fun w => d (ψ.symm w)) n :=
  ⟨vertexCellCochainPerm R ψ d n z.val, vertexCellCochainPerm_cycle R ψ d n z⟩

variable [IsNoetherianRing R]

/-- **The geometric map on cubical classes.** The geometric map of multi-twist cohomology sends
the class of a cubical cocycle of `O(-d)` to the class of the transported cocycle. -/
theorem vertexTwistHPerm_cellClass (d : V → ℕ) (n : ℕ) (z : vertexTwistCellCycles R V d n) :
    vertexTwistHPerm R ψ (fun v => -(d v : ℤ)) (fun w => -(d (ψ.symm w) : ℤ)) (fun v => by simp) n
        (vertexTwistCellActualAtLinearEquiv R V _ n
          ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n z)) =
      vertexTwistCellActualAtLinearEquiv R W _ n
        ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n (vertexCellCyclePerm R ψ d n z)) := by
  let _ := augmentation_epi (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V)
  let _ := augmentation_epi (vertexCoordinateOpen R W) (vertexCellChartOpen_cover R W)
  rw [vertexTwistHPerm_apply]
  change Sheaf.H.map (vertexNegativeTwistPermIso R ψ d).hom n (vertexSheafHPerm R ψ _ n
      (finiteCubicalActualAtEquiv (vertexCoordinateOpen R V) _ (vertexCellChartOpen_cover R V)
        (vertexTwistCellSheaf_terms_acyclic R V _) n
          ((cubicalTower (vertexCoordinateOpen R V)).classAt _ n z))) =
    finiteCubicalActualAtEquiv (vertexCoordinateOpen R W) _ (vertexCellChartOpen_cover R W)
      (vertexTwistCellSheaf_terms_acyclic R W _) n
        ((cubicalTower (vertexCoordinateOpen R W)).classAt _ n (vertexCellCyclePerm R ψ d n z))
  rw [finiteCubicalActualAtEquiv_class, finiteCubicalActualAtEquiv_class, vertexSheafHPerm_cellClass,
    ← localSheafTopEquiv_naturality]
  congr 1
  rw [Ext.comp_assoc_of_third_deg_zero, ← ExactTower.cocycleComparison_postcomp]
  congr 2

/-- **The multi-twist state formula.** For every vertex bijection, the state coordinates of the
geometric map of the cohomology of `O(-d)` are the signed relabeling `hVertexPerm` (Koszul sign of
`ψ` on the twist support) of the state coordinates, in every degree. -/
theorem vertexTwistStateFormula : VertexTwistStateFormula R ψ := by
  intro d d' h n x
  subst h
  obtain ⟨y, rfl⟩ := (vertexTwistCellActualAtLinearEquiv R V (fun v => -(d v : ℤ)) n).surjective x
  obtain ⟨z, rfl⟩ := (cubicalTower (vertexCoordinateOpen R V)).classAt_surjective _ n y
  have hx := vertexTwistHPerm_cellClass R ψ d n z
  erw [hx]
  rw [vertexTwistActualStateAt_actual, vertexTwistActualStateAt_actual, vertexTwistCellStateAt_class,
    vertexTwistCellStateAt_class, castH_rfl, vertexTwistCellCycleProjection_val,
    vertexTwistCellCycleProjection_val]
  change (contraction R _).p (vertexTwistCellCoefficientEquiv R W _ n
    (vertexCellCochainPerm R ψ d n z.val)).val = _
  rw [vertexCellCochainPerm_coefficient, contraction_p_cechVertexPerm]

/-- The state formula in the form used below: the state coordinates of the geometric image of a
class of `O(-d)` are the signed relabeling of its state coordinates. -/
theorem vertexTwistActualStateAt_vertexTwistHPerm (d : V → ℕ) (n : ℕ)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    (vertexTwistActualStateAt R W (fun w => d (ψ.symm w)) n
      (vertexTwistHPerm R ψ (fun v => -(d v : ℤ)) (fun w => -(d (ψ.symm w) : ℤ)) (fun v => by simp) n
        x) : CechProduct.H R (fun w => d (ψ.symm w))) =
      hVertexPerm R ψ d (vertexTwistActualStateAt R V d n x) :=
  vertexTwistStateFormula R ψ d _ rfl n x

namespace VertexRelabel

variable {V W E : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E]
  [Fintype E] {G : Multigraph V E} {H : Multigraph W E} (φ : VertexRelabel G H)
variable (R : Type) [CommRing R] [IsNoetherianRing R]

/-- **Exterior state formula.** The state vector of the geometric image of an exterior class is
the signed relabeling of its state vector, with the Koszul sign of the Tor side. -/
theorem exteriorCohomologyState_vertexRelabel (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    H.exteriorCohomologyState R q j (φ.exteriorCohomologyVertexRelabel R q j x) =
      φ.statePerm R (G.exteriorCohomologyState R q j x) :=
  φ.exteriorCohomologyState_vertexRelabel_of R (vertexTwistStateFormula R φ.vertex) q j x

/-- **Naturality square.** The Tor-to-exterior isomorphism carries the Tor map of a vertex
relabeling to the geometric map of exterior cohomology. -/
theorem incidenceTorExteriorEquiv_vertexRelabel {p q : ℕ} (h : p ≤ q)
    (x : G.incidenceTorInternalPiece p q) :
    H.incidenceTorExteriorEquiv h (φ.incidenceTorInternalVertexRelabel p q x) =
      φ.exteriorCohomologyVertexRelabel ℂ q (q - p) (G.incidenceTorExteriorEquiv h x) :=
  φ.incidenceTorExteriorEquiv_vertexRelabel_of (vertexTwistStateFormula ℂ φ.vertex) h x

/-- **Products.** The geometric map preserves the exterior cohomology products. -/
theorem exteriorCohomologyVertexRelabel_product (q q' i j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) i)
    (y : Sheaf.H.{1} (G.exteriorBundleAbelian R q') j) :
    φ.exteriorCohomologyVertexRelabel R (q + q') (i + j) (G.exteriorCohomologyProduct R q q' i j x y) =
      H.exteriorCohomologyProduct R q q' i j (φ.exteriorCohomologyVertexRelabel R q i x)
        (φ.exteriorCohomologyVertexRelabel R q' j y) :=
  φ.exteriorCohomologyVertexRelabel_product_of R (vertexTwistStateFormula R φ.vertex) q q' i j x y

/-- **Unit.** The geometric map sends the exterior unit to the unit. -/
theorem exteriorCohomologyVertexRelabel_unit :
    φ.exteriorCohomologyVertexRelabel R 0 0 (G.exteriorCohomologyUnit R) = H.exteriorCohomologyUnit R :=
  φ.exteriorCohomologyVertexRelabel_unit_of R (vertexTwistStateFormula R φ.vertex)

end VertexRelabel

end BPFixedPoints.Multigraph
