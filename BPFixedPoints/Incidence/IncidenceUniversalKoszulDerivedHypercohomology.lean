import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedComparison
import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedCech
import BPFixedPoints.Incidence.SheafTerminalCohomology
import BPFixedPoints.Incidence.BinaryCoverCellCoverAugmentation

/-! # Hypercohomology of the universal Koszul complex (Theorem `alg:resolution`)

* `sheafHypercohomology K n`: hypercohomology of a complex of abelian sheaves on a topological
  space, defined in the derived category as `Hom_{D(Ab)}(ℤ, K[n])` (shifted morphisms from the
  constant sheaf `ℤ`, the unit object of Mathlib's `Sheaf.H`, placed in degree zero). For a sheaf
  in degree zero it is Mathlib's sheaf cohomology (`sheafHypercohomologySingleEquiv`), and for a
  sheaf in degree `p` it is the shifted sheaf cohomology (`sheafHypercohomologySingleShiftEquiv`).
* `incUniversalKoszulHypercohomology G n = H^n(K_G)`, for any model of the derived category.
* `incUniversalKoszul_derivedMapBijective`: `K_G` is bounded (`exteriorBundleAbelian_isZero`) with
  terms acyclic for the cubical cell resolution (`exteriorBundle_terms_acyclic`), so homotopy
  classes from the cell resolution compute derived morphisms.
* `incUniversalKoszulHypercohomologyEquiv`: `H^n(K_G)` is additively isomorphic to the degree-`n`
  Hom-complex cohomology from the cell resolution, which `IncidenceUniversalKoszulDerivedCech.lean`
  identifies with the Čech–Koszul total complex.
* **Main results**: `incUniversalKoszulHypercohomology_eq_zero` (`H^n(K_G) = 0` for `n ≠ 0`) and
  `incUniversalKoszulHypercohomologyZeroEquiv` (`H^0(K_G) ≃+ 𝒰_G`); the `S_G`-linear version is
  `incUniversalKoszulHypercohomologyZeroLinearEquiv` in `IncidenceUniversalKoszulDerivedLinear.lean`.

Not proved here: the identification of `H^0(K_G)` with sections of the pushforward of `O_{Z_G}`
as a sheaf (the augmentation `O → ι_* O_{Z_G}` as a morphism of sheaves).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open TopologicalSpace CechProduct ProjectiveLine SheafTools SheafTools.BinaryCells
open ExtResolutionTools HomologicalComplex ComplexShape CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

universe w w'

section Hypercohomology

variable {T : Type} [TopologicalSpace T]
  [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})]

/-- **Hypercohomology of a complex of abelian sheaves**, defined in the derived category:
`H^n(T, K) = Hom_{D(Ab(T))}(ℤ_T, K[n])`, the degree-`n` shifted morphisms from the constant sheaf
`ℤ_T` (the unit object used by Mathlib's `Sheaf.H`), placed in degree zero, to `K`. -/
noncomputable abbrev sheafHypercohomology
    (K : CochainComplex (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) ℤ) (n : ℤ) :=
  ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ULift ℤ)))) (DerivedCategory.Q.obj K) n

/-- **Hypercohomology of a sheaf placed in degree zero is its sheaf cohomology**: for every
`j : ℕ`, `H^j(T, F[0]) ≃+ Sheaf.H F j` (Mathlib's `Ext`-defined sheaf cohomology). -/
noncomputable def sheafHypercohomologySingleEquiv
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})]
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (j : ℕ) :
    sheafHypercohomology ((CochainComplex.singleFunctor _ 0).obj F) j ≃+ Sheaf.H.{w'} F j :=
  Ext.homAddEquiv.symm

/-- **Hypercohomology of a sheaf placed in degree `p`**: for every `j : ℕ`,
`H^{p+j}(T, F[-p]) ≃+ Sheaf.H F j`, through the shift isomorphism of single complexes in the
derived category and `sheafHypercohomologySingleEquiv`. -/
noncomputable def sheafHypercohomologySingleShiftEquiv
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})]
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (p : ℤ) (j : ℕ) :
    sheafHypercohomology ((CochainComplex.singleFunctor _ p).obj F) (p + j) ≃+ Sheaf.H.{w'} F j :=
  let e : (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ p).obj F))⟦p + (j : ℤ)⟧ ≅
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj F))⟦(j : ℤ)⟧ :=
    (shiftFunctor _ (p + (j : ℤ))).mapIso
        (((DerivedCategory.singleFunctors _).shiftIso (-p) p 0 (by omega)).app F).symm ≪≫
      ((shiftFunctorAdd' _ (-p) (p + (j : ℤ)) (j : ℤ) (by omega)).app _).symm
  ({ toFun := fun x => x ≫ e.hom
     invFun := fun y => y ≫ e.inv
     left_inv := fun x => by simp
     right_inv := fun y => by simp
     map_add' := fun x y => Preadditive.add_comp _ _ _ _ _ _ } :
    sheafHypercohomology ((CochainComplex.singleFunctor _ p).obj F) (p + j) ≃+
      sheafHypercohomology ((CochainComplex.singleFunctor _ 0).obj F) j).trans
    (sheafHypercohomologySingleEquiv F j)

end Hypercohomology

section Universal

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

noncomputable local instance incUniversalKoszulDerivedHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

noncomputable local instance incUniversalKoszulDerivedAugmentationEpi :
    Epi (augmentation (vertexCoordinateOpen (IncCoeffRing E) V)) :=
  augmentation_epi _ (vertexCellChartOpen_cover (IncCoeffRing E) V)

variable [HasDerivedCategory.{w}
  (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0})]

/-- **The hypercohomology `H^n(K_G)`** of the universal Koszul complex on `(ℙ¹)^V` over `S_G`,
in the derived category of abelian sheaves. -/
noncomputable abbrev incUniversalKoszulHypercohomology (n : ℤ) :=
  sheafHypercohomology G.incUniversalKoszulCochainComplex n

/-- The terms of `K_G` vanish above the number of edges. -/
theorem incUniversalKoszulAbelianComplex_isZero (k : ℕ) (hk : Fintype.card E + 1 ≤ k) :
    IsZero (G.incUniversalKoszulAbelianComplex.X k) :=
  G.exteriorBundleAbelian_isZero (IncCoeffRing E) (by omega)

/-- **`Qh` computes morphisms from the cubical cell resolution to `K_G`**: the homotopy category
already has the derived-category morphisms (all shifts), because `K_G` is bounded with terms
acyclic for the cubical cell resolution. -/
theorem incUniversalKoszul_derivedMapBijective :
    DerivedMapBijective DerivedCategory.Qh
      ((HomotopyCategory.quotient _ (up ℤ)).obj
        (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V))))
      ((HomotopyCategory.quotient _ (up ℤ)).obj G.incUniversalKoszulCochainComplex) :=
  derivedMapBijective_negativeComplex_extend
    (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V))
    (augmentation _) (augmentation_zero _) (augmentation_exact _) (sheafComplex_exact _)
    G.incUniversalKoszulAbelianComplex (Fintype.card E + 1)
    (G.incUniversalKoszulAbelianComplex_isZero) (fun k => G.exteriorBundle_terms_acyclic _ k) 0

/-- The derived identification of the augmentation target of the cubical cell resolution with
the constant sheaf `ℤ`. -/
noncomputable def cellAugmentationTargetIso :
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((constantSheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ULift ℤ)))) ≅
    DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
      ((presheafToSheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
        AddCommGrpCat).obj (yoneda.obj ⊤ ⋙ AddCommGrpCat.free))) :=
  DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor _ 0).mapIso freeSheafTopIso.symm)

/-- **The comparison of `H^n(K_G)` with Hom-complex cohomology.** Degree-`n` hypercohomology of
`K_G` is additively isomorphic to the degree-`n` cohomology of the Hom complex from the negative
cubical cell resolution of `ℤ` to `K_G`. -/
noncomputable def incUniversalKoszulHypercohomologyEquiv (n : ℤ) :
    CohomologyClass (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex n ≃+ G.incUniversalKoszulHypercohomology n :=
  (derivedCohomologyClassEquiv (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V))
    (augmentation _) (augmentation_zero _) (augmentation_exact _) (sheafComplex_exact _)
    G.incUniversalKoszulCochainComplex G.incUniversalKoszul_derivedMapBijective n).trans
  { toFun := fun x => (cellAugmentationTargetIso (V := V) (E := E)).hom ≫ x
    invFun := fun y => (cellAugmentationTargetIso (V := V) (E := E)).inv ≫ y
    left_inv := fun x => by simp
    right_inv := fun y => by simp
    map_add' := fun x y => Preadditive.comp_add _ _ _ _ _ _ }

/-- **`H^n(K_G) = 0` for `n ≠ 0`** (the vanishing part of Theorem `alg:resolution`). -/
theorem incUniversalKoszulHypercohomology_eq_zero {n : ℤ} (hn : n ≠ 0)
    (x : G.incUniversalKoszulHypercohomology n) : x = 0 := by
  obtain ⟨c, rfl⟩ := (G.incUniversalKoszulHypercohomologyEquiv n).surjective x
  obtain ⟨z, rfl⟩ := c.mk_surjective
  rw [(CohomologyClass.mk_eq_zero_iff z).mpr (G.cocycle_mem_coboundaries_of_ne_zero hn z), map_zero]

/-- `H^n(K_G)` is trivial for `n ≠ 0`. -/
theorem incUniversalKoszulHypercohomology_subsingleton {n : ℤ} (hn : n ≠ 0) :
    Subsingleton (G.incUniversalKoszulHypercohomology n) :=
  subsingleton_of_forall_eq 0 (G.incUniversalKoszulHypercohomology_eq_zero hn)

/-- **`H^0(K_G) ≅ 𝒰_G`** (the degree-zero part of Theorem `alg:resolution`), additively: the
inverse of the derived comparison followed by the augmentation of the Čech–Koszul model. -/
noncomputable def incUniversalKoszulHypercohomologyZeroEquiv :
    G.incUniversalKoszulHypercohomology 0 ≃+ G.IncidenceRing :=
  (G.incUniversalKoszulHypercohomologyEquiv 0).symm.trans
    (AddEquiv.ofBijective _ G.cohomologyClassZeroAugmentation_bijective)

end Universal

end BPFixedPoints.Multigraph
