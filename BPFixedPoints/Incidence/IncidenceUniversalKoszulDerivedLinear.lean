import BPFixedPoints.Incidence.IncidenceUniversalKoszulDerivedHypercohomology

/-! # `S_G`-linearity of `H^0(K_G) ≅ 𝒰_G`

* `derivedCohomologyClassHom_postcomp`: the derived comparison of
  `IncidenceUniversalKoszulDerivedComparison.lean` is natural in the target complex.
* `incUniversalKoszulScalar`, `incUniversalKoszulCochainScalar`: the action of `r ∈ S_G` on `K_G`
  by the geometric scalar endomorphisms of the exterior bundles (a chain map, since the Koszul
  differential is a morphism of sheaves of modules).
* `incUniversalKoszulHypercohomologyModule`: the resulting `S_G`-module structure on `H^n(K_G)`,
  by postcomposition with the derived image of these endomorphisms.
* `cechOfCochain_postcomp_scalar`: the Hom-complex/Čech–Koszul comparison is `S_G`-linear.
* `incUniversalKoszulHypercohomologyZeroLinearEquiv`: `H^0(K_G) ≃ₗ[S_G] 𝒰_G`, with `S_G` acting on
  `𝒰_G = IncidenceRing` through `coeffHom`.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open TopologicalSpace CechProduct ProjectiveLine SheafTools SheafTools.BinaryCells SchemeTools
open ExtResolutionTools HomologicalComplex ComplexShape CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 8000
set_option maxHeartbeats 1600000

universe w w' v u

section Naturality

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
variable (P : ChainComplex C ℕ) {A : C} (π : P.X 0 ⟶ A) (hπ : P.d 1 0 ≫ π = 0)
  (e : (ShortComplex.mk (P.d 1 0) π hπ).Exact) [Epi π] (hP : ∀ n, P.ExactAt (n + 1))

/-- **Naturality of the derived comparison in the target complex.** Postcomposing a cocycle with
a morphism of complexes `f` corresponds to postcomposing the derived morphism with `Q(f)[n]`. -/
theorem derivedCohomologyClassHom_postcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ)
    (x : Cocycle (negativeComplex P) K n) :
    derivedCohomologyClassHom P π hπ e hP L n (CohomologyClass.mk (x.postcomp f)) =
      derivedCohomologyClassHom P π hπ e hP K n (CohomologyClass.mk x) ≫
        (DerivedCategory.Q.map f)⟦n⟧' := by
  change (Iso.homCongr _ _) (DerivedCategory.Qh.map ((Iso.homCongr _ _)
      (CohomologyClass.toHom (CohomologyClass.mk (x.postcomp f))))) =
    (Iso.homCongr _ _) (DerivedCategory.Qh.map ((Iso.homCongr _ _)
      (CohomologyClass.toHom (CohomologyClass.mk x)))) ≫ (DerivedCategory.Q.map f)⟦n⟧'
  simp only [Iso.homCongr_apply, CohomologyClass.toHom_mk, Cocycle.equivHomShift_symm_postcomp,
    Functor.map_comp, Iso.refl_inv, Category.id_comp, Category.assoc, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  congr 2
  have hε : DerivedCategory.Qh.map ((HomotopyCategory.quotient C (up ℤ)).map f) ≫
      (DerivedCategory.quotientCompQhIso C).hom.app L =
      (DerivedCategory.quotientCompQhIso C).hom.app K ≫ DerivedCategory.Q.map f :=
    (DerivedCategory.quotientCompQhIso C).hom.naturality f
  rw [← Functor.map_comp_assoc, Functor.commShiftIso_hom_naturality, Functor.map_comp,
    Category.assoc, Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, hε,
    Functor.map_comp]

end Naturality

section Scalars

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)

/-- **The `S_G`-action on `K_G`**: the geometric scalar endomorphism of every exterior bundle,
a chain endomorphism of the abelian Koszul complex (the Koszul differential is a morphism of
sheaves of modules). -/
noncomputable def incUniversalKoszulScalar (r : IncCoeffRing E) :
    G.incUniversalKoszulAbelianComplex ⟶ G.incUniversalKoszulAbelianComplex where
  f k := schemeBaseAbelianScalar (vertexToBase (IncCoeffRing E) V)
    (G.exteriorBundle (IncCoeffRing E) k) r
  comm' i j hij := by
    obtain rfl : i = j + 1 := hij.symm
    rw [incUniversalKoszulAbelianComplex_d]
    exact schemeBaseAbelianScalar_naturality _ _ r

/-- The components of the scalar endomorphism of `K_G`. -/
theorem incUniversalKoszulScalar_f (r : IncCoeffRing E) (k : ℕ) :
    (G.incUniversalKoszulScalar r).f k = schemeBaseAbelianScalar (vertexToBase (IncCoeffRing E) V)
      (G.exteriorBundle (IncCoeffRing E) k) r := rfl

/-- The scalar `1` acts as the identity of `K_G`. -/
theorem incUniversalKoszulScalar_one : G.incUniversalKoszulScalar 1 = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun _ => schemeBaseAbelianScalar_one _ _

/-- The scalar `0` acts as zero on `K_G`. -/
theorem incUniversalKoszulScalar_zero : G.incUniversalKoszulScalar 0 = 0 :=
  HomologicalComplex.hom_ext _ _ fun _ => schemeBaseAbelianScalar_zero _ _

/-- The scalar action on `K_G` is additive in the scalar. -/
theorem incUniversalKoszulScalar_add (r s : IncCoeffRing E) :
    G.incUniversalKoszulScalar (r + s) = G.incUniversalKoszulScalar r + G.incUniversalKoszulScalar s :=
  HomologicalComplex.hom_ext _ _ fun _ => schemeBaseAbelianScalar_add _ _ r s

/-- The scalar action on `K_G` is multiplicative in the scalar (in action order). -/
theorem incUniversalKoszulScalar_mul (r s : IncCoeffRing E) :
    G.incUniversalKoszulScalar (r * s) = G.incUniversalKoszulScalar s ≫ G.incUniversalKoszulScalar r :=
  HomologicalComplex.hom_ext _ _ fun _ => schemeBaseAbelianScalar_mul _ _ r s

/-- The `S_G`-action on `K_G` as a cochain complex. -/
noncomputable def incUniversalKoszulCochainScalar (r : IncCoeffRing E) :
    G.incUniversalKoszulCochainComplex ⟶ G.incUniversalKoszulCochainComplex :=
  extendMap (G.incUniversalKoszulScalar r) (embeddingUpIntLE 0)

/-- **The `S_G`-module structure on `H^n(K_G)`**: `r` acts by postcomposition with the derived
image of the scalar endomorphism `r` of `K_G`, shifted by `n`. -/
@[instance_reducible] noncomputable def incUniversalKoszulHypercohomologyModule
    [HasDerivedCategory.{w}
      (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0})]
    (n : ℤ) : Module (IncCoeffRing E) (G.incUniversalKoszulHypercohomology n) where
  smul r x := x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar r))⟦n⟧'
  one_smul x := by
    change x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar 1))⟦n⟧' = x
    rw [incUniversalKoszulCochainScalar, incUniversalKoszulScalar_one, extendMap_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  mul_smul r s x := by
    change x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar (r * s)))⟦n⟧' =
      (x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar s))⟦n⟧') ≫
        (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar r))⟦n⟧'
    rw [incUniversalKoszulCochainScalar, incUniversalKoszulScalar_mul, extendMap_comp,
      Functor.map_comp, Functor.map_comp, Category.assoc]
    rfl
  smul_zero r := zero_comp
  smul_add r x y := Preadditive.add_comp _ _ _ _ _ _
  add_smul r s x := by
    change x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar (r + s)))⟦n⟧' =
      x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar r))⟦n⟧' +
        x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar s))⟦n⟧'
    rw [incUniversalKoszulCochainScalar, incUniversalKoszulScalar_add, extendMap_add,
      Functor.map_add, Functor.map_add, Preadditive.comp_add]
    rfl
  zero_smul x := by
    change x ≫ (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar 0))⟦n⟧' = 0
    rw [incUniversalKoszulCochainScalar, incUniversalKoszulScalar_zero, extendMap_zero,
      Functor.map_zero, Functor.map_zero, comp_zero]

/-- The blocks of a cochain postcomposed with the scalar `r` of `K_G`. -/
theorem cochainBlock_postcomp_scalar {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) (r : IncCoeffRing E) (i k : ℕ) (h : (i : ℤ) = k + m) :
    cochainBlock _ _ i k h (z.comp (Cochain.ofHom (G.incUniversalKoszulCochainScalar r)) (add_zero m)) =
      cochainBlock _ _ i k h z ≫ (G.incUniversalKoszulScalar r).f k := by
  rw [cochainBlock_apply, cochainBlock_apply, Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
    incUniversalKoszulCochainScalar, extendMap_f _ _ (embeddingUpIntLE_zero_f k)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The scalar of `K_G` commutes with the projection to a summand. -/
theorem incUniversalKoszulScalar_proj (r : IncCoeffRing E) (k : ℕ) (S : Set.powersetCard E k) :
    (G.incUniversalKoszulScalar r).f k ≫ G.exteriorAbelianProj (IncCoeffRing E) k S =
      G.exteriorAbelianProj (IncCoeffRing E) k S ≫
        schemeBaseAbelianScalar (vertexToBase (IncCoeffRing E) V)
          (vertexTwistSheaf (IncCoeffRing E) V (fun v => -(G.deg S v : ℤ))) r :=
  schemeBaseAbelianScalar_naturality _ _ r

/-- **`cechOfCochain` is `S_G`-linear**: postcomposition with the scalar `r` of `K_G` becomes
multiplication by `r` on the Čech–Koszul total module. -/
theorem cechOfCochain_postcomp_scalar {m : ℤ}
    (z : Cochain (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex m) (r : IncCoeffRing E) :
    G.cechOfCochain m (z.comp (Cochain.ofHom (G.incUniversalKoszulCochainScalar r)) (add_zero m)) =
      r • G.cechOfCochain m z := by
  funext S
  rw [Pi.smul_apply, cechOfCochain_apply, cechOfCochain_apply]
  by_cases h : 0 ≤ (S.card : ℤ) + m
  · rw [dite_eq_left h, dite_eq_left h, cochainBlock_postcomp_scalar, Category.assoc,
      incUniversalKoszulScalar_proj, ← Category.assoc, vertexTwistCellNativeEquiv_postcomp_scalar,
      Submodule.coe_smul, smul_comm]
  · rw [dite_eq_right h, dite_eq_right h, smul_zero]

/-- `cocycleZeroToCycles` is `S_G`-linear for postcomposition with the scalars of `K_G`. -/
theorem cocycleZeroToCycles_postcomp_scalar
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex 0) (r : IncCoeffRing E) :
    G.cocycleZeroToCycles (z.postcomp (G.incUniversalKoszulCochainScalar r)) =
      r • G.cocycleZeroToCycles z :=
  Subtype.ext (G.cechOfCochain_postcomp_scalar z.1 r)

end Scalars

section LinearZero

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
variable [HasDerivedCategory.{w}
  (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V)) AddCommGrpCat.{0})]

noncomputable local instance incUniversalKoszulDerivedIncidenceAlgebra :
    Algebra (IncCoeffRing E) G.IncidenceRing :=
  G.coeffHom.toRingHom.toAlgebra

noncomputable local instance incUniversalKoszulLinearHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme (IncCoeffRing E) V))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

noncomputable local instance incUniversalKoszulLinearAugmentationEpi :
    Epi (augmentation (vertexCoordinateOpen (IncCoeffRing E) V)) :=
  augmentation_epi _ (vertexCellChartOpen_cover (IncCoeffRing E) V)

/-- The scalar action on `H^n(K_G)` corresponds to postcomposition of cocycles. -/
theorem incUniversalKoszulHypercohomologyEquiv_postcomp_scalar (n : ℤ)
    (z : Cocycle (negativeComplex (sheafComplex (vertexCoordinateOpen (IncCoeffRing E) V)))
      G.incUniversalKoszulCochainComplex n) (r : IncCoeffRing E) :
    letI := G.incUniversalKoszulHypercohomologyModule n
    G.incUniversalKoszulHypercohomologyEquiv n
        (CohomologyClass.mk (z.postcomp (G.incUniversalKoszulCochainScalar r))) =
      r • G.incUniversalKoszulHypercohomologyEquiv n (CohomologyClass.mk z) := by
  change (cellAugmentationTargetIso (V := V) (E := E)).hom ≫
      derivedCohomologyClassHom _ _ _ _ _ _ n
        (CohomologyClass.mk (z.postcomp (G.incUniversalKoszulCochainScalar r))) =
    ((cellAugmentationTargetIso (V := V) (E := E)).hom ≫
      derivedCohomologyClassHom _ _ _ _ _ _ n (CohomologyClass.mk z)) ≫
      (DerivedCategory.Q.map (G.incUniversalKoszulCochainScalar r))⟦n⟧'
  rw [derivedCohomologyClassHom_postcomp, Category.assoc]

/-- **`H^0(K_G) ≅ 𝒰_G` as `S_G`-modules** (the degree-zero part of Theorem `alg:resolution`),
for the action of `S_G` on `H^0(K_G)` by the scalar endomorphisms of `K_G`
(`incUniversalKoszulHypercohomologyModule`) and on `𝒰_G = IncidenceRing` through
`coeffHom`. -/
noncomputable def incUniversalKoszulHypercohomologyZeroLinearEquiv :
    letI := G.incUniversalKoszulHypercohomologyModule 0
    G.incUniversalKoszulHypercohomology 0 ≃ₗ[IncCoeffRing E] G.IncidenceRing :=
  letI := G.incUniversalKoszulHypercohomologyModule 0
  { G.incUniversalKoszulHypercohomologyZeroEquiv with
    map_smul' := fun r x => by
      obtain ⟨c, rfl⟩ := (G.incUniversalKoszulHypercohomologyEquiv 0).surjective x
      obtain ⟨z, rfl⟩ := c.mk_surjective
      change G.incUniversalKoszulHypercohomologyZeroEquiv _ =
        r • G.incUniversalKoszulHypercohomologyZeroEquiv _
      rw [← G.incUniversalKoszulHypercohomologyEquiv_postcomp_scalar 0 z r]
      simp only [incUniversalKoszulHypercohomologyZeroEquiv, AddEquiv.trans_apply,
        AddEquiv.symm_apply_apply, AddEquiv.ofBijective_apply, cohomologyClassZeroAugmentation_mk,
        cocycleZeroToCycles_postcomp_scalar, map_smul] }

/-- The `S_G`-linear isomorphism has the additive isomorphism as underlying map. -/
theorem incUniversalKoszulHypercohomologyZeroLinearEquiv_apply
    (x : G.incUniversalKoszulHypercohomology 0) :
    letI := G.incUniversalKoszulHypercohomologyModule 0
    G.incUniversalKoszulHypercohomologyZeroLinearEquiv x =
      G.incUniversalKoszulHypercohomologyZeroEquiv x := rfl

end LinearZero

end BPFixedPoints.Multigraph
