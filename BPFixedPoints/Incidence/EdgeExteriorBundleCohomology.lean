import BPFixedPoints.Incidence.EdgeExteriorBundle
import BPFixedPoints.Incidence.VertexProjectiveTwistCellCohomology
import BPFixedPoints.Incidence.VertexProjectiveTwistCohomologyRanks
import BPFixedPoints.Incidence.CycleSpace

/-! # Actual cohomology of the exterior bundle as a product over edge subsets

The forgetful functor to abelian sheaves is additive, so it carries the
biproduct bicone of the exterior bundle to a bilimit bicone of the actual
abelian multi-twists. Actual Ext-defined cohomology commutes with this finite
biproduct, linearly for the original geometric base action. The same
splitting transfers the relative acyclicity of the original cubical cell
resolution from each summand to the whole exterior bundle, and the original
state comparison of each summand gives vanishing above the exterior degree.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory Opposite

variable {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))

/-- The original geometric scalar endomorphisms commute with every actual module-sheaf morphism. -/
@[reassoc] theorem schemeBaseAbelianScalar_naturality {M N : SheafOfModules X.ringCatSheaf}
    (φ : M ⟶ N) (r : R) :
    schemeBaseAbelianScalar f M r ≫ (SheafOfModules.toSheaf X.ringCatSheaf).map φ =
      (SheafOfModules.toSheaf X.ringCatSheaf).map φ ≫ schemeBaseAbelianScalar f N r := by
  apply Sheaf.hom_ext
  ext U s
  exact (φ.val.app U).hom.map_smul (schemeBaseCoefficientAt f U.unop r) s

end BPFixedPoints.SchemeTools

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace ProjectiveLine SchemeTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {V E : Type} [DecidableEq V] [Fintype V] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

noncomputable local instance exteriorBundleHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The image of the exterior biproduct bicone among actual abelian sheaves, with the actual
abelian multi-twists as factors. -/
noncomputable def exteriorBundleAbelianBicone (q : ℕ) :
    Bicone (fun S : Set.powersetCard E q =>
      vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) :=
  (SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).mapBicone
    (biproduct.bicone fun S : Set.powersetCard E q => G.exteriorSummand R S)

/-- The cone point of the abelian exterior bicone is the underlying abelian exterior bundle. -/
theorem exteriorBundleAbelianBicone_pt (q : ℕ) :
    (G.exteriorBundleAbelianBicone R q).pt = G.exteriorBundleAbelian R q := rfl

/-- The underlying abelian exterior bundle is the actual biproduct of the abelian multi-twists. -/
noncomputable def exteriorBundleAbelianBiconeIsBilimit (q : ℕ) :
    (G.exteriorBundleAbelianBicone R q).IsBilimit :=
  isBilimitOfTotal _ (by
    simp only [exteriorBundleAbelianBicone, Functor.mapBicone_π, Functor.mapBicone_ι,
      ← Functor.map_comp]
    rw [← Functor.map_sum, biproduct.total, CategoryTheory.Functor.map_id]
    rfl)

/-- Actual cohomology of the exterior bundle is the product of the actual cohomology of the
multi-twists by minus the multigraph degrees of the `q`-element edge subsets. -/
noncomputable def exteriorBundleCohomologyEquiv (q j : ℕ) :
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃+
      Π S : Set.powersetCard E q,
        Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) j :=
  Ext.addEquivBiproduct _ (G.exteriorBundleAbelianBiconeIsBilimit R q) j

/-- Each component of the splitting is the map induced by the actual biproduct projection. -/
theorem exteriorBundleCohomologyEquiv_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) (S : Set.powersetCard E q) :
    G.exteriorBundleCohomologyEquiv R q j x S =
      Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
        (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)) j x := rfl

/-- The inverse splitting sums the maps induced by the actual biproduct inclusions. -/
theorem exteriorBundleCohomologyEquiv_symm_apply (q j : ℕ)
    (y : Π S : Set.powersetCard E q,
      Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) j) :
    (G.exteriorBundleCohomologyEquiv R q j).symm y =
      ∑ S : Set.powersetCard E q,
        Sheaf.H.map ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
          (biproduct.ι (fun S : Set.powersetCard E q => G.exteriorSummand R S) S)) j (y S) := rfl

/-- The original geometric base action on the actual cohomology of the exterior bundle. -/
@[instance_reducible] noncomputable def exteriorBundleCohomologyModule (q j : ℕ) :
    Module R (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :=
  schemeBaseCohomologyModule (vertexToBase R V) (G.exteriorBundle R q) j

/-- The splitting of the actual exterior cohomology is linear for the original geometric base
actions on the exterior bundle and on every summand. -/
noncomputable def exteriorBundleCohomologyLinearEquiv (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    letI := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R]
      Π S : Set.powersetCard E q,
        Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
  { G.exteriorBundleCohomologyEquiv R q j with
    map_smul' := fun r x => by
      funext S
      change (x.comp (Ext.mk₀ (schemeBaseAbelianScalar (vertexToBase R V) (G.exteriorBundle R q) r))
          (add_zero j)).comp (Ext.mk₀ ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
            (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S))) (add_zero j) =
        (x.comp (Ext.mk₀ ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).map
            (biproduct.π (fun S : Set.powersetCard E q => G.exteriorSummand R S) S))) (add_zero j)).comp
          (Ext.mk₀ (schemeBaseAbelianScalar (vertexToBase R V) (G.exteriorSummand R S) r)) (add_zero j)
      rw [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_second_deg_zero,
        Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, schemeBaseAbelianScalar_naturality] }

/-- The linear splitting has the same underlying map as the additive splitting. -/
theorem exteriorBundleCohomologyLinearEquiv_apply (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :
    G.exteriorBundleCohomologyLinearEquiv R q j x = G.exteriorBundleCohomologyEquiv R q j x := rfl

/-- Actual cohomology of the exterior bundle is, linearly for the original geometric base action,
the product over `q`-element edge subsets of the original state pieces of their degrees. -/
noncomputable def exteriorBundleStateLinearEquiv [IsNoetherianRing R] (q j : ℕ) :
    letI := G.exteriorBundleCohomologyModule R q j
    Sheaf.H.{1} (G.exteriorBundleAbelian R q) j ≃ₗ[R]
      Π S : Set.powersetCard E q, CechProduct.stateDegreePiece R (G.deg S) j :=
  letI := G.exteriorBundleCohomologyModule R q j
  letI := fun S : Set.powersetCard E q => vertexTwistStateCohomologyModule R V (G.deg S) j
  (G.exteriorBundleCohomologyLinearEquiv R q j).trans
    (LinearEquiv.piCongrRight fun S => vertexTwistStateLinearEquiv R V (G.deg S) j)

/-- Each state component of an exterior class is the state of its actual biproduct projection. -/
theorem exteriorBundleStateLinearEquiv_apply [IsNoetherianRing R] (q j : ℕ)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) (S : Set.powersetCard E q) :
    G.exteriorBundleStateLinearEquiv R q j x S =
      vertexTwistStateLinearEquiv R V (G.deg S) j (G.exteriorBundleCohomologyEquiv R q j x S) := rfl

/-- The actual exterior bundle is acyclic for every term of the original cubical cell resolution. -/
theorem exteriorBundle_terms_acyclic [IsNoetherianRing R] (q : ℕ) :
    ExtResolutionTools.ComplexAcyclicAgainst
      (SheafTools.BinaryCells.sheafComplex (vertexCoordinateOpen R V))
      (G.exteriorBundleAbelian R q) := by
  intro n k x
  let e := Ext.addEquivBiproduct ((SheafTools.BinaryCells.sheafComplex (vertexCoordinateOpen R V)).X n)
    (G.exteriorBundleAbelianBiconeIsBilimit R q) (k+1)
  apply e.injective
  rw [map_zero]
  funext S
  exact vertexTwistCellSheaf_terms_acyclic R V (fun v => -(G.deg S v : ℤ)) n k (e x S)

/-- The original geometric base action on the original cubical cell Hom cohomology of the
exterior bundle. -/
@[instance_reducible] noncomputable def exteriorBundleCellModule (q n : ℕ) :
    Module R (SheafTools.BinaryCells.cubicalCohomology (vertexCoordinateOpen R V)
      (G.exteriorBundleAbelian R q) n) :=
  schemeBaseCubicalModule (vertexToBase R V) (G.exteriorBundle R q) (vertexCoordinateOpen R V) n

/-- Original cubical cell Hom cohomology of the exterior bundle computes its actual positive
cohomology, linearly for the original geometric base action. -/
noncomputable def exteriorBundleCellActualLinearEquiv [IsNoetherianRing R] (q n : ℕ) :
    letI := G.exteriorBundleCellModule R q n
    letI := G.exteriorBundleCohomologyModule R q (n+1)
    SheafTools.BinaryCells.cubicalCohomology (vertexCoordinateOpen R V) (G.exteriorBundleAbelian R q) n ≃ₗ[R]
      Sheaf.H.{1} (G.exteriorBundleAbelian R q) (n+1) :=
  schemeBaseFiniteCubicalActualLinearEquiv (vertexToBase R V) (G.exteriorBundle R q)
    (vertexCoordinateOpen R V) (vertexCellChartOpen_cover R V) (G.exteriorBundle_terms_acyclic R q) n

/-- Each summand of the `q`-th exterior bundle has vanishing actual cohomology above degree `q`. -/
theorem exteriorSummand_cohomology_eq_zero_of_lt [IsNoetherianRing R] {q j : ℕ} (h : q < j)
    (S : Set.powersetCard E q)
    (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(G.deg S v : ℤ))) j) : x = 0 := by
  classical
  by_cases hS : G.IsContributing S
  · apply vertexTwistCohomology_eq_zero_off_degree R V (G.deg S) j
    have hc : CechProduct.cohomologyDegree (G.deg S) = (G.support S).card :=
      CechProduct.cohomologyDegree_eq_card _
    have hle := G.card_support_le_of_isContributing hS
    rw [Set.powersetCard.card_eq S] at hle
    omega
  · obtain ⟨v, hv⟩ : ∃ v, G.deg S v = 1 := by
      simpa [IsContributing] using hS
    exact vertexTwistCohomology_eq_zero_of_one R V (G.deg S) v hv j x

/-- The actual cohomology of the `q`-th exterior bundle vanishes in every degree above `q`. -/
theorem exteriorBundleCohomology_eq_zero_of_lt [IsNoetherianRing R] {q j : ℕ} (h : q < j)
    (x : Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) : x = 0 := by
  apply (G.exteriorBundleCohomologyEquiv R q j).injective
  rw [map_zero]
  funext S
  exact G.exteriorSummand_cohomology_eq_zero_of_lt R h S _

/-- The actual cohomology of the `q`-th exterior bundle is trivial in every degree above `q`. -/
theorem exteriorBundleCohomology_subsingleton_of_lt [IsNoetherianRing R] {q j : ℕ} (h : q < j) :
    Subsingleton (Sheaf.H.{1} (G.exteriorBundleAbelian R q) j) :=
  subsingleton_of_forall_eq 0 (G.exteriorBundleCohomology_eq_zero_of_lt R h)

end BPFixedPoints.Multigraph
