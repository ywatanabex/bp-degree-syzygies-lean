import BPFixedPoints.Incidence.EdgeExteriorPairingBridge
import BPFixedPoints.Incidence.VertexProjectiveTwistPairCoefficients

/-! # Degree zero of the chart identification of the exterior bundle

The untwisted multi-twist `L(0)` has a unit section on every open: on each product chart the
section with chart coefficient one, and these agree on the pair overlaps because the original
transition functions of twist zero are one, so they glue to a global section, which is
restricted to every open. Its chart coefficient on every subopen of a chart is one.

The degree-zero section-level exterior wedge sends `r ∈ ⋀^0 = Γ(X, W)` to `r` times the unit
section in the summand of the empty edge subset. Together with the section-level exterior wedge
of positive degrees it gives a wedge map in every degree. It commutes with restriction, on every
subopen of a product chart it sends Mathlib's exterior power basis of the chart frame to the chart
frame basis of the exterior bundle and so is bijective there, and both the section exterior
pairing and the sheaf pairing defining the exterior cohomology product send wedges of degrees
`p` and `q` to the wedge of the concatenated tuple, for all `p` and `q` including zero.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (R : Type) [CommRing R]

/-- The original overlap transition unit of the untwisted line sheaf is one. -/
theorem twistOverlapUnit_zero : twistOverlapUnit R 0 = 1 := by
  have h := twistOverlapUnit_add R 0 0
  rw [add_zero] at h
  exact mul_eq_left.mp h.symm

/-- All original pair transition units of the untwisted line sheaf are one. -/
theorem twistSheafPairUnit_zero (i j : Fin 2) : twistSheafPairUnit R 0 i j = 1 := by
  fin_cases i <;> fin_cases j
  · rfl
  · exact twistOverlapUnit_zero R
  · change (twistOverlapUnit R 0)⁻¹ = 1
    rw [twistOverlapUnit_zero, inv_one]
  · rfl

variable (V : Type) [Fintype V]

/-- The original pair transition unit of the untwisted multi-twist is one. -/
theorem vertexTwistSheafPairUnit_zero (σ τ : V → Fin 2) : vertexTwistSheafPairUnit R V 0 σ τ = 1 := by
  rw [vertexTwistSheafPairUnit]
  refine Finset.prod_eq_one fun v _ => ?_
  rw [vertexTwistPairFactorUnit, Pi.zero_apply, twistSheafPairUnit_zero, map_one]

/-- The transition coefficient of the untwisted multi-twist on every pair subopen is one. -/
theorem vertexTwistSheafPairTransitionCoefficient_zero (σ τ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartPairOpen R V σ τ) :
    vertexTwistSheafPairTransitionCoefficient R V 0 σ τ W hW = 1 := by
  rw [vertexTwistSheafPairTransitionCoefficient, vertexTwistSheafPairUnit_zero, Units.val_one]
  exact SheafTools.moduleOverMultiplicationCoefficient_one _ _ _

/-- On a subopen of a product chart, sections of a multi-twist are determined by their chart
coefficient. -/
theorem vertexTwistSheafChartCoefficient_injective (a : V → ℤ) (σ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ) :
    Function.Injective (vertexTwistSheafChartCoefficient R V a σ W hW) :=
  (vertexTwistChartCoefficientEquiv R V a σ W hW).injective

/-- On a product chart, the section of the untwisted multi-twist with chart coefficient one. -/
noncomputable def vertexTwistZeroChartUnit (σ : V → Fin 2) :
    Γ(vertexTwistSheaf R V 0, vertexChartOpen R V σ) :=
  (vertexTwistChartCoefficientEquiv R V 0 σ (vertexChartOpen R V σ) le_rfl).symm 1

/-- The chart unit has chart coefficient one. -/
theorem vertexTwistZeroChartUnit_coefficient (σ : V → Fin 2) :
    vertexTwistSheafChartCoefficient R V 0 σ (vertexChartOpen R V σ) le_rfl
      (vertexTwistZeroChartUnit R V σ) = 1 :=
  (vertexTwistChartCoefficientEquiv R V 0 σ (vertexChartOpen R V σ) le_rfl).apply_symm_apply 1

/-- The chart units agree on the pair overlaps. -/
theorem vertexTwistZeroChartUnit_compatible :
    TopCat.Presheaf.IsCompatible (vertexTwistSheaf R V 0).presheaf (vertexChartOpen R V)
      (vertexTwistZeroChartUnit R V) := by
  intro σ τ
  apply vertexTwistSheafChartCoefficient_injective R V 0 σ (vertexChartPairOpen R V σ τ) inf_le_left
  have hl := vertexTwistSheafChartCoefficient_restrict R V 0 σ (W := vertexChartPairOpen R V σ τ)
    (U := vertexChartOpen R V σ) inf_le_left le_rfl (vertexTwistZeroChartUnit R V σ)
  have hr := vertexTwistSheafChartCoefficient_restrict R V 0 τ (W := vertexChartPairOpen R V σ τ)
    (U := vertexChartOpen R V τ) inf_le_right le_rfl (vertexTwistZeroChartUnit R V τ)
  have ht := vertexTwistSheafChartCoefficient_pair_transition R V 0 σ τ (vertexChartPairOpen R V σ τ) le_rfl
    ((vertexTwistSheaf R V 0).presheaf.map (homOfLE inf_le_right).op (vertexTwistZeroChartUnit R V τ))
  rw [vertexTwistZeroChartUnit_coefficient, map_one] at hl hr
  rw [vertexTwistSheafPairTransitionCoefficient_zero, mul_one] at ht
  exact hl.trans (ht.trans hr).symm

/-- The chart units glue to a unique global section. -/
theorem vertexTwistZeroChartUnit_existsUnique_gluing :
    ∃! s : Γ(vertexTwistSheaf R V 0, ⊤), ∀ σ : V → Fin 2,
      (vertexTwistSheaf R V 0).presheaf.map (homOfLE le_top : vertexChartOpen R V σ ⟶ ⊤).op s =
        vertexTwistZeroChartUnit R V σ :=
  TopCat.Sheaf.existsUnique_gluing' ⟨(vertexTwistSheaf R V 0).presheaf, Scheme.Modules.isSheaf _⟩
    (vertexChartOpen R V) ⊤ (fun σ => homOfLE le_top)
    (fun x _ => by
      obtain ⟨σ, y, hy⟩ := vertexChart_covers R V x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨σ, ⟨y, hy⟩⟩)
    (vertexTwistZeroChartUnit R V) (vertexTwistZeroChartUnit_compatible R V)

/-- The global unit section of the untwisted multi-twist: the gluing of the chart units. -/
noncomputable def vertexTwistZeroGlobalUnit : Γ(vertexTwistSheaf R V 0, ⊤) :=
  (vertexTwistZeroChartUnit_existsUnique_gluing R V).exists.choose

/-- The global unit section restricts to the chart unit on every product chart. -/
theorem vertexTwistZeroGlobalUnit_restrict (σ : V → Fin 2) :
    (vertexTwistSheaf R V 0).presheaf.map (homOfLE le_top : vertexChartOpen R V σ ⟶ ⊤).op
      (vertexTwistZeroGlobalUnit R V) = vertexTwistZeroChartUnit R V σ :=
  (vertexTwistZeroChartUnit_existsUnique_gluing R V).exists.choose_spec σ

/-- The unit section of the untwisted multi-twist on an open: the restriction of the global unit
section. -/
noncomputable def vertexTwistZeroUnit (W : (vertexScheme R V).Opens) : Γ(vertexTwistSheaf R V 0, W) :=
  (vertexTwistSheaf R V 0).presheaf.map (homOfLE le_top : W ⟶ ⊤).op (vertexTwistZeroGlobalUnit R V)

/-- Restriction of sections of a sheaf of modules along two inclusions of opens is restriction
along the composite inclusion. -/
theorem vertexModules_restrict_restrict (M : (vertexScheme R V).Modules) {W U U' : (vertexScheme R V).Opens}
    (i : W ⟶ U) (j : U ⟶ U') (k : W ⟶ U') (x : Γ(M, U')) :
    M.presheaf.map i.op (M.presheaf.map j.op x) = M.presheaf.map k.op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The unit sections commute with restriction. -/
theorem vertexTwistZeroUnit_restrict {W U : (vertexScheme R V).Opens} (i : W ⟶ U) :
    (vertexTwistSheaf R V 0).presheaf.map i.op (vertexTwistZeroUnit R V U) = vertexTwistZeroUnit R V W :=
  vertexModules_restrict_restrict R V _ i _ _ _

/-- On every subopen of a product chart, the unit section has chart coefficient one. -/
theorem vertexTwistZeroUnit_chart (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) :
    vertexTwistSheafChartCoefficient R V 0 σ W hW (vertexTwistZeroUnit R V W) = 1 := by
  have hu : vertexTwistZeroUnit R V W =
      (vertexTwistSheaf R V 0).presheaf.map (homOfLE hW).op (vertexTwistZeroChartUnit R V σ) := by
    rw [← vertexTwistZeroGlobalUnit_restrict R V σ]
    exact (vertexModules_restrict_restrict R V _ _ _ _ _).symm
  rw [hu]
  refine (vertexTwistSheafChartCoefficient_restrict R V 0 σ hW le_rfl _).trans ?_
  rw [vertexTwistZeroChartUnit_coefficient, map_one]

end BPFixedPoints.ProjectiveLine

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ProjectiveLine
open Set.powersetCard SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars true

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E] (G : Multigraph V E)
variable (R : Type) [CommRing R]

omit [Fintype V] [LinearOrder E] [Fintype E] in
/-- The empty edge subset has twist zero. -/
theorem exteriorTwist_empty :
    (0 : V → ℤ) = fun v => -(G.deg ((emptyEdgeSubset : Set.powersetCard E 0) : Finset E) v : ℤ) := by
  funext v
  simp

/-- The unit section of the zeroth exterior bundle: the unit section of the untwisted multi-twist
in the summand of the empty edge subset. -/
noncomputable def exteriorSectionUnit (W : (vertexScheme R V).Opens) : Γ(G.exteriorBundle R 0, W) :=
  G.exteriorSectionInclusion R 0 W emptyEdgeSubset
    (vertexTwistCast R (G.exteriorTwist_empty) W (vertexTwistZeroUnit R V W))

omit [LinearOrder E] in
/-- The unit sections of the zeroth exterior bundle commute with restriction. -/
theorem exteriorSectionUnit_restrict {W U : (vertexScheme R V).Opens} (i : W ⟶ U) :
    (Scheme.Modules.presheaf (G.exteriorBundle R 0)).map i.op (G.exteriorSectionUnit R U) =
      G.exteriorSectionUnit R W := by
  rw [exteriorSectionUnit, exteriorSectionInclusion_restrict]
  exact congrArg _ ((vertexTwistCast_restrict _ i _).trans
    (congrArg _ (vertexTwistZeroUnit_restrict R V i)))

/-- On a chart, the coordinate of the unit section on the empty edge subset is one. -/
theorem exteriorChartCoordinates_unit (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) (T : Set.powersetCard E 0) :
    G.exteriorChartCoordinates R σ W hW 0 (G.exteriorSectionUnit R W) T = 1 := by
  obtain rfl : T = emptyEdgeSubset := Subsingleton.elim _ _
  rw [exteriorSectionUnit, exteriorChartCoordinates_inclusion_self, vertexTwistCast_chart,
    vertexTwistZeroUnit_chart]

/-- The degree-zero section-level exterior wedge: the map from `⋀^0 = Γ(X, W)` to the sections
of the zeroth exterior bundle sending a function to its multiple of the unit section. -/
noncomputable def exteriorSectionWedgeZero (W : (vertexScheme R V).Opens) :
    ⋀[Γ(vertexScheme R V, W)]^0 Γ(G.edgeDualBundle R, W) →ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorBundle R 0, W) :=
  (LinearMap.toSpanSingleton Γ(vertexScheme R V, W) _ (G.exteriorSectionUnit R W)).comp
    (exteriorPower.zeroEquiv Γ(vertexScheme R V, W) Γ(G.edgeDualBundle R, W)).toLinearMap

omit [LinearOrder E] in
/-- The degree-zero wedge is the identification `⋀^0 = Γ(X, W)` times the unit section. -/
theorem exteriorSectionWedgeZero_apply (W : (vertexScheme R V).Opens)
    (z : ⋀[Γ(vertexScheme R V, W)]^0 Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionWedgeZero R W z =
      exteriorPower.zeroEquiv Γ(vertexScheme R V, W) Γ(G.edgeDualBundle R, W) z • G.exteriorSectionUnit R W :=
  rfl

omit [LinearOrder E] in
/-- The degree-zero wedge of the empty tuple is the unit section. -/
theorem exteriorSectionWedgeZero_ιMulti (W : (vertexScheme R V).Opens) (x : Fin 0 → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionWedgeZero R W (exteriorPower.ιMulti _ 0 x) = G.exteriorSectionUnit R W := by
  rw [exteriorSectionWedgeZero_apply, exteriorPower.zeroEquiv_ιMulti, one_smul]

/-- The section-level exterior wedge in every degree: the degree-zero wedge in degree zero and
the section-level exterior wedge in positive degrees. -/
noncomputable def exteriorSectionWedgeAll : (n : ℕ) → (W : (vertexScheme R V).Opens) →
    ⋀[Γ(vertexScheme R V, W)]^n Γ(G.edgeDualBundle R, W) →ₗ[Γ(vertexScheme R V, W)]
      Γ(G.exteriorBundle R n, W)
  | 0, W => G.exteriorSectionWedgeZero R W
  | q + 1, W => G.exteriorSectionWedge R q W

/-- In degree zero the wedge in every degree is the degree-zero wedge. -/
theorem exteriorSectionWedgeAll_zero (W : (vertexScheme R V).Opens) :
    G.exteriorSectionWedgeAll R 0 W = G.exteriorSectionWedgeZero R W := rfl

/-- In positive degrees the wedge in every degree is the section-level exterior wedge. -/
theorem exteriorSectionWedgeAll_succ (q : ℕ) (W : (vertexScheme R V).Opens) :
    G.exteriorSectionWedgeAll R (q + 1) W = G.exteriorSectionWedge R q W := rfl

/-- The wedge in every degree commutes with restriction to smaller opens. -/
theorem exteriorSectionWedgeAll_restrict (n : ℕ) {W U : (vertexScheme R V).Opens} (i : W ⟶ U)
    (x : Fin n → Γ(G.edgeDualBundle R, U)) :
    (Scheme.Modules.presheaf (G.exteriorBundle R n)).map i.op
        (G.exteriorSectionWedgeAll R n U (exteriorPower.ιMulti _ n x)) =
      G.exteriorSectionWedgeAll R n W (exteriorPower.ιMulti _ n
        fun k => (Scheme.Modules.presheaf (G.edgeDualBundle R)).map i.op (x k)) := by
  cases n with
  | zero =>
    rw [exteriorSectionWedgeAll_zero, exteriorSectionWedgeAll_zero, exteriorSectionWedgeZero_ιMulti,
      exteriorSectionWedgeZero_ιMulti, exteriorSectionUnit_restrict]
  | succ q => exact G.exteriorSectionWedge_restrict R q i x

section Chart

variable (σ : V → Fin 2) (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartOpen R V σ)

/-- On a chart, the coordinate of the degree-zero wedge is the coordinate in the exterior power
basis of the chart frame. -/
theorem exteriorChartCoordinates_wedgeZero (z : ⋀[Γ(vertexScheme R V, W)]^0 Γ(G.edgeDualBundle R, W))
    (T : Set.powersetCard E 0) :
    G.exteriorChartCoordinates R σ W hW 0 (G.exteriorSectionWedgeZero R W z) T =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower 0).repr z T := by
  have h : (LinearMap.proj T).comp ((G.exteriorChartCoordinates R σ W hW 0).toLinearMap.comp
      (G.exteriorSectionWedgeZero R W)) = ((G.edgeDualChartBasis R σ W hW).exteriorPower 0).coord T := by
    apply exteriorPower.linearMap_ext
    ext x
    change G.exteriorChartCoordinates R σ W hW 0 (G.exteriorSectionWedgeZero R W (exteriorPower.ιMulti _ 0 x)) T =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower 0).repr (exteriorPower.ιMulti _ 0 x) T
    rw [exteriorSectionWedgeZero_ιMulti, exteriorChartCoordinates_unit, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, Matrix.det_isEmpty]
  exact LinearMap.congr_fun h z

/-- On a chart, the coordinates of the wedge in every degree are the coordinates in the exterior
power basis of the chart frame. -/
theorem exteriorChartCoordinates_wedgeAll (n : ℕ)
    (z : ⋀[Γ(vertexScheme R V, W)]^n Γ(G.edgeDualBundle R, W)) (T : Set.powersetCard E n) :
    G.exteriorChartCoordinates R σ W hW n (G.exteriorSectionWedgeAll R n W z) T =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower n).repr z T := by
  cases n with
  | zero => exact G.exteriorChartCoordinates_wedgeZero R σ W hW z T
  | succ q => exact G.exteriorChartCoordinates_wedge R σ W hW q z T

/-- On a chart, the wedge in every degree is the linear equivalence matching the exterior power
basis of the chart frame with the chart frame basis of the exterior bundle. -/
theorem exteriorSectionWedgeAll_eq_basisEquiv (n : ℕ)
    (z : ⋀[Γ(vertexScheme R V, W)]^n Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionWedgeAll R n W z =
      (((G.edgeDualChartBasis R σ W hW).exteriorPower n).repr.trans
        (G.exteriorChartBasis R σ W hW n).repr.symm) z := by
  apply (G.exteriorChartBasis R σ W hW n).repr.injective
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  ext T
  rw [exteriorChartBasis, Module.Basis.ofEquivFun_repr_apply, exteriorChartCoordinates_wedgeAll]

/-- On a chart, the wedge in every degree sends the exterior power basis of the chart frame to
the chart frame basis of the exterior bundle. -/
theorem exteriorSectionWedgeAll_basis (n : ℕ) (S : Set.powersetCard E n) :
    G.exteriorSectionWedgeAll R n W ((G.edgeDualChartBasis R σ W hW).exteriorPower n S) =
      G.exteriorChartBasis R σ W hW n S := by
  rw [exteriorSectionWedgeAll_eq_basisEquiv, LinearEquiv.trans_apply, Module.Basis.repr_self,
    Module.Basis.repr_symm_single, one_smul]

end Chart

/-- On every subopen of a product chart, the wedge in every degree is bijective. -/
theorem exteriorSectionWedgeAll_bijective (n : ℕ) (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) : Function.Bijective (G.exteriorSectionWedgeAll R n W) := by
  have h : ⇑(G.exteriorSectionWedgeAll R n W) =
      ((G.edgeDualChartBasis R σ W hW).exteriorPower n).repr.trans
        (G.exteriorChartBasis R σ W hW n).repr.symm :=
    funext fun z => G.exteriorSectionWedgeAll_eq_basisEquiv R σ W hW n z
  rw [h]
  exact LinearEquiv.bijective _

/-- On every subopen of a product chart, the degree-zero wedge is bijective. -/
theorem exteriorSectionWedgeZero_bijective (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) : Function.Bijective (G.exteriorSectionWedgeZero R W) :=
  G.exteriorSectionWedgeAll_bijective R 0 σ W hW

/-- On a chart, the section exterior pairing of two wedges of arbitrary degrees is the wedge of
the concatenated tuple. -/
theorem exteriorSectionPairing_wedgeAll_of_le (p q : ℕ) (σ : V → Fin 2) (W : (vertexScheme R V).Opens)
    (hW : W ≤ vertexChartOpen R V σ) (x : Fin p → Γ(G.edgeDualBundle R, W))
    (y : Fin q → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionPairing R p q W (G.exteriorSectionWedgeAll R p W (exteriorPower.ιMulti _ p x))
        (G.exteriorSectionWedgeAll R q W (exteriorPower.ιMulti _ q y)) =
      G.exteriorSectionWedgeAll R (p + q) W (exteriorPower.ιMulti _ (p + q) (Fin.append x y)) := by
  apply (G.exteriorChartCoordinates R σ W hW (p + q)).injective
  funext U
  rw [exteriorChartCoordinates_pairing]
  refine Eq.trans ?_ (G.exteriorChartCoordinates_wedgeAll R σ W hW (p + q) _ U).symm
  refine Eq.trans ?_ (Koszul.exteriorPower_basis_repr_ιMulti_append (G.edgeDualChartBasis R σ W hW) x y U).symm
  simp only [exteriorChartCoordinates_wedgeAll]

/-- On every open, the section exterior pairing of two wedges of arbitrary degrees, zero included,
is the wedge of the concatenated tuple. -/
theorem exteriorSectionPairing_wedgeAll (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin p → Γ(G.edgeDualBundle R, W)) (y : Fin q → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionPairing R p q W (G.exteriorSectionWedgeAll R p W (exteriorPower.ιMulti _ p x))
        (G.exteriorSectionWedgeAll R q W (exteriorPower.ιMulti _ q y)) =
      G.exteriorSectionWedgeAll R (p + q) W (exteriorPower.ιMulti _ (p + q) (Fin.append x y)) := by
  apply vertexSections_ext_of_charts (G.exteriorBundle R (p + q)) W
  intro σ
  rw [exteriorSectionPairing_restrict, exteriorSectionWedgeAll_restrict, exteriorSectionWedgeAll_restrict,
    G.exteriorSectionPairing_wedgeAll_of_le R p q σ _ inf_le_right]
  refine Eq.trans ?_ (G.exteriorSectionWedgeAll_restrict R (p + q) _ _).symm
  congr 2
  funext k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · simp only [Fin.append_left]
  · simp only [Fin.append_right]

/-- On every open, the degree-zero wedge of the empty tuple is a left unit for the section
exterior pairing with wedges of any degree. -/
theorem exteriorSectionPairing_wedgeZero_left (q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin 0 → Γ(G.edgeDualBundle R, W)) (y : Fin q → Γ(G.edgeDualBundle R, W)) :
    G.exteriorSectionPairing R 0 q W (G.exteriorSectionWedgeZero R W (exteriorPower.ιMulti _ 0 x))
        (G.exteriorSectionWedgeAll R q W (exteriorPower.ιMulti _ q y)) =
      G.exteriorSectionWedgeAll R (0 + q) W (exteriorPower.ιMulti _ (0 + q) (Fin.append x y)) :=
  G.exteriorSectionPairing_wedgeAll R 0 q W x y

/-- On sections over any open, the sheaf pairing of the exterior product sends wedges of
arbitrary degrees, zero included, to the wedge of the concatenated tuple. -/
theorem exteriorWedgePairing_wedgeAll (p q : ℕ) (W : (vertexScheme R V).Opens)
    (x : Fin p → Γ(G.edgeDualBundle R, W)) (y : Fin q → Γ(G.edgeDualBundle R, W)) :
    (G.exteriorWedgePairing R p q).pairing W
        (G.exteriorSectionWedgeAll R p W (exteriorPower.ιMulti _ p x))
        (G.exteriorSectionWedgeAll R q W (exteriorPower.ιMulti _ q y)) =
      G.exteriorSectionWedgeAll R (p + q) W (exteriorPower.ιMulti _ (p + q) (Fin.append x y)) :=
  (G.exteriorWedgePairing_eq_sectionPairing R p q W _ _).trans (G.exteriorSectionPairing_wedgeAll R p q W x y)

end BPFixedPoints.Multigraph
