import BPFixedPoints.Incidence.IncidenceKernelSheafEvaluation
import BPFixedPoints.Incidence.IncidenceKernelBundleTrivialization

/-! # The kernel sheaf of the incidence evaluation map is locally free of rank `3m`

This file continues `IncidenceKernelSheafEvaluation.lean` (Lemma `alg:incidence-vector-bundle`,
supplement section `supp:vector-bundle`). The kernel bundle `K_G = incKernelSheaf` is Mathlib's
kernel of the evaluation map `incEvaluationSheafMap : O^{4m} ⟶ F_G` in the abelian category of
sheaves of modules on `X_G = vertexScheme ℂ V`.

* **Sections and restriction.** The inclusion `K_G → O^{4m}` is injective on sections with image
  the sections killed by the evaluation map (`incKernelSheafι_app_injective`,
  `incKernelSheafι_app_exists`); on every subopen `W` of a chart `σ` the sections of `K_G` are
  the kernel of the chart evaluation map at the chart point
  (`incKernelSheafChartSectionsEquiv`). For every open `U`, the restriction of `K_G` to `U` is
  Mathlib's kernel of the restricted evaluation map (`incKernelSheafOverIso`, from
  `isLimit_kernelFork_over` of `IncidenceKernelSheafSections.lean`).
* **Free of rank `3m` on charts.** On the chart open of `σ`, the restriction of `K_G` is
  isomorphic to `O^{3m} = overFreeSheaf (incChartOpen V σ) (E × Fin 3)`
  (`incKernelChartIso`): the forward map reads the non-unit coefficients
  `c_{e, incChartFreeIdx σ e i}`, the inverse is the kernel extension of chart `σ` (a matrix of
  functions on the chart, `incKernelExtendOver`), lifted through the kernel. The kernel extension
  is itself a kernel of the restricted evaluation map (`incKernelExtendOver_isLimit`). Hence
  `K_G` is locally free in Mathlib's sense (`incKernelSheaf_isLocallyFree`) and quasicoherent.
* **Kernel coordinates.** On every subopen of chart `σ` the trivialization is the chart kernel
  coordinate map `incChartEvaluationKernelEquivFree σ` (`incKernelChartIso_chart`); on the face
  open of a face `r` refined by `σ`, in face coordinates, it is `κ_σ = incOverlapKernelCoord hσ`
  of `IncidenceKernelBundleTransitions.lean` (`incKernelChartFaceCoord_eq`).
* **Transitions.** On a face refined by charts `σ` and `τ` the transition `Φ_τ ∘ Φ_σ⁻¹` of
  these trivializations is `incKernelTransition hσ hτ` (`incKernelChartFaceCoord_transition`,
  `incKernelSheafTransition_eq`), so the transitions of the trivializations `incFaceKernelTriv`
  of `Z_G` are the linear substitutions `Sym(g^∨)` given by the transitions of `K_G`
  (`incFaceKernelTriv_transition_kernelSheaf`).

Not constructed here: the relative spectrum of the symmetric algebra of the dual of `K_G` as a
scheme over `X_G` and its identification with `Z_G` as schemes; the comparison with `Z_G` is
through the chart and face coordinate rings of `IncidenceKernelBundleTrivialization.lean`. The
surjectivity of the evaluation map as a morphism of sheaves is not proved.
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CechProduct ProjectiveLine SheafTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option linter.unusedSectionVars false

/-! ### Linear maps on sections -/

section SectionMaps

variable {X : Scheme.{0}}

/-- A morphism of sheaves of modules on a scheme, on the sections over `W`, as a linear map over
the functions on `W`. -/
noncomputable def schemeSectionsMap {M N : SheafOfModules X.ringCatSheaf} (f : M ⟶ N)
    (W : X.Opens) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun := (f.val.app (op W)).hom
  map_add' := (f.val.app (op W)).hom.map_add
  map_smul' := (f.val.app (op W)).hom.map_smul

/-- The linear map on sections applies the morphism. -/
@[simp] theorem schemeSectionsMap_apply {M N : SheafOfModules X.ringCatSheaf} (f : M ⟶ N)
    (W : X.Opens) (x : Γ(M, W)) : schemeSectionsMap f W x = (f.val.app (op W)).hom x :=
  rfl

/-- Finite biproducts of sheaves of modules on a scheme. -/
instance schemeSheafOfModules_hasFiniteBiproducts :
    HasFiniteBiproducts (SheafOfModules X.ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Finite biproducts of sheaves of modules on the over-site of an open. -/
instance overSheafOfModules_hasFiniteBiproducts (U : X.Opens) :
    HasFiniteBiproducts (SheafOfModules (X.ringCatSheaf.over U)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The free sheaf of modules of rank `J` on the over-site of an open `U`. -/
noncomputable abbrev overFreeSheaf (U : X.Opens) (J : Type) [Fintype J] : SheafOfModules (X.ringCatSheaf.over U) :=
  ⨁ fun _ : J => SheafOfModules.unit (X.ringCatSheaf.over U)

/-- The morphism from the free sheaf of rank `J` on the over-site of `U` to the restriction to
`U` of the free sheaf of rank `I` on `X`, given by a matrix of functions on `U`. -/
noncomputable def overFreeMatrix (U : X.Opens) {I J : Type} [Fintype I] [Fintype J]
    (A : I → J → Γ(X, U)) :
    overFreeSheaf U J ⟶ (SheafOfModules.overFunctor X.ringCatSheaf U).obj
      (⨁ fun _ : I => SheafOfModules.unit X.ringCatSheaf) :=
  biproduct.desc fun j => ∑ i, moduleOverMultiplication X U (U.topIso.inv (A i j)) ≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).map
      (biproduct.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i)

/-- On sections over `S`, the matrix morphism multiplies the coordinates by the restricted
matrix. -/
theorem overFreeMatrix_app (U : X.Opens) {I J : Type} [Fintype I] [Fintype J]
    (A : I → J → Γ(X, U)) (S : Over U) (y : (overFreeSheaf U J).val.obj (op S)) (i : I) :
    ((biproduct.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app (op S.left)).hom
        (((overFreeMatrix U A).val.app (op S)).hom y) =
      ∑ j, (show Γ(X, S.left) from
        ((biproduct.π (fun _ : J => SheafOfModules.unit (X.ringCatSheaf.over U)) j).val.app
          (op S)).hom y) * X.presheaf.map S.hom.op (A i j) := by
  rw [overFreeMatrix, biproduct_desc_app, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sheafOfModules_sum_app_apply, map_sum]
  rw [Finset.sum_eq_single i]
  · change ((biproduct.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app (op S.left)).hom
      (((biproduct.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app (op S.left)).hom
        (((moduleOverMultiplication X U (U.topIso.inv (A i j))).val.app (op S)).hom _)) = _
    rw [biproduct_ι_π_app_self]
    change (show Γ(X, S.left) from ((moduleOverMultiplication X U (U.topIso.inv (A i j))).val.app
      (op S)).hom _) = _
    rw [moduleOverMultiplication_app, moduleOverMultiplicationCoefficient_geometric,
      Iso.inv_hom_id_apply]
  · intro i' _ hi'
    change ((biproduct.π (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i).val.app (op S.left)).hom
      (((biproduct.ι (fun _ : I => SheafOfModules.unit X.ringCatSheaf) i').val.app (op S.left)).hom
        _) = 0
    exact biproduct_ι_π_app_ne _ hi' _ _
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end SectionMaps

section Main

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-! ### The kernel sheaf and its sections -/

section Kernel

/-- **The kernel bundle `K_G`**: Mathlib's kernel of the evaluation map `O^{4m} → F_G` in the
abelian category of sheaves of modules on `X_G`. -/
noncomputable def incKernelSheaf : SheafOfModules (vertexScheme ℂ V).ringCatSheaf :=
  kernel G.incEvaluationSheafMap

/-- The inclusion `K_G → O^{4m}`. -/
noncomputable def incKernelSheafι : G.incKernelSheaf ⟶ incCoeffSheaf V E :=
  kernel.ι G.incEvaluationSheafMap

/-- The inclusion of `K_G` followed by the evaluation map is zero. -/
@[reassoc (attr := simp)] theorem incKernelSheafι_comp :
    G.incKernelSheafι ≫ G.incEvaluationSheafMap = 0 :=
  kernel.condition _

/-- The inclusion of `K_G` is injective on sections. -/
theorem incKernelSheafι_app_injective (W : (vertexScheme ℂ V).Opens) :
    Function.Injective (G.incKernelSheafι.val.app (op W)).hom :=
  kernel_ι_app_injective _ _

/-- The evaluation map kills the sections of `K_G`. -/
theorem incKernelSheafι_app_eval (W : (vertexScheme ℂ V).Opens) (k : Γ(G.incKernelSheaf, W)) :
    (G.incEvaluationSheafMap.val.app (op W)).hom ((G.incKernelSheafι.val.app (op W)).hom k) = 0 :=
  kernel_ι_app_comp _ _ k

/-- Every section of `O^{4m}` killed by the evaluation map is a section of `K_G`. -/
theorem incKernelSheafι_app_exists (W : (vertexScheme ℂ V).Opens) (x : Γ(incCoeffSheaf V E, W))
    (hx : (G.incEvaluationSheafMap.val.app (op W)).hom x = 0) :
    ∃ k : Γ(G.incKernelSheaf, W), (G.incKernelSheafι.val.app (op W)).hom k = x :=
  kernel_ι_app_exists _ _ x hx

/-- **Restriction preserves the kernel.** For every open `U` of `X_G`, the restriction of `K_G`
to `U` is Mathlib's kernel of the restriction of the evaluation map to `U`. -/
noncomputable def incKernelSheafOverIso (U : (vertexScheme ℂ V).Opens) :
    (SheafOfModules.overFunctor _ U).obj G.incKernelSheaf ≅
      kernel ((SheafOfModules.overFunctor _ U).map G.incEvaluationSheafMap) :=
  kernelOverIso U G.incEvaluationSheafMap

/-- The restriction comparison of kernels commutes with the inclusions into `O^{4m}`. -/
@[reassoc (attr := simp)] theorem incKernelSheafOverIso_hom_ι (U : (vertexScheme ℂ V).Opens) :
    (G.incKernelSheafOverIso U).hom ≫
        kernel.ι ((SheafOfModules.overFunctor _ U).map G.incEvaluationSheafMap) =
      (SheafOfModules.overFunctor _ U).map G.incKernelSheafι :=
  kernelOverIso_hom_ι U G.incEvaluationSheafMap

/-- On a subopen `W` of chart `σ`, the coefficient vector of a section of `O^{4m}` lies in the
kernel of the chart evaluation map iff the section is killed by the evaluation map. -/
theorem incCoeffSectionsEquiv_mem_ker_iff (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) (x : Γ(incCoeffSheaf V E, W)) :
    incCoeffSectionsEquiv W x ∈ LinearMap.ker (G.incChartEvaluation σ (incChartPoint σ W hW)) ↔
      (G.incEvaluationSheafMap.val.app (op W)).hom x = 0 := by
  rw [LinearMap.mem_ker, ← G.incEvaluationSheafMap_chart σ W hW x,
    LinearEquiv.map_eq_zero_iff]

/-- **Sections of `K_G` on a chart.** On every subopen `W` of chart `σ`, the sections of the
kernel sheaf are, by their coefficient vectors, the kernel of the chart evaluation map at the
chart point of `W`. -/
noncomputable def incKernelSheafChartSectionsEquiv (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) :
    Γ(G.incKernelSheaf, W) ≃ₗ[Γ(vertexScheme ℂ V, W)]
      LinearMap.ker (G.incChartEvaluation σ (incChartPoint σ W hW)) :=
  LinearEquiv.ofBijective
    (LinearMap.codRestrict _
      ((incCoeffSectionsEquiv W).toLinearMap ∘ₗ schemeSectionsMap G.incKernelSheafι W)
      fun k => (G.incCoeffSectionsEquiv_mem_ker_iff σ W hW _).mpr
        (G.incKernelSheafι_app_eval W k))
    ⟨fun k k' h => G.incKernelSheafι_app_injective W
        ((incCoeffSectionsEquiv W).injective (congrArg Subtype.val h)),
      fun v => by
        obtain ⟨k, hk⟩ := G.incKernelSheafι_app_exists W ((incCoeffSectionsEquiv W).symm v.1)
          ((G.incCoeffSectionsEquiv_mem_ker_iff σ W hW _).mp
            (by rw [LinearEquiv.apply_symm_apply]; exact v.2))
        refine ⟨k, Subtype.ext ?_⟩
        change incCoeffSectionsEquiv W ((G.incKernelSheafι.val.app (op W)).hom k) = v.1
        rw [hk, LinearEquiv.apply_symm_apply]⟩

/-- The chart identification of the sections of `K_G` reads the coefficient vector. -/
theorem incKernelSheafChartSectionsEquiv_apply (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) (k : Γ(G.incKernelSheaf, W)) :
    (G.incKernelSheafChartSectionsEquiv σ W hW k : IncCoeffIdx E → Γ(vertexScheme ℂ V, W)) =
      incCoeffSectionsEquiv W ((G.incKernelSheafι.val.app (op W)).hom k) :=
  rfl

end Kernel

/-! ### The kernel extension as a matrix -/

section KernelExtend

/-- A linear map between coordinate modules is the sum of its columns. -/
theorem linearMap_pi_apply_eq_sum_single {R ι κ : Type*} [CommRing R] [Fintype κ]
    [DecidableEq κ] (L : (κ → R) →ₗ[R] (ι → R)) (z : κ → R) (c : ι) :
    L z c = ∑ k, z k * L (Pi.single k 1) c := by
  have hz : z = ∑ k, z k • Pi.single k (1 : R) := by
    funext m
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hz]
  simp [map_sum, map_smul, Finset.sum_apply]

/-- The kernel extension of coordinates numbered by `E × Fin 3` is the combination of the kernel
extensions of the basis vectors. -/
theorem incChartKernelExtend_eq_sum {R : Type*} [CommRing R] (σ : V → Bool) (t : V → R)
    (y : E × Fin 3 → R) (c : IncCoeffIdx E) :
    G.incChartKernelExtend σ t (y ∘ (G.incChartFreeIdxEquiv σ).symm) c =
      ∑ j, y j * G.incChartKernelExtend σ t (Pi.single (G.incChartFreeIdxEquiv σ j) 1) c := by
  have h := linearMap_pi_apply_eq_sum_single (G.incChartKernelExtendLinear σ t)
    (y ∘ (G.incChartFreeIdxEquiv σ).symm) c
  simp only [incChartKernelExtendLinear_apply] at h
  rw [h]
  exact Fintype.sum_equiv (G.incChartFreeIdxEquiv σ).symm _ _ fun k => by simp

/-- The kernel extension of the coordinates of a kernel vector is the vector itself. -/
theorem incChartKernelExtend_of_mem {R : Type*} [CommRing R] (σ : V → Bool) (t : V → R)
    (v : IncCoeffIdx E → R) (hv : v ∈ LinearMap.ker (G.incChartEvaluation σ t)) :
    G.incChartKernelExtend σ t (fun f => v f.1) = v :=
  congrArg Subtype.val ((G.incChartEvaluationKernelEquiv σ t).symm_apply_apply ⟨v, hv⟩)

/-- The matrix of the kernel extension of chart `σ`, with entries functions on the chart open:
column `j` is the kernel vector whose non-unit coordinates are the basis vector `j`. -/
noncomputable def incKernelExtendMatrix (σ : V → Bool) (c : IncCoeffIdx E) (j : E × Fin 3) :
    Γ(vertexScheme ℂ V, incChartOpen V σ) :=
  G.incChartKernelExtend σ (incChartCoordinate σ) (Pi.single (G.incChartFreeIdxEquiv σ j) 1) c

/-- The kernel extension matrix restricts to the kernel extension at the chart point. -/
theorem incKernelExtendMatrix_restrict (σ : V → Bool) (W : (vertexScheme ℂ V).Opens)
    (hW : W ≤ incChartOpen V σ) (c : IncCoeffIdx E) (j : E × Fin 3) :
    (vertexScheme ℂ V).presheaf.map (homOfLE hW).op (G.incKernelExtendMatrix σ c j) =
      G.incChartKernelExtend σ (incChartPoint σ W hW) (Pi.single (G.incChartFreeIdxEquiv σ j) 1) c := by
  rw [incKernelExtendMatrix,
    G.map_incChartKernelExtend ((vertexScheme ℂ V).presheaf.map (homOfLE hW).op).hom]
  congr 1
  funext k
  by_cases hk : k = G.incChartFreeIdxEquiv σ j
  · subst hk
    simp
  · simp [Pi.single_eq_of_ne hk]

end KernelExtend

/-! ### The chart trivializations of the kernel sheaf -/

section ChartIso

/-- The coordinates of a section of the free sheaf on the over-site of `U`. -/
noncomputable def overFreeCoord {X : Scheme.{0}} (U : X.Opens) {J : Type} [Fintype J]
    (S : Over U) (y : (overFreeSheaf U J).val.obj (op S)) : J → Γ(X, S.left) :=
  fun j => ((biproduct.π (fun _ : J => SheafOfModules.unit (X.ringCatSheaf.over U)) j).val.app
    (op S)).hom y

/-- The kernel extension of chart `σ` on the over-site of the chart open, from `O^{3m}` to the
restriction of `O^{4m}`. -/
noncomputable def incKernelExtendOver (σ : V → Bool) :
    overFreeSheaf (incChartOpen V σ) (E × Fin 3) ⟶
      (SheafOfModules.overFunctor _ (incChartOpen V σ)).obj (incCoeffSheaf V E) :=
  overFreeMatrix (incChartOpen V σ) (G.incKernelExtendMatrix σ)

/-- On sections, the kernel extension of chart `σ` is `incChartKernelExtend` at the chart
point. -/
theorem incKernelExtendOver_app (σ : V → Bool) (S : Over (incChartOpen V σ))
    (y : (overFreeSheaf (incChartOpen V σ) (E × Fin 3)).val.obj (op S)) (c : IncCoeffIdx E) :
    ((biproduct.π (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf) c).val.app
        (op S.left)).hom (((G.incKernelExtendOver σ).val.app (op S)).hom y) =
      G.incChartKernelExtend σ (incChartPoint σ S.left S.hom.le)
        (overFreeCoord (incChartOpen V σ) S y ∘ (G.incChartFreeIdxEquiv σ).symm) c := by
  rw [incKernelExtendOver, overFreeMatrix_app, incChartKernelExtend_eq_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  exact G.incKernelExtendMatrix_restrict σ S.left S.hom.le c j

/-- The kernel extension of chart `σ` lands in the kernel of the evaluation map. -/
@[reassoc (attr := simp)] theorem incKernelExtendOver_comp (σ : V → Bool) :
    G.incKernelExtendOver σ ≫
      (SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incEvaluationSheafMap = 0 := by
  apply SheafOfModules.hom_ext
  ext S : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  change (G.incEvaluationSheafMap.val.app (op S.unop.left)).hom
    (((G.incKernelExtendOver σ).val.app S).hom y) = 0
  apply (G.incEdgeChartEquiv σ S.unop.left S.unop.hom.le).injective
  rw [map_zero, incEvaluationSheafMap_chart]
  have h : incCoeffSectionsEquiv S.unop.left (((G.incKernelExtendOver σ).val.app S).hom y) =
      G.incChartKernelExtend σ (incChartPoint σ S.unop.left S.unop.hom.le)
        (overFreeCoord (incChartOpen V σ) S.unop y ∘ (G.incChartFreeIdxEquiv σ).symm) :=
    funext fun c => G.incKernelExtendOver_app σ S.unop y c
  rw [h]
  exact LinearMap.mem_ker.mp (G.incChartKernelExtend_mem σ _ _)

/-- The chart-`σ` coordinates of the kernel sheaf on the chart open: the non-unit coefficients
`c_{e, incChartFreeIdx σ e i}` of chart `σ`. -/
noncomputable def incKernelChartHom (σ : V → Bool) :
    (SheafOfModules.overFunctor _ (incChartOpen V σ)).obj G.incKernelSheaf ⟶
      overFreeSheaf (incChartOpen V σ) (E × Fin 3) :=
  biproduct.lift fun j => (SheafOfModules.overFunctor _ (incChartOpen V σ)).map
    (G.incKernelSheafι ≫ biproduct.π (fun _ : IncCoeffIdx E =>
      SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf) (j.1, G.incChartFreeIdx σ j.1 j.2))

/-- The chart coordinates of a section of `K_G` are its non-unit coefficients. -/
theorem overFreeCoord_incKernelChartHom (σ : V → Bool) (S : Over (incChartOpen V σ))
    (k : Γ(G.incKernelSheaf, S.left)) (j : E × Fin 3) :
    overFreeCoord (incChartOpen V σ) S (((G.incKernelChartHom σ).val.app (op S)).hom k) j =
      incCoeffSectionsEquiv S.left ((G.incKernelSheafι.val.app (op S.left)).hom k)
        (j.1, G.incChartFreeIdx σ j.1 j.2) := by
  rw [overFreeCoord, incKernelChartHom, biproduct_lift_app_π]
  rfl

/-- The inverse of the chart coordinates: the kernel extension of chart `σ`, lifted to the
restriction of the kernel sheaf, which is a kernel of the restricted evaluation map
(`isLimit_kernelFork_over`). -/
noncomputable def incKernelChartInv (σ : V → Bool) :
    overFreeSheaf (incChartOpen V σ) (E × Fin 3) ⟶
      (SheafOfModules.overFunctor _ (incChartOpen V σ)).obj G.incKernelSheaf :=
  (isLimit_kernelFork_over (incChartOpen V σ) G.incEvaluationSheafMap).lift
    (KernelFork.ofι (G.incKernelExtendOver σ) (G.incKernelExtendOver_comp σ))

/-- The inverse chart coordinates followed by the inclusion are the kernel extension. -/
@[reassoc (attr := simp)] theorem incKernelChartInv_ι (σ : V → Bool) :
    G.incKernelChartInv σ ≫ (SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incKernelSheafι =
      G.incKernelExtendOver σ :=
  (isLimit_kernelFork_over (incChartOpen V σ) G.incEvaluationSheafMap).fac
    (KernelFork.ofι (G.incKernelExtendOver σ) (G.incKernelExtendOver_comp σ)) WalkingParallelPair.zero

/-- The restricted inclusion of the kernel sheaf is a monomorphism. -/
instance incKernelSheafι_over_mono (U : (vertexScheme ℂ V).Opens) :
    Mono ((SheafOfModules.overFunctor _ U).map G.incKernelSheafι) :=
  mono_of_isLimit_fork (isLimit_kernelFork_over U G.incEvaluationSheafMap)

/-- **The kernel sheaf is free of rank `3m` on every chart.** On the chart open of `σ`, the
restriction of `K_G` is isomorphic to `O^{3m}`, by the chart-`σ` kernel coordinates. -/
noncomputable def incKernelChartIso (σ : V → Bool) :
    (SheafOfModules.overFunctor _ (incChartOpen V σ)).obj G.incKernelSheaf ≅
      overFreeSheaf (incChartOpen V σ) (E × Fin 3) where
  hom := G.incKernelChartHom σ
  inv := G.incKernelChartInv σ
  hom_inv_id := by
    rw [← cancel_mono ((SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incKernelSheafι),
      Category.assoc, incKernelChartInv_ι, Category.id_comp]
    apply SheafOfModules.hom_ext
    ext S : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro k
    change (show (incCoeffSheaf V E).val.obj (op S.unop.left) from
      ((G.incKernelExtendOver σ).val.app S).hom (((G.incKernelChartHom σ).val.app S).hom k)) =
        (G.incKernelSheafι.val.app (op S.unop.left)).hom k
    apply biproduct_section_ext _ (op S.unop.left)
    intro c
    rw [incKernelExtendOver_app]
    have hk : incCoeffSectionsEquiv S.unop.left ((G.incKernelSheafι.val.app (op S.unop.left)).hom k) ∈
        LinearMap.ker (G.incChartEvaluation σ (incChartPoint σ S.unop.left S.unop.hom.le)) :=
      (G.incCoeffSectionsEquiv_mem_ker_iff σ _ _ _).mpr (G.incKernelSheafι_app_eval _ k)
    have hcoord : overFreeCoord (incChartOpen V σ) S.unop (((G.incKernelChartHom σ).val.app S).hom k) ∘
        (G.incChartFreeIdxEquiv σ).symm = fun f =>
          incCoeffSectionsEquiv S.unop.left ((G.incKernelSheafι.val.app (op S.unop.left)).hom k) f.1 := by
      funext f
      simp only [Function.comp_apply]
      rw [overFreeCoord_incKernelChartHom]
      conv_rhs => rw [← (G.incChartFreeIdxEquiv σ).apply_symm_apply f]
      rfl
    rw [hcoord, G.incChartKernelExtend_of_mem σ _ _ hk]
    rfl
  inv_hom_id := by
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, incKernelChartHom, biproduct.lift_π, Category.id_comp, Functor.map_comp,
      incKernelChartInv_ι_assoc]
    apply SheafOfModules.hom_ext
    ext S : 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro y
    change ((biproduct.π (fun _ : IncCoeffIdx E => SheafOfModules.unit (vertexScheme ℂ V).ringCatSheaf)
      (G.incChartFreeIdxEquiv σ j).1).val.app (op S.unop.left)).hom
        (((G.incKernelExtendOver σ).val.app S).hom y) = overFreeCoord (incChartOpen V σ) S.unop y j
    rw [incKernelExtendOver_app, incChartKernelExtend_freeIdxEquiv]
    simp

/-- The chart trivialization followed by the kernel extension is the inclusion of `K_G`. -/
@[reassoc (attr := simp)] theorem incKernelChartIso_hom_extend (σ : V → Bool) :
    (G.incKernelChartIso σ).hom ≫ G.incKernelExtendOver σ =
      (SheafOfModules.overFunctor _ (incChartOpen V σ)).map G.incKernelSheafι := by
  rw [← G.incKernelChartInv_ι σ]
  change (G.incKernelChartIso σ).hom ≫ (G.incKernelChartIso σ).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc]

/-- **The local kernel on a chart.** On the chart open of `σ`, the kernel extension
`O^{3m} → O^{4m}` of chart `σ` is a kernel of the restricted evaluation map. -/
noncomputable def incKernelExtendOver_isLimit (σ : V → Bool) :
    IsLimit (KernelFork.ofι (G.incKernelExtendOver σ) (G.incKernelExtendOver_comp σ)) :=
  IsLimit.ofIsoLimit (isLimit_kernelFork_over (incChartOpen V σ) G.incEvaluationSheafMap)
    (Fork.ext (G.incKernelChartIso σ) (G.incKernelChartIso_hom_extend σ))

/-- **Compatibility with the chart kernel coordinates.** On every subopen `W` of chart `σ`, the
chart-`σ` trivialization of `K_G` sends a section to the kernel coordinates
`incChartEvaluationKernelEquivFree σ` (at the chart point of `W`) of its coefficient vector. -/
theorem incKernelChartIso_chart (σ : V → Bool) (S : Over (incChartOpen V σ))
    (k : Γ(G.incKernelSheaf, S.left)) :
    overFreeCoord (incChartOpen V σ) S (((G.incKernelChartIso σ).hom.val.app (op S)).hom k) =
      G.incChartEvaluationKernelEquivFree σ (incChartPoint σ S.left S.hom.le)
        (G.incKernelSheafChartSectionsEquiv σ S.left S.hom.le k) := by
  funext j
  exact G.overFreeCoord_incKernelChartHom σ S k j

end ChartIso

/-! ### Local freeness in Mathlib's sense -/

section LocallyFree

variable (V) in
/-- The chart opens cover the terminal open of the site of `X_G`. -/
theorem incChartOpen_coversTop :
    (Opens.grothendieckTopology (vertexScheme ℂ V)).CoversTop (incChartOpen V) := by
  intro W x hx
  obtain ⟨σ, hσ⟩ := TopologicalSpace.Opens.mem_iSup.mp
    (incChartOpen_iSup_top V (show x ∈ (⊤ : (vertexScheme ℂ V).Opens) from trivial))
  exact ⟨W ⊓ incChartOpen V σ, homOfLE inf_le_left, ⟨σ, ⟨homOfLE inf_le_right⟩⟩, hx, hσ⟩

/-- The `3m` generating sections of `K_G` over chart `σ`: the images of the standard basis of
`O^{3m}` under the inverse chart trivialization. -/
noncomputable def incKernelSheafChartGenerators (σ : V → Bool) :
    ((SheafOfModules.overFunctor _ (incChartOpen V σ)).obj G.incKernelSheaf).GeneratingSections :=
  (SheafOfModules.free.generatingSections
    (R := (vertexScheme ℂ V).ringCatSheaf.over (incChartOpen V σ)) (E × Fin 3)).ofEpi
      ((biproduct.isoCoproduct _).inv ≫ (G.incKernelChartIso σ).inv)

/-- The chart generating sections of `K_G` as local generator data on the chart cover. -/
noncomputable def incKernelSheafLocalGenerators : G.incKernelSheaf.LocalGeneratorsData where
  I := V → Bool
  X := incChartOpen V
  coversTop := incChartOpen_coversTop V
  generators σ := G.incKernelSheafChartGenerators σ

/-- The chart generating sections of `K_G` are free: the presentations are isomorphisms. -/
instance incKernelSheafLocalGenerators_isLocallyFreeData :
    G.incKernelSheafLocalGenerators.IsLocallyFreeData where
  isIso σ := by
    change IsIso (G.incKernelSheafChartGenerators σ).π
    rw [incKernelSheafChartGenerators, SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    infer_instance

/-- **The kernel sheaf is locally free** in Mathlib's sense. -/
instance incKernelSheaf_isLocallyFree : G.incKernelSheaf.IsLocallyFree :=
  G.incKernelSheafLocalGenerators.isLocallyFree

/-- The kernel sheaf is quasicoherent. -/
instance incKernelSheaf_isQuasicoherent : G.incKernelSheaf.IsQuasicoherent := by
  infer_instance

end LocallyFree

/-! ### Faces: kernel coordinates and transitions -/

section Faces

variable {σ τ : V → Bool} {r : V → Fin 3}

/-- The over-site object of the face open of `r` inside the chart open of `σ`. -/
noncomputable abbrev incFaceOver (hσ : FaceRefines (chartFace σ) r) : Over (incChartOpen V σ) :=
  Over.mk (homOfLE (incFaceOpen_le_chart hσ))

/-- The coefficient vector of a section of `K_G` over the face open of `r`, in face
coordinates. -/
noncomputable def incKernelSheafFaceVector (r : V → Fin 3) (k : Γ(G.incKernelSheaf, incFaceOpen V r)) :
    IncCoeffIdx E → FaceRing ℂ r :=
  fun c => vertexFaceSectionsEquiv ℂ V r
    (incCoeffSectionsEquiv (incFaceOpen V r) ((G.incKernelSheafι.val.app (op (incFaceOpen V r))).hom k) c)

/-- The face coefficient vector of a section of `K_G` lies in the kernel `IncOverlapKernel r` of
the face evaluation map. -/
theorem incKernelSheafFaceVector_mem (hσ : FaceRefines (chartFace σ) r)
    (k : Γ(G.incKernelSheaf, incFaceOpen V r)) :
    G.incKernelSheafFaceVector r k ∈ G.IncOverlapKernel r := by
  change _ ∈ LinearMap.ker (G.incFaceEvaluation r)
  rw [← G.ker_incChartEvaluation_overlap hσ, LinearMap.mem_ker]
  have hk := (G.incCoeffSectionsEquiv_mem_ker_iff σ (incFaceOpen V r) (incFaceOpen_le_chart hσ)
    ((G.incKernelSheafι.val.app (op (incFaceOpen V r))).hom k)).mpr (G.incKernelSheafι_app_eval _ k)
  rw [LinearMap.mem_ker] at hk
  funext e
  have h := congrArg (vertexFaceSectionsEquiv ℂ V r) (congrFun hk e)
  rw [G.map_incChartEvaluation (vertexFaceSectionsEquiv ℂ V r)] at h
  simp only [vertexFaceSectionsEquiv_incChartPoint hσ, Pi.zero_apply, map_zero] at h
  exact h

/-- The face coefficient vector of a section of `K_G`, as an element of `IncOverlapKernel r`. -/
noncomputable def incKernelSheafFaceKernel (hσ : FaceRefines (chartFace σ) r)
    (k : Γ(G.incKernelSheaf, incFaceOpen V r)) : G.IncOverlapKernel r :=
  ⟨G.incKernelSheafFaceVector r k, G.incKernelSheafFaceVector_mem hσ k⟩

/-- The face coordinates of the chart-`σ` trivialization of a section of `K_G` over the face
open of `r`. -/
noncomputable def incKernelChartFaceCoord (hσ : FaceRefines (chartFace σ) r)
    (k : Γ(G.incKernelSheaf, incFaceOpen V r)) : E × Fin 3 → FaceRing ℂ r :=
  fun j => vertexFaceSectionsEquiv ℂ V r (overFreeCoord (incChartOpen V σ) (incFaceOver hσ)
    (((G.incKernelChartIso σ).hom.val.app (op (incFaceOver hσ))).hom k) j)

/-- **The trivializations of `K_G` are the kernel coordinates `κ_σ`.** On the face open of a
face `r` refined by chart `σ`, the chart-`σ` trivialization of `K_G`, read in face coordinates,
is the kernel coordinate map `incOverlapKernelCoord hσ` of
`IncidenceKernelBundleTransitions.lean` applied to the face coefficient vector. -/
theorem incKernelChartFaceCoord_eq (hσ : FaceRefines (chartFace σ) r)
    (k : Γ(G.incKernelSheaf, incFaceOpen V r)) :
    G.incKernelChartFaceCoord hσ k = G.incOverlapKernelCoord hσ (G.incKernelSheafFaceKernel hσ k) := by
  funext j
  rw [incOverlapKernelCoord_apply, incKernelChartFaceCoord]
  exact congrArg (vertexFaceSectionsEquiv ℂ V r)
    (G.overFreeCoord_incKernelChartHom σ (incFaceOver hσ) k j)

/-- **The transitions of `K_G` are `incKernelTransition`.** On the face open of a face `r`
refined by charts `σ` and `τ`, the chart-`τ` coordinates of a section of `K_G` are obtained from
its chart-`σ` coordinates by the kernel transition `g_{τσ} = incKernelTransition hσ hτ`. -/
theorem incKernelChartFaceCoord_transition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (k : Γ(G.incKernelSheaf, incFaceOpen V r)) :
    G.incKernelChartFaceCoord hτ k = G.incKernelTransition hσ hτ (G.incKernelChartFaceCoord hσ k) := by
  rw [G.incKernelChartFaceCoord_eq hσ, G.incKernelChartFaceCoord_eq hτ,
    incKernelTransition_kernelCoord]
  rfl

/-- The section of `O^{3m}` over the face open of `r` with prescribed face coordinates. -/
noncomputable def incFaceFreeSection (hσ : FaceRefines (chartFace σ) r)
    (y : E × Fin 3 → FaceRing ℂ r) :
    (overFreeSheaf (incChartOpen V σ) (E × Fin 3)).val.obj (op (incFaceOver hσ)) :=
  (biproductSectionsEquiv _ (op (incFaceOver hσ))).symm
    fun j => (vertexFaceSectionsEquiv ℂ V r).symm (y j)

/-- The transition of the trivializations of `K_G` from chart `σ` to chart `τ` over the face
open of `r`, in face coordinates: `y ↦ Φ_τ (Φ_σ⁻¹ y)`. -/
noncomputable def incKernelSheafTransition (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (y : E × Fin 3 → FaceRing ℂ r) : E × Fin 3 → FaceRing ℂ r :=
  G.incKernelChartFaceCoord hτ
    (((G.incKernelChartIso σ).inv.val.app (op (incFaceOver hσ))).hom (incFaceFreeSection hσ y))

/-- **The transition functions of `K_G` are the kernel transitions.** For a face `r` refined by
charts `σ` and `τ`, the transition `Φ_τ ∘ Φ_σ⁻¹` of the chart trivializations of the kernel
sheaf, read in face coordinates, is `incKernelTransition hσ hτ`. Together with
`incFaceKernelTriv_transition`, the trivializations of `K_G` reproduce the trivializations of
`Z_G` and their `Sym(g^∨)` transitions. -/
theorem incKernelSheafTransition_eq (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) :
    G.incKernelSheafTransition hσ hτ = ⇑(G.incKernelTransition hσ hτ) := by
  funext y
  rw [incKernelSheafTransition, incKernelChartFaceCoord_transition G hσ hτ]
  congr 1
  funext j
  have h := congrArg (fun φ => (φ.val.app (op (incFaceOver hσ))).hom (incFaceFreeSection hσ y))
    (G.incKernelChartIso σ).inv_hom_id
  rw [incKernelChartFaceCoord]
  change vertexFaceSectionsEquiv ℂ V r (overFreeCoord (incChartOpen V σ) (incFaceOver hσ)
    (((G.incKernelChartIso σ).inv ≫ (G.incKernelChartIso σ).hom).val.app (op (incFaceOver hσ))
      |>.hom (incFaceFreeSection hσ y)) j) = y j
  rw [h]
  change vertexFaceSectionsEquiv ℂ V r
    ((biproductSectionsEquiv _ (op (incFaceOver hσ))) (incFaceFreeSection hσ y) j) = y j
  rw [incFaceFreeSection, LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Faces

end Main

/-! ### The trivializations of `Z_G` -/

section IncidenceScheme

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) {σ τ : V → Bool} {r : V → Fin 3}

/-- **`Z_G` is the total space of `K_G` over each face.** The transition of the trivializations
`incFaceKernelTriv` of the coordinate ring of `Z_G` over a face refined by charts `σ` and `τ` is
the linear substitution given by the transition of the kernel sheaf from `τ` to `σ`. -/
theorem incFaceKernelTriv_transition_kernelSheaf (hσ : FaceRefines (chartFace σ) r)
    (hτ : FaceRefines (chartFace τ) r) (j : E × Fin 3) :
    G.incFaceKernelTriv hτ ((G.incFaceKernelTriv hσ).symm (MvPolynomial.X j)) =
      ∑ i, MvPolynomial.C (G.incKernelSheafTransition hτ hσ (Pi.single i 1) j) * MvPolynomial.X i := by
  rw [incKernelSheafTransition_eq]
  exact G.incFaceKernelTriv_transition_X hσ hτ j

end IncidenceScheme

end BPFixedPoints.Multigraph
