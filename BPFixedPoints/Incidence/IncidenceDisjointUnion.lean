import BPFixedPoints.Incidence.IncidenceDisjointUnionRings
import BPFixedPoints.Incidence.IncidenceDisjointUnionTensor

/-!
# The incidence ring of a disjoint union (`alg:functoriality`, tensor formula)

For multigraphs `G : Multigraph V E` and `H : Multigraph W F` we prove
`𝒰_{G⊔H} ≃ 𝒰_G ⊗_ℂ 𝒰_H` for the chart model `IncidenceRing` of the universal edge-incidence ring
(`incidenceSumEquiv`). The isomorphism is the restriction of the torus isomorphism
`torusSumEquiv : T_{G⊔H} ≃ T_G ⊗ T_H` (`incidenceTensorIncl_incidenceSumEquiv`); concretely
`y ⊗ z` goes to the product of the pullbacks of `y` and `z` along the two summand inclusions
(`incidenceSumEquiv_symm_tmul_val`). It intertwines the coefficient maps through
`coeffSumEquiv : S_{G⊔H} ≃ S_G ⊗ S_H` (`incidenceSumEquiv_coeffHom`).

The proof replaces the paper's appeal to Künneth for global sections by the chart description:
`𝒰_{G⊔H}` is the intersection over `σ = (σ₁, σ₂)` of the chart images, the chart image at `σ`
corresponds to `im χ_{σ₁} ⊠ im χ_{σ₂}` inside `T_G ⊗ T_H`, and over the field `ℂ`
`⋂_{σ₁,σ₂} (A_{σ₁} ⊠ B_{σ₂}) = (⋂ A_{σ₁}) ⊠ (⋂ B_{σ₂})` (`iInf_range_mapIncl`), while
`𝒰_G ⊗ 𝒰_H → T_G ⊗ T_H` is injective by flatness.

For a graph with no vertices and no edges, `IncidenceRing = ⊤` and `𝒰 ≃ ℂ`
(`incidenceRing_eq_top_of_isEmpty`, `emptyIncidenceEquiv`). As a sanity check, `𝒰_{G⊔∅} ≃ 𝒰_G`
(`incidenceSumEmptyEquiv`), and its inverse is the pullback along the summand inclusion
(`incidenceSumEmptyEquiv_symm_val`).

The symmetry, associativity and unit compatibilities with the graph isomorphisms of disjoint
unions are in `IncidenceDisjointUnionCoherence.lean`. Not proved: compatibility with the natural
coefficient grading `incidenceCoefficientPiece`. The identification of `IncidenceRing` with sheaf
global sections, and the scheme-theoretic product statement, are neither used nor proved.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial TensorProduct
open scoped TensorProduct

/-! ### Ranges of tensor products of algebra maps -/

section TensorRange

variable {A B T₁ T₂ : Type*} [CommRing A] [CommRing B] [CommRing T₁] [CommRing T₂]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ T₁] [Algebra ℂ T₂]

/-- The range of a tensor product of algebra maps is the tensor product of the ranges, viewed
inside the tensor product of the targets. -/
theorem mem_range_tensorMap_iff (f : A →ₐ[ℂ] T₁) (g : B →ₐ[ℂ] T₂) (x : T₁ ⊗[ℂ] T₂) :
    x ∈ (Algebra.TensorProduct.map f g).range ↔
      x ∈ LinearMap.range (mapIncl (LinearMap.range f.toLinearMap)
        (LinearMap.range g.toLinearMap)) := by
  rw [range_mapIncl, ← TensorProduct.range_map, AlgHom.mem_range, LinearMap.mem_range]
  rfl

end TensorRange

/-! ### The incidence ring of a disjoint union -/

section Incidence

variable {V W E F : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq W] [Fintype W] [DecidableEq F] [Fintype F]
  (G : Multigraph V E) (H : Multigraph W F)

/-- The inclusion `𝒰_G ⊗ 𝒰_H → T_G ⊗ T_H`. -/
noncomputable def incidenceTensorIncl :
    G.IncidenceRing ⊗[ℂ] H.IncidenceRing →ₐ[ℂ] G.IncTorusRing ⊗[ℂ] H.IncTorusRing :=
  Algebra.TensorProduct.map G.IncidenceRing.val H.IncidenceRing.val

@[simp] theorem incidenceTensorIncl_tmul (y : G.IncidenceRing) (z : H.IncidenceRing) :
    incidenceTensorIncl G H (y ⊗ₜ[ℂ] z) = y.val ⊗ₜ[ℂ] z.val := rfl

/-- Over `ℂ`, `𝒰_G ⊗ 𝒰_H → T_G ⊗ T_H` is injective (flatness of vector spaces). -/
theorem incidenceTensorIncl_injective : Function.Injective (incidenceTensorIncl G H) := by
  have : Module.Flat ℂ G.IncTorusRing := Module.Flat.of_free
  have : Module.Flat ℂ H.IncidenceRing := Module.Flat.of_free
  exact TensorProduct.map_injective_of_flat_flat G.IncidenceRing.val.toLinearMap
    H.IncidenceRing.val.toLinearMap Subtype.val_injective Subtype.val_injective

/-- As a subspace of the torus ring, `𝒰_G` is the intersection of the chart images. -/
theorem iInf_range_incChartMap :
    ⨅ σ : V → Bool, LinearMap.range (G.incChartMap σ).toLinearMap =
      LinearMap.range G.IncidenceRing.val.toLinearMap := by
  ext y
  simp only [Submodule.mem_iInf, LinearMap.mem_range, AlgHom.toLinearMap_apply]
  constructor
  · intro h
    have hy : y ∈ G.IncidenceRing := by
      simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range]
      exact h
    exact ⟨⟨y, hy⟩, rfl⟩
  · rintro ⟨u, rfl⟩ σ
    have hu : (u : G.IncTorusRing) ∈ G.IncidenceRing := u.property
    simp only [IncidenceRing, Algebra.mem_iInf, AlgHom.mem_range] at hu
    exact hu σ

/-- A torus element of `G ⊔ H` comes from the chart at `σ` iff its image in `T_G ⊗ T_H` lies in
the tensor product of the chart images at `σ ∘ Sum.inl` and `σ ∘ Sum.inr`. -/
theorem mem_range_incChartMap_disjointSum_iff (σ : V ⊕ W → Bool)
    (x : (G.disjointSum H).IncTorusRing) :
    x ∈ ((G.disjointSum H).incChartMap σ).range ↔
      G.torusSumEquiv H x ∈ (Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl))
        (H.incChartMap (σ ∘ Sum.inr))).range := by
  simp only [AlgHom.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨G.chartSumEquiv H σ y, (G.torusSumEquiv_incChartMap H σ y).symm⟩
  · rintro ⟨z, hz⟩
    refine ⟨(G.chartSumEquiv H σ).symm z, (G.torusSumEquiv H).injective ?_⟩
    rw [torusSumEquiv_incChartMap, AlgEquiv.apply_symm_apply, hz]

/-- **Membership in the incidence ring of a disjoint union.** A torus element of `G ⊔ H` lies in
`𝒰_{G⊔H}` iff its image in `T_G ⊗ T_H` lies in `𝒰_G ⊗ 𝒰_H`. -/
theorem mem_incidenceRing_disjointSum_iff (x : (G.disjointSum H).IncTorusRing) :
    x ∈ (G.disjointSum H).IncidenceRing ↔
      G.torusSumEquiv H x ∈ (incidenceTensorIncl G H).range := by
  rw [IncidenceRing, Algebra.mem_iInf]
  simp only [mem_range_incChartMap_disjointSum_iff, mem_range_tensorMap_iff]
  rw [incidenceTensorIncl, mem_range_tensorMap_iff, ← iInf_range_incChartMap G,
    ← iInf_range_incChartMap H, mem_range_mapIncl_iInf_iff]
  constructor
  · intro h σ₁ σ₂
    exact h (Sum.elim σ₁ σ₂)
  · intro h σ
    exact h (σ ∘ Sum.inl) (σ ∘ Sum.inr)

/-- The torus isomorphism carries `𝒰_{G⊔H}` onto the image of `𝒰_G ⊗ 𝒰_H`. -/
theorem map_incidenceRing_disjointSum :
    (G.disjointSum H).IncidenceRing.map (G.torusSumEquiv H : _ →ₐ[ℂ] _) =
      (incidenceTensorIncl G H).range := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (G.mem_incidenceRing_disjointSum_iff H x).1 hx
  · intro hy
    refine ⟨(G.torusSumEquiv H).symm y, ?_, by simp⟩
    rw [mem_incidenceRing_disjointSum_iff, AlgEquiv.apply_symm_apply]
    exact hy

/-- **Tensor formula for a disjoint union (`alg:functoriality`).**
`𝒰_{G⊔H} ≃ₐ[ℂ] 𝒰_G ⊗[ℂ] 𝒰_H`, the restriction of `torusSumEquiv`. -/
noncomputable def incidenceSumEquiv :
    (G.disjointSum H).IncidenceRing ≃ₐ[ℂ] G.IncidenceRing ⊗[ℂ] H.IncidenceRing :=
  ((AlgEquiv.subalgebraMap (G.torusSumEquiv H) (G.disjointSum H).IncidenceRing).trans
    (Subalgebra.equivOfEq _ _ (G.map_incidenceRing_disjointSum H))).trans
      (AlgEquiv.ofInjective _ (incidenceTensorIncl_injective G H)).symm

/-- The incidence isomorphism is the restriction of the torus isomorphism. -/
theorem incidenceTensorIncl_incidenceSumEquiv (x : (G.disjointSum H).IncidenceRing) :
    incidenceTensorIncl G H (G.incidenceSumEquiv H x) = G.torusSumEquiv H x.val := by
  exact congrArg Subtype.val
    ((AlgEquiv.ofInjective _ (incidenceTensorIncl_injective G H)).apply_symm_apply
      ((Subalgebra.equivOfEq _ _ (G.map_incidenceRing_disjointSum H))
        (AlgEquiv.subalgebraMap (G.torusSumEquiv H) (G.disjointSum H).IncidenceRing x)))

/-- The inverse incidence isomorphism is the restriction of the inverse torus isomorphism. -/
theorem incidenceSumEquiv_symm_val (z : G.IncidenceRing ⊗[ℂ] H.IncidenceRing) :
    ((G.incidenceSumEquiv H).symm z).val =
      (G.torusSumEquiv H).symm (incidenceTensorIncl G H z) := by
  apply (G.torusSumEquiv H).injective
  rw [AlgEquiv.apply_symm_apply, ← incidenceTensorIncl_incidenceSumEquiv, AlgEquiv.apply_symm_apply]

/-- The coefficient element `c_{e,ab}` of the torus ring. -/
theorem coeffHom_X_val (c : IncCoeffIdx E) :
    (G.coeffHom (X c)).val = Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c))) := by
  simp [coeffHom]

/-- **Coefficient compatibility.** The incidence isomorphism intertwines the coefficient map of
`G ⊔ H` with the tensor product of the coefficient maps, through `coeffSumEquiv`. -/
theorem incidenceSumEquiv_coeffHom (r : IncCoeffRing (E ⊕ F)) :
    G.incidenceSumEquiv H ((G.disjointSum H).coeffHom r) =
      Algebra.TensorProduct.map G.coeffHom H.coeffHom (coeffSumEquiv E F r) := by
  apply incidenceTensorIncl_injective G H
  rw [incidenceTensorIncl_incidenceSumEquiv]
  have h : (G.torusSumEquiv H).toAlgHom.comp
        ((G.disjointSum H).IncidenceRing.val.comp (G.disjointSum H).coeffHom) =
      ((incidenceTensorIncl G H).comp (Algebra.TensorProduct.map G.coeffHom H.coeffHom)).comp
        (coeffSumEquiv E F).toAlgHom := by
    apply MvPolynomial.algHom_ext
    rintro ⟨e | f, ab⟩
    · change G.torusSumEquiv H ((G.disjointSum H).coeffHom (X (Sum.inl e, ab))).val =
        incidenceTensorIncl G H (Algebra.TensorProduct.map G.coeffHom H.coeffHom
          (coeffSumEquiv E F (X (Sum.inl e, ab))))
      rw [coeffHom_X_val, coeffSumEquiv_X_inl, Algebra.TensorProduct.map_tmul, map_one,
        incidenceTensorIncl_tmul, coeffHom_X_val, Subalgebra.coe_one, torusSumEquiv_coeff_inl]
    · change G.torusSumEquiv H ((G.disjointSum H).coeffHom (X (Sum.inr f, ab))).val =
        incidenceTensorIncl G H (Algebra.TensorProduct.map G.coeffHom H.coeffHom
          (coeffSumEquiv E F (X (Sum.inr f, ab))))
      rw [coeffHom_X_val, coeffSumEquiv_X_inr, Algebra.TensorProduct.map_tmul, map_one,
        incidenceTensorIncl_tmul, coeffHom_X_val, Subalgebra.coe_one, torusSumEquiv_coeff_inr]
  exact AlgHom.congr_fun h r

/-! #### Pullbacks along the summand inclusions -/

/-- Pullback of torus functions along the projection `Z_{G⊔H} → Z_G`, i.e. the inclusion
`T_G → T_{G⊔H}` renaming vertices and coefficients into the first summand. -/
noncomputable def torusInl : G.IncTorusRing →ₐ[ℂ] (G.disjointSum H).IncTorusRing :=
  (G.torusSumEquiv H).symm.toAlgHom.comp Algebra.TensorProduct.includeLeft

/-- Pullback of torus functions along the projection `Z_{G⊔H} → Z_H`. -/
noncomputable def torusInr : H.IncTorusRing →ₐ[ℂ] (G.disjointSum H).IncTorusRing :=
  (G.torusSumEquiv H).symm.toAlgHom.comp Algebra.TensorProduct.includeRight

theorem torusInl_mk (p : MvPolynomial (IncTorusVar V E) ℂ) :
    G.torusInl H (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (torusVarSumEquiv V W E F ∘ Sum.inl) p) :=
  quotTensorToSum_tmul_one (torusVarSumEquiv V W E F) (torusRelIdxSumEquiv V W E F)
    G.incTorusRel H.incTorusRel (G.disjointSum H).incTorusRel
    (G.disjointSum_incTorusRel_inl H) (G.disjointSum_incTorusRel_inr H) p

theorem torusInr_mk (p : MvPolynomial (IncTorusVar W F) ℂ) :
    G.torusInr H (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (rename (torusVarSumEquiv V W E F ∘ Sum.inr) p) :=
  quotTensorToSum_one_tmul (torusVarSumEquiv V W E F) (torusRelIdxSumEquiv V W E F)
    G.incTorusRel H.incTorusRel (G.disjointSum H).incTorusRel
    (G.disjointSum_incTorusRel_inl H) (G.disjointSum_incTorusRel_inr H) p

/-- **Künneth description.** The inverse of the incidence isomorphism sends `y ⊗ z` to the
product of the pullbacks of `y` and `z` to `G ⊔ H`. -/
theorem incidenceSumEquiv_symm_tmul_val (y : G.IncidenceRing) (z : H.IncidenceRing) :
    ((G.incidenceSumEquiv H).symm (y ⊗ₜ[ℂ] z)).val = G.torusInl H y.val * G.torusInr H z.val := by
  rw [incidenceSumEquiv_symm_val, incidenceTensorIncl_tmul, torusInl, torusInr]
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul]
  rfl

end Incidence

/-! ### The empty graph and the unit compatibility -/

section Empty

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

variable {V₀ E₀ : Type} [DecidableEq V₀] [Fintype V₀] [DecidableEq E₀] [Fintype E₀]
  [IsEmpty V₀] [IsEmpty E₀] (G₀ : Multigraph V₀ E₀)

/-- With no vertices and no edges, every torus function is a constant. -/
theorem incTorus_eq_algebraMap_of_isEmpty (x : G₀.IncTorusRing) :
    ∃ a : ℂ, x = algebraMap ℂ G₀.IncTorusRing a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨p.coeff 0, ?_⟩
  conv_lhs => rw [MvPolynomial.eq_C_of_isEmpty p]
  rfl

/-- With no vertices and no edges, the incidence ring is the whole torus ring. -/
theorem incidenceRing_eq_top_of_isEmpty : G₀.IncidenceRing = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, rfl⟩ := G₀.incTorus_eq_algebraMap_of_isEmpty x
  exact Subalgebra.algebraMap_mem _ a

theorem algebraMap_incidenceRing_bijective_of_isEmpty :
    Function.Bijective (algebraMap ℂ G₀.IncidenceRing) := by
  refine ⟨(algebraMap ℂ G₀.IncidenceRing).injective, fun u => ?_⟩
  obtain ⟨a, ha⟩ := G₀.incTorus_eq_algebraMap_of_isEmpty u.val
  exact ⟨a, Subtype.ext ha.symm⟩

/-- **Unit.** For a graph with no vertices and no edges, `𝒰 ≃ₐ[ℂ] ℂ`. -/
noncomputable def emptyIncidenceEquiv : G₀.IncidenceRing ≃ₐ[ℂ] ℂ :=
  (AlgEquiv.ofBijective (Algebra.ofId ℂ G₀.IncidenceRing)
    (G₀.algebraMap_incidenceRing_bijective_of_isEmpty)).symm

@[simp] theorem emptyIncidenceEquiv_symm_apply (a : ℂ) :
    (G₀.emptyIncidenceEquiv).symm a = algebraMap ℂ G₀.IncidenceRing a := rfl

/-- **Sanity check: disjoint union with an empty graph.** `𝒰_{G⊔∅} ≃ₐ[ℂ] 𝒰_G`. -/
noncomputable def incidenceSumEmptyEquiv :
    (G.disjointSum G₀).IncidenceRing ≃ₐ[ℂ] G.IncidenceRing :=
  (G.incidenceSumEquiv G₀).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl G₀.emptyIncidenceEquiv).trans
      (Algebra.TensorProduct.rid ℂ ℂ G.IncidenceRing))

/-- **Unit compatibility.** The inverse of `𝒰_{G⊔∅} ≃ 𝒰_G` is the pullback along the summand
inclusion `T_G → T_{G⊔∅}`. -/
theorem incidenceSumEmptyEquiv_symm_val (y : G.IncidenceRing) :
    ((G.incidenceSumEmptyEquiv G₀).symm y).val = G.torusInl G₀ y.val := by
  have h : (G.incidenceSumEmptyEquiv G₀).symm y = (G.incidenceSumEquiv G₀).symm (y ⊗ₜ[ℂ] 1) := by
    simp [incidenceSumEmptyEquiv, AlgEquiv.symm_trans_apply]
  rw [h, incidenceSumEquiv_symm_tmul_val, Subalgebra.coe_one, map_one, mul_one]

/-- A concrete graph with no vertices and no edges. -/
def emptyMultigraph : Multigraph Empty Empty := ⟨Empty.elim, Empty.elim⟩

/-- The empty multigraph has incidence ring `ℂ`. -/
noncomputable example : emptyMultigraph.IncidenceRing ≃ₐ[ℂ] ℂ :=
  emptyMultigraph.emptyIncidenceEquiv

/-- Disjoint union with the empty multigraph does not change the incidence ring. -/
noncomputable example : (G.disjointSum emptyMultigraph).IncidenceRing ≃ₐ[ℂ] G.IncidenceRing :=
  G.incidenceSumEmptyEquiv emptyMultigraph

end Empty

end BPFixedPoints.Multigraph
