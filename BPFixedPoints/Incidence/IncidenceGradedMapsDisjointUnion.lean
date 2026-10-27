import BPFixedPoints.Incidence.IncidenceGradedMapsScaling
import BPFixedPoints.Incidence.IncidenceDisjointUnion
import BPFixedPoints.Incidence.NaturalGradedResolution

/-!
# The tensor formula for a disjoint union is graded (`alg:functoriality`, grading)

For multigraphs `G : Multigraph V E` and `H : Multigraph W F` the tensor formula
`incidenceSumEquiv : 𝒰_{G⊔H} ≃ₐ[ℂ] 𝒰_G ⊗[ℂ] 𝒰_H` is compatible with the natural coefficient
gradings `incidenceCoefficientPiece`, the tensor product carrying the total degree.

* **Scaling.** The torus isomorphism and the tensor formula intertwine coefficient scaling on
  `G ⊔ H` with the tensor product of the coefficient scalings (`torusSumEquiv_incTorusScale`,
  `incidenceSumEquiv_incidenceScale`).
* **Degree pieces of the tensor product.** `incidenceTensorBipiece G H i j` is the span of the
  `y ⊗ z` with `y` of degree `i` and `z` of degree `j`, and `incidenceTensorPiece G H n` is the sum
  of these over `i + j = n`. The bidegree parts span (`iSup_incidenceTensorBipiece`) and are
  independent (`iSupIndep_incidenceTensorBipiece`, via the bidegree projections
  `incidenceTensorProj`); `𝒰_{G,i} ⊗ 𝒰_{H,j}` maps isomorphically onto the bidegree-`(i, j)` part
  (`mapIncl_incidenceCoefficientPiece_injective`, `incidenceTensorBipieceEquiv`).
* **Graded tensor formula.** `y ⊗ z` of degrees `i`, `j` goes to a section of degree `i + j` of
  `𝒰_{G⊔H}` (`incidenceSumEquiv_symm_tmul_mem`), and `incidenceSumEquiv` maps the degree-`n` piece
  of `𝒰_{G⊔H}` onto `incidenceTensorPiece G H n` (`map_incidenceCoefficientPiece_disjointSum`,
  `incidenceSumEquiv_mem_incidenceTensorPiece_iff`). Consequently the degree-`n` piece of
  `𝒰_{G⊔H}` is isomorphic to `⨁_{i+j=n} 𝒰_{G,i} ⊗ 𝒰_{H,j}` (`incidenceSumPieceEquiv`), with
  inverse `y ⊗ z ↦ incidenceSumEquiv.symm (y ⊗ z)` on each summand
  (`incidenceSumPieceEquiv_symm_of_tmul`).

The natural grading of `𝒰_{G⊔H}` is formed with the lexicographic order `disjointSumEdgeOrder` on
`E ⊕ F` (edges of `G` first), used as a local instance; by the scaling characterization the pieces
do not depend on the order, but no statement comparing two orders is formalized. Not covered: the
graded structure as a Mathlib `GradedAlgebra` on `𝒰_G ⊗ 𝒰_H`, gradings of `Tor`, and
the identification of `IncidenceRing` with sheaf global sections.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial TensorProduct
open scoped TensorProduct DirectSum

/-! ### The disjoint-union isomorphisms commute with coefficient scaling -/

section Scaling

variable {V W E F : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq W] [Fintype W] [DecidableEq F] [Fintype F]
  (G : Multigraph V E) (H : Multigraph W F)

/-- The torus isomorphism `T_{G⊔H} ≃ T_G ⊗ T_H` intertwines coefficient scaling with the tensor
product of the coefficient scalings. -/
theorem torusSumEquiv_comp_incTorusScale (a : ℂ) :
    (G.torusSumEquiv H).toAlgHom.comp ((G.disjointSum H).incTorusScale a) =
      (Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)).comp
        (G.torusSumEquiv H).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ((v | w) | (v | w) | ⟨e | f, ab⟩)
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inl v))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inl v)))))
    rw [incTorusScale_t, torusSumEquiv_t_inl, Algebra.TensorProduct.map_tmul, incTorusScale_t,
      map_one]
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inr w))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inr w)))))
    rw [incTorusScale_t, torusSumEquiv_t_inr, Algebra.TensorProduct.map_tmul, incTorusScale_t,
      map_one]
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inl v)))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inl v))))))
    rw [incTorusScale_s, torusSumEquiv_s_inl, Algebra.TensorProduct.map_tmul, incTorusScale_s,
      map_one]
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inr w)))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inr w))))))
    rw [incTorusScale_s, torusSumEquiv_s_inr, Algebra.TensorProduct.map_tmul, incTorusScale_s,
      map_one]
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inl e, ab)))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inl e, ab))))))
    rw [incTorusScale_coeff, map_smul, torusSumEquiv_coeff_inl, Algebra.TensorProduct.map_tmul,
      incTorusScale_coeff, map_one, smul_tmul']
  · change G.torusSumEquiv H ((G.disjointSum H).incTorusScale a
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inr f, ab)))))) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)
        (G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inr f, ab))))))
    rw [incTorusScale_coeff, map_smul, torusSumEquiv_coeff_inr, Algebra.TensorProduct.map_tmul,
      incTorusScale_coeff, map_one, tmul_smul]

/-- The torus isomorphism commutes with coefficient scaling, elementwise. -/
theorem torusSumEquiv_incTorusScale (a : ℂ) (x : (G.disjointSum H).IncTorusRing) :
    G.torusSumEquiv H ((G.disjointSum H).incTorusScale a x) =
      Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a) (G.torusSumEquiv H x) :=
  AlgHom.congr_fun (G.torusSumEquiv_comp_incTorusScale H a) x

/-- **The tensor formula commutes with coefficient scaling**: `𝒰_{G⊔H} ≃ 𝒰_G ⊗ 𝒰_H` intertwines
coefficient scaling with the tensor product of the coefficient scalings. -/
theorem incidenceSumEquiv_incidenceScale (a : ℂ) (x : (G.disjointSum H).IncidenceRing) :
    G.incidenceSumEquiv H ((G.disjointSum H).incidenceScale a x) =
      Algebra.TensorProduct.map (G.incidenceScale a) (H.incidenceScale a)
        (G.incidenceSumEquiv H x) := by
  apply incidenceTensorIncl_injective G H
  rw [incidenceTensorIncl_incidenceSumEquiv, incidenceScale_val, torusSumEquiv_incTorusScale,
    ← incidenceTensorIncl_incidenceSumEquiv]
  have h : (Algebra.TensorProduct.map (G.incTorusScale a) (H.incTorusScale a)).comp
        (incidenceTensorIncl G H) =
      (incidenceTensorIncl G H).comp
        (Algebra.TensorProduct.map (G.incidenceScale a) (H.incidenceScale a)) := by
    rw [incidenceTensorIncl, ← Algebra.TensorProduct.map_comp, ← Algebra.TensorProduct.map_comp]
    rfl
  exact AlgHom.congr_fun h _

end Scaling

/-! ### The tensor formula is graded -/

/-- The lexicographic linear order on the edges `E ⊕ F` of a disjoint union (edges of the first
summand first). It is only used to form the natural grading of `𝒰_{G⊔H}`, which is the weight
decomposition of coefficient scaling (`mem_incidenceCoefficientPiece_iff_scale`); a comparison of
the pieces for two different orders is not formalized. -/
abbrev disjointSumEdgeOrder (E F : Type) [LinearOrder E] [LinearOrder F] : LinearOrder (E ⊕ F) :=
  Sum.Lex.linearOrder

section Grading

variable {V W E F : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  [DecidableEq W] [Fintype W] [LinearOrder F] [Fintype F]
  (G : Multigraph V E) (H : Multigraph W F)

attribute [local instance] disjointSumEdgeOrder incidenceCoefficientGradedAlgebra

/-- The bidegree-`(i, j)` part of `𝒰_G ⊗ 𝒰_H`: the span of the products `y ⊗ z` with `y` of
natural degree `i` and `z` of natural degree `j`. -/
noncomputable def incidenceTensorBipiece (i j : ℕ) :
    Submodule ℂ (G.IncidenceRing ⊗[ℂ] H.IncidenceRing) :=
  Submodule.map₂ (TensorProduct.mk ℂ G.IncidenceRing H.IncidenceRing)
    (G.incidenceCoefficientPiece i) (H.incidenceCoefficientPiece j)

/-- The degree-`n` part of `𝒰_G ⊗ 𝒰_H` for the total natural degree: the sum of the bidegree
`(i, j)` parts with `i + j = n`. -/
noncomputable def incidenceTensorPiece (n : ℕ) :
    Submodule ℂ (G.IncidenceRing ⊗[ℂ] H.IncidenceRing) :=
  ⨆ (i : ℕ) (j : ℕ) (_ : i + j = n), incidenceTensorBipiece G H i j

/-- **Products of homogeneous sections.** Under the inverse tensor isomorphism, `y ⊗ z` with `y`
of degree `i` and `z` of degree `j` has degree `i + j` in `𝒰_{G⊔H}`. -/
theorem incidenceSumEquiv_symm_tmul_mem {i j : ℕ} {y : G.IncidenceRing} {z : H.IncidenceRing}
    (hy : y ∈ G.incidenceCoefficientPiece i) (hz : z ∈ H.incidenceCoefficientPiece j) :
    (G.incidenceSumEquiv H).symm (y ⊗ₜ[ℂ] z) ∈
      (G.disjointSum H).incidenceCoefficientPiece (i + j) := by
  rw [mem_incidenceCoefficientPiece_iff_scale] at hy hz ⊢
  intro a
  apply (G.incidenceSumEquiv H).injective
  rw [incidenceSumEquiv_incidenceScale, AlgEquiv.apply_symm_apply,
    show G.incidenceSumEquiv H (a ^ (i + j) • (G.incidenceSumEquiv H).symm (y ⊗ₜ[ℂ] z)) =
        a ^ (i + j) • G.incidenceSumEquiv H ((G.incidenceSumEquiv H).symm (y ⊗ₜ[ℂ] z)) from
      (G.incidenceSumEquiv H).toLinearMap.map_smul _ _,
    AlgEquiv.apply_symm_apply, Algebra.TensorProduct.map_tmul, hy a, hz a, smul_tmul_smul,
    pow_add]

/-- The inverse tensor isomorphism sends the bidegree-`(i, j)` part into degree `i + j`. -/
theorem incidenceSumEquiv_symm_mem_of_mem_bipiece {i j : ℕ}
    {t : G.IncidenceRing ⊗[ℂ] H.IncidenceRing} (ht : t ∈ incidenceTensorBipiece G H i j) :
    (G.incidenceSumEquiv H).symm t ∈ (G.disjointSum H).incidenceCoefficientPiece (i + j) := by
  have hle : incidenceTensorBipiece G H i j ≤
      ((G.disjointSum H).incidenceCoefficientPiece (i + j)).comap
        (G.incidenceSumEquiv H).symm.toLinearMap :=
    Submodule.map₂_le.mpr fun y hy z hz => G.incidenceSumEquiv_symm_tmul_mem H hy hz
  exact hle ht

/-- The bidegree parts span `𝒰_G ⊗ 𝒰_H`. -/
theorem iSup_incidenceTensorBipiece :
    ⨆ ij : ℕ × ℕ, incidenceTensorBipiece G H ij.1 ij.2 = ⊤ := by
  rw [iSup_prod]
  simp_rw [incidenceTensorBipiece, ← Submodule.map₂_iSup_right, ← Submodule.map₂_iSup_left,
    G.iSup_incidenceCoefficientPiece, H.iSup_incidenceCoefficientPiece]
  exact TensorProduct.map₂_mk_top_top_eq_top ℂ _ _

/-- **The tensor formula is graded.** The isomorphism `𝒰_{G⊔H} ≃ 𝒰_G ⊗ 𝒰_H` carries the natural
degree-`n` piece of `𝒰_{G⊔H}` onto the span of the products `y ⊗ z` of homogeneous sections of
degrees `i` and `j` with `i + j = n`. -/
theorem map_incidenceCoefficientPiece_disjointSum (n : ℕ) :
    ((G.disjointSum H).incidenceCoefficientPiece n).map (G.incidenceSumEquiv H).toLinearMap =
      incidenceTensorPiece G H n := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hz : G.incidenceSumEquiv H x ∈ ⨆ ij : ℕ × ℕ, incidenceTensorBipiece G H ij.1 ij.2 := by
      rw [iSup_incidenceTensorBipiece]
      trivial
    obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hz
    have h1 : x = ∑ ij ∈ f.support, (G.incidenceSumEquiv H).symm (f ij) := by
      have h0 : (G.incidenceSumEquiv H).symm (f.sum fun _ t => t) = x := by
        rw [hsum, AlgEquiv.symm_apply_apply]
      rw [← h0, Finsupp.sum, map_sum]
    have hx' : x = ∑ ij ∈ f.support.filter (fun ij => ij.1 + ij.2 = n),
        (G.incidenceSumEquiv H).symm (f ij) := by
      have hproj : GradedAlgebra.proj (G.disjointSum H).incidenceCoefficientPiece n x = x := by
        rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same _ hx]
      rw [← hproj, h1, map_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [GradedAlgebra.proj_apply]
      have hmem := G.incidenceSumEquiv_symm_mem_of_mem_bipiece H (hf ij)
      split_ifs with h
      · rw [← h]
        exact DirectSum.decompose_of_mem_same _ hmem
      · exact DirectSum.decompose_of_mem_ne _ hmem h
    change G.incidenceSumEquiv H x ∈ _
    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun ij hij => ?_
    rw [AlgEquiv.apply_symm_apply]
    exact Submodule.mem_iSup_of_mem ij.1 (Submodule.mem_iSup_of_mem ij.2
      (Submodule.mem_iSup_of_mem (Finset.mem_filter.mp hij).2 (hf ij)))
  · refine iSup_le fun i => iSup_le fun j => iSup_le fun hij t ht =>
      ⟨(G.incidenceSumEquiv H).symm t, ?_, ?_⟩
    · have hmem := G.incidenceSumEquiv_symm_mem_of_mem_bipiece H ht
      rwa [hij] at hmem
    · exact (G.incidenceSumEquiv H).apply_symm_apply t

/-- Membership form of the graded tensor formula. -/
theorem incidenceSumEquiv_mem_incidenceTensorPiece_iff (n : ℕ)
    (x : (G.disjointSum H).IncidenceRing) :
    G.incidenceSumEquiv H x ∈ incidenceTensorPiece G H n ↔
      x ∈ (G.disjointSum H).incidenceCoefficientPiece n := by
  rw [← map_incidenceCoefficientPiece_disjointSum]
  constructor
  · rintro ⟨y, hy, hxy⟩
    rwa [(G.incidenceSumEquiv H).injective hxy] at hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-! #### Bidegree decomposition of `𝒰_G ⊗ 𝒰_H` -/

/-- The projection of `𝒰_G ⊗ 𝒰_H` onto bidegree `(k, l)`: the tensor product of the projections
onto the homogeneous components. -/
noncomputable def incidenceTensorProj (k l : ℕ) :
    G.IncidenceRing ⊗[ℂ] H.IncidenceRing →ₗ[ℂ] G.IncidenceRing ⊗[ℂ] H.IncidenceRing :=
  TensorProduct.map (GradedAlgebra.proj G.incidenceCoefficientPiece k)
    (GradedAlgebra.proj H.incidenceCoefficientPiece l)

/-- The bidegree projections act on the bidegree parts as the identity or zero. -/
theorem incidenceTensorProj_of_mem_bipiece {i j : ℕ} (k l : ℕ)
    {t : G.IncidenceRing ⊗[ℂ] H.IncidenceRing} (ht : t ∈ incidenceTensorBipiece G H i j) :
    incidenceTensorProj G H k l t = if (i, j) = (k, l) then t else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    have hle : incidenceTensorBipiece G H i j ≤
        LinearMap.eqLocus (incidenceTensorProj G H i j) LinearMap.id := by
      refine Submodule.map₂_le.mpr fun y hy z hz => ?_
      rw [LinearMap.mem_eqLocus, TensorProduct.mk_apply, incidenceTensorProj,
        TensorProduct.map_tmul, GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
        DirectSum.decompose_of_mem_same _ hy, DirectSum.decompose_of_mem_same _ hz]
      rfl
    exact LinearMap.mem_eqLocus.mp (hle ht)
  · have hle : incidenceTensorBipiece G H i j ≤ LinearMap.ker (incidenceTensorProj G H k l) := by
      refine Submodule.map₂_le.mpr fun y hy z hz => ?_
      rw [LinearMap.mem_ker, TensorProduct.mk_apply, incidenceTensorProj,
        TensorProduct.map_tmul, GradedAlgebra.proj_apply, GradedAlgebra.proj_apply]
      by_cases hik : i = k
      · have hjl : j ≠ l := fun hjl => h (by rw [hik, hjl])
        rw [DirectSum.decompose_of_mem_ne _ hz hjl, tmul_zero]
      · rw [DirectSum.decompose_of_mem_ne _ hy hik, zero_tmul]
    exact LinearMap.mem_ker.mp (hle ht)

/-- **The bidegree parts of `𝒰_G ⊗ 𝒰_H` are independent.** -/
theorem iSupIndep_incidenceTensorBipiece :
    iSupIndep fun ij : ℕ × ℕ => incidenceTensorBipiece G H ij.1 ij.2 := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum kl hkl
  have h := congrArg (incidenceTensorProj G H kl.1 kl.2) hsum
  rw [map_sum, map_zero, Finset.sum_congr rfl fun ij hij =>
    G.incidenceTensorProj_of_mem_bipiece H kl.1 kl.2 (hv ij hij)] at h
  simpa [Prod.mk.eta, hkl] using h

/-- Over `ℂ`, `𝒰_{G,i} ⊗ 𝒰_{H,j} → 𝒰_G ⊗ 𝒰_H` is injective. -/
theorem mapIncl_incidenceCoefficientPiece_injective (i j : ℕ) :
    Function.Injective (TensorProduct.mapIncl (G.incidenceCoefficientPiece i)
      (H.incidenceCoefficientPiece j)) := by
  have : Module.Flat ℂ G.IncidenceRing := Module.Flat.of_free
  have : Module.Free ℂ (H.incidenceCoefficientPiece j) := Module.Free.of_divisionRing ℂ _
  have : Module.Flat ℂ (H.incidenceCoefficientPiece j) := Module.Flat.of_free
  exact TensorProduct.map_injective_of_flat_flat _ _ Subtype.val_injective Subtype.val_injective

/-- `𝒰_{G,i} ⊗ 𝒰_{H,j}` is the bidegree-`(i, j)` part of `𝒰_G ⊗ 𝒰_H`. -/
noncomputable def incidenceTensorBipieceEquiv (i j : ℕ) :
    (G.incidenceCoefficientPiece i ⊗[ℂ] H.incidenceCoefficientPiece j) ≃ₗ[ℂ]
      incidenceTensorBipiece G H i j :=
  (LinearEquiv.ofInjective _ (G.mapIncl_incidenceCoefficientPiece_injective H i j)).trans
    (LinearEquiv.ofEq _ _ (TensorProduct.range_mapIncl _ _))

@[simp] theorem incidenceTensorBipieceEquiv_tmul {i j : ℕ}
    (y : G.incidenceCoefficientPiece i) (z : H.incidenceCoefficientPiece j) :
    (incidenceTensorBipieceEquiv G H i j (y ⊗ₜ[ℂ] z) : G.IncidenceRing ⊗[ℂ] H.IncidenceRing) =
      (y : G.IncidenceRing) ⊗ₜ[ℂ] (z : H.IncidenceRing) := rfl

/-- The degree-`n` part of `𝒰_G ⊗ 𝒰_H` as a supremum over the antidiagonal subtype. -/
theorem incidenceTensorPiece_eq_iSup_subtype (n : ℕ) :
    incidenceTensorPiece G H n =
      ⨆ ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n}, incidenceTensorBipiece G H ij.1.1 ij.1.2 := by
  rw [iSup_subtype, iSup_prod]
  rfl

/-- **The graded tensor formula.** The natural degree-`n` piece of `𝒰_{G⊔H}` is isomorphic to
`⨁_{i+j=n} 𝒰_{G,i} ⊗ 𝒰_{H,j}`, through the tensor formula `incidenceSumEquiv`. -/
noncomputable def incidenceSumPieceEquiv (n : ℕ) :
    (G.disjointSum H).incidenceCoefficientPiece n ≃ₗ[ℂ]
      ⨁ ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n},
        (G.incidenceCoefficientPiece ij.1.1 ⊗[ℂ] H.incidenceCoefficientPiece ij.1.2) :=
  let p : {ij : ℕ × ℕ // ij.1 + ij.2 = n} → Submodule ℂ (G.IncidenceRing ⊗[ℂ] H.IncidenceRing) :=
    fun ij => incidenceTensorBipiece G H ij.1.1 ij.1.2
  have hindep : iSupIndep p :=
    (G.iSupIndep_incidenceTensorBipiece H).comp Subtype.val_injective
  have hrange : ((G.disjointSum H).incidenceCoefficientPiece n).map
      (G.incidenceSumEquiv H).toLinearEquiv.toLinearMap =
      LinearMap.range (DFinsupp.lsum ℕ fun ij => (p ij).subtype) := by
    rw [← Submodule.iSup_eq_range_dfinsupp_lsum, ← incidenceTensorPiece_eq_iSup_subtype,
      ← map_incidenceCoefficientPiece_disjointSum]
  (((G.incidenceSumEquiv H).toLinearEquiv.submoduleMap _).trans
    ((LinearEquiv.ofEq _ _ hrange).trans
      (LinearEquiv.ofInjective _ hindep.dfinsupp_lsum_injective).symm)).trans
    (DFinsupp.mapRange.linearEquiv fun ij => (incidenceTensorBipieceEquiv G H ij.1.1 ij.1.2).symm)

/-- The inverse of the graded tensor formula sends `y ⊗ z` in the summand `(i, j)` to the
corresponding product section of `𝒰_{G⊔H}`. -/
theorem incidenceSumPieceEquiv_symm_of_tmul (n : ℕ) (ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n})
    (y : G.incidenceCoefficientPiece ij.1.1) (z : H.incidenceCoefficientPiece ij.1.2) :
    ((G.incidenceSumPieceEquiv H n).symm (DirectSum.of _ ij (y ⊗ₜ[ℂ] z)) :
        (G.disjointSum H).IncidenceRing) =
      (G.incidenceSumEquiv H).symm ((y : G.IncidenceRing) ⊗ₜ[ℂ] (z : H.IncidenceRing)) := by
  classical
  apply (G.incidenceSumEquiv H).injective
  rw [AlgEquiv.apply_symm_apply]
  have key : ∀ v : ((G.disjointSum H).incidenceCoefficientPiece n).map
      (G.incidenceSumEquiv H).toLinearEquiv.toLinearMap,
      G.incidenceSumEquiv H
        (((G.incidenceSumEquiv H).toLinearEquiv.submoduleMap _).symm v :
          (G.disjointSum H).IncidenceRing) = v :=
    fun v => congrArg Subtype.val (LinearEquiv.apply_symm_apply
      ((G.incidenceSumEquiv H).toLinearEquiv.submoduleMap
        ((G.disjointSum H).incidenceCoefficientPiece n)) v)
  have hD : (DFinsupp.mapRange.linearEquiv fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
      (incidenceTensorBipieceEquiv G H ij.1.1 ij.1.2).symm).symm
        (DirectSum.of (fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
          G.incidenceCoefficientPiece ij.1.1 ⊗[ℂ] H.incidenceCoefficientPiece ij.1.2) ij
          (y ⊗ₜ[ℂ] z)) =
      DFinsupp.single ij (incidenceTensorBipieceEquiv G H ij.1.1 ij.1.2 (y ⊗ₜ[ℂ] z)) :=
    DFinsupp.mapRange_single (hf := fun _ => LinearEquiv.map_zero _)
  refine (key _).trans ?_
  change (DFinsupp.lsum ℕ fun i : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
      (incidenceTensorBipiece G H i.1.1 i.1.2).subtype)
      ((DFinsupp.mapRange.linearEquiv fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
        (incidenceTensorBipieceEquiv G H ij.1.1 ij.1.2).symm).symm
        (DirectSum.of (fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
          G.incidenceCoefficientPiece ij.1.1 ⊗[ℂ] H.incidenceCoefficientPiece ij.1.2) ij
          (y ⊗ₜ[ℂ] z))) = _
  rw [hD, DFinsupp.lsum_single]
  rfl

end Grading

end BPFixedPoints.Multigraph
