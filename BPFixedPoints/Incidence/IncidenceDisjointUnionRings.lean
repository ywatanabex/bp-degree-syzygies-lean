import BPFixedPoints.Incidence.Torus

/-!
# Disjoint unions of multigraphs and the tensor decomposition of their incidence rings

`Multigraph.disjointSum G H : Multigraph (V ⊕ W) (E ⊕ F)` is the disjoint union: each edge keeps
its ordered endpoint pair inside its own summand. We record its basic combinatorial API (endpoints,
loops, incidence, endpoint counts and degrees).

For the ring-theoretic side we first prove two general facts about polynomial rings over `ℂ` in a
disjoint union of variable sets `Y ≃ Y₁ ⊕ Y₂`:
* `polySumEquiv`: `ℂ[Y] ≃ ℂ[Y₁] ⊗ ℂ[Y₂]`;
* `quotSumEquiv`: if the relation family on `Y` is the disjoint union of relation families on `Y₁`
  and `Y₂` (renamed), then the quotient is the tensor product of the two quotients.
Both are built directly from generators, with explicit inverse maps.

Applied to a disjoint union these give
* `coeffSumEquiv : IncCoeffRing (E ⊕ F) ≃ₐ[ℂ] IncCoeffRing E ⊗[ℂ] IncCoeffRing F`,
* `chartSumEquiv σ : (G.disjointSum H).IncChartRing σ ≃ₐ[ℂ]
    G.IncChartRing (σ ∘ Sum.inl) ⊗[ℂ] H.IncChartRing (σ ∘ Sum.inr)`,
* `torusSumEquiv : (G.disjointSum H).IncTorusRing ≃ₐ[ℂ] G.IncTorusRing ⊗[ℂ] H.IncTorusRing`,
and the torus isomorphism intertwines the chart restriction at `σ` with the tensor product of the
chart restrictions at `σ ∘ Sum.inl` and `σ ∘ Sum.inr` (`torusSumEquiv_incChartMap`). On
generators it sends each vertex coordinate, inverse coordinate and coefficient of a summand to the
same generator in the corresponding tensor factor (`torusSumEquiv_t_inl`, ...,
`torusSumEquiv_coeff_inr`).

The incidence ring itself is treated in `IncidenceDisjointUnion.lean`. No grading statement, and no
statement about the sheaf-theoretic incidence scheme, is made here.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial
open scoped TensorProduct

/-! ### The disjoint union of two multigraphs -/

section Graph

variable {V W E F : Type*}

/-- **Disjoint union of multigraphs.** The vertex type is `V ⊕ W` and the edge type `E ⊕ F`; every
edge keeps its ordered endpoint pair inside its own summand. -/
def disjointSum (G : Multigraph V E) (H : Multigraph W F) : Multigraph (V ⊕ W) (E ⊕ F) where
  fst := Sum.map G.fst H.fst
  snd := Sum.map G.snd H.snd

variable (G : Multigraph V E) (H : Multigraph W F)

@[simp] theorem disjointSum_fst_inl (e : E) :
    (G.disjointSum H).fst (Sum.inl e) = Sum.inl (G.fst e) := rfl

@[simp] theorem disjointSum_fst_inr (f : F) :
    (G.disjointSum H).fst (Sum.inr f) = Sum.inr (H.fst f) := rfl

@[simp] theorem disjointSum_snd_inl (e : E) :
    (G.disjointSum H).snd (Sum.inl e) = Sum.inl (G.snd e) := rfl

@[simp] theorem disjointSum_snd_inr (f : F) :
    (G.disjointSum H).snd (Sum.inr f) = Sum.inr (H.snd f) := rfl

@[simp] theorem disjointSum_isLoop_inl (e : E) :
    (G.disjointSum H).IsLoop (Sum.inl e) ↔ G.IsLoop e := by
  simp [IsLoop]

@[simp] theorem disjointSum_isLoop_inr (f : F) :
    (G.disjointSum H).IsLoop (Sum.inr f) ↔ H.IsLoop f := by
  simp [IsLoop]

/-- A disjoint union is loopless iff both summands are. -/
theorem loopless_disjointSum_iff : (G.disjointSum H).Loopless ↔ G.Loopless ∧ H.Loopless := by
  constructor
  · intro h
    exact ⟨fun e he => h (Sum.inl e) (by simpa using he),
      fun f hf => h (Sum.inr f) (by simpa using hf)⟩
  · rintro ⟨hG, hH⟩ (e | f) h
    · exact hG e (by simpa using h)
    · exact hH f (by simpa using h)

@[simp] theorem disjointSum_incident_inl_inl (e : E) (v : V) :
    (G.disjointSum H).Incident (Sum.inl e) (Sum.inl v) ↔ G.Incident e v := by
  simp [Incident]

@[simp] theorem disjointSum_incident_inr_inr (f : F) (w : W) :
    (G.disjointSum H).Incident (Sum.inr f) (Sum.inr w) ↔ H.Incident f w := by
  simp [Incident]

@[simp] theorem disjointSum_not_incident_inl_inr (e : E) (w : W) :
    ¬ (G.disjointSum H).Incident (Sum.inl e) (Sum.inr w) := by
  simp [Incident]

@[simp] theorem disjointSum_not_incident_inr_inl (f : F) (v : V) :
    ¬ (G.disjointSum H).Incident (Sum.inr f) (Sum.inl v) := by
  simp [Incident]

section Degree

variable [DecidableEq V] [DecidableEq W]

@[simp] theorem disjointSum_endCount_inl_inl (e : E) (v : V) :
    (G.disjointSum H).endCount (Sum.inl e) (Sum.inl v) = G.endCount e v := by
  simp [endCount]

@[simp] theorem disjointSum_endCount_inr_inr (f : F) (w : W) :
    (G.disjointSum H).endCount (Sum.inr f) (Sum.inr w) = H.endCount f w := by
  simp [endCount]

@[simp] theorem disjointSum_endCount_inl_inr (e : E) (w : W) :
    (G.disjointSum H).endCount (Sum.inl e) (Sum.inr w) = 0 := by
  simp [endCount]

@[simp] theorem disjointSum_endCount_inr_inl (f : F) (v : V) :
    (G.disjointSum H).endCount (Sum.inr f) (Sum.inl v) = 0 := by
  simp [endCount]

/-- Degrees in a disjoint union of edge sets, at a vertex of the first summand. -/
theorem disjointSum_deg_inl (S : Finset E) (T : Finset F) (v : V) :
    (G.disjointSum H).deg (S.disjSum T) (Sum.inl v) = G.deg S v := by
  simp [deg, Finset.sum_disjSum]

/-- Degrees in a disjoint union of edge sets, at a vertex of the second summand. -/
theorem disjointSum_deg_inr (S : Finset E) (T : Finset F) (w : W) :
    (G.disjointSum H).deg (S.disjSum T) (Sum.inr w) = H.deg T w := by
  simp [deg, Finset.sum_disjSum]

end Degree

end Graph

/-! ### Polynomial rings and their quotients in a disjoint union of variables -/

section PolynomialSum

variable {Y₁ Y₂ Y : Type*} (e : Y₁ ⊕ Y₂ ≃ Y)

/-- Split a polynomial in the variables `Y ≃ Y₁ ⊕ Y₂` into the tensor product of the polynomial
rings in `Y₁` and in `Y₂`. -/
noncomputable def polySumToTensor :
    MvPolynomial Y ℂ →ₐ[ℂ] MvPolynomial Y₁ ℂ ⊗[ℂ] MvPolynomial Y₂ ℂ :=
  aeval fun y => Sum.elim (fun a => X a ⊗ₜ[ℂ] (1 : MvPolynomial Y₂ ℂ))
    (fun b => (1 : MvPolynomial Y₁ ℂ) ⊗ₜ[ℂ] X b) (e.symm y)

/-- Multiply the two factors back into the polynomial ring in `Y`. -/
noncomputable def polyTensorToSum :
    MvPolynomial Y₁ ℂ ⊗[ℂ] MvPolynomial Y₂ ℂ →ₐ[ℂ] MvPolynomial Y ℂ :=
  Algebra.TensorProduct.lift (rename (e ∘ Sum.inl)) (rename (e ∘ Sum.inr))
    fun _ _ => Commute.all _ _

@[simp] theorem polySumToTensor_X_inl (a : Y₁) :
    polySumToTensor e (X (e (Sum.inl a))) = X a ⊗ₜ[ℂ] (1 : MvPolynomial Y₂ ℂ) := by
  simp [polySumToTensor]

@[simp] theorem polySumToTensor_X_inr (b : Y₂) :
    polySumToTensor e (X (e (Sum.inr b))) = (1 : MvPolynomial Y₁ ℂ) ⊗ₜ[ℂ] X b := by
  simp [polySumToTensor]

theorem polySumToTensor_comp_rename_inl :
    (polySumToTensor e).comp (rename (e ∘ Sum.inl)) = Algebra.TensorProduct.includeLeft := by
  apply MvPolynomial.algHom_ext
  intro a
  simp

theorem polySumToTensor_comp_rename_inr :
    (polySumToTensor e).comp (rename (e ∘ Sum.inr)) =
      (Algebra.TensorProduct.includeRight : MvPolynomial Y₂ ℂ →ₐ[ℂ] _) := by
  apply MvPolynomial.algHom_ext
  intro b
  simp

@[simp] theorem polySumToTensor_rename_inl (p : MvPolynomial Y₁ ℂ) :
    polySumToTensor e (rename (e ∘ Sum.inl) p) = p ⊗ₜ[ℂ] (1 : MvPolynomial Y₂ ℂ) :=
  AlgHom.congr_fun (polySumToTensor_comp_rename_inl e) p

@[simp] theorem polySumToTensor_rename_inr (p : MvPolynomial Y₂ ℂ) :
    polySumToTensor e (rename (e ∘ Sum.inr) p) = (1 : MvPolynomial Y₁ ℂ) ⊗ₜ[ℂ] p :=
  AlgHom.congr_fun (polySumToTensor_comp_rename_inr e) p

/-- **Polynomial rings in a disjoint union of variables.** `ℂ[Y] ≃ ℂ[Y₁] ⊗ ℂ[Y₂]` for
`Y ≃ Y₁ ⊕ Y₂`. -/
noncomputable def polySumEquiv :
    MvPolynomial Y ℂ ≃ₐ[ℂ] MvPolynomial Y₁ ℂ ⊗[ℂ] MvPolynomial Y₂ ℂ :=
  AlgEquiv.ofAlgHom (polySumToTensor e) (polyTensorToSum e)
    (by
      apply Algebra.TensorProduct.ext
      · apply MvPolynomial.algHom_ext
        intro a
        simp [polyTensorToSum]
      · apply MvPolynomial.algHom_ext
        intro b
        simp [polyTensorToSum])
    (by
      apply MvPolynomial.algHom_ext
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      rcases z with a | b <;> simp [polyTensorToSum])

@[simp] theorem polySumEquiv_apply (p : MvPolynomial Y ℂ) :
    polySumEquiv e p = polySumToTensor e p := rfl

@[simp] theorem polySumEquiv_symm_tmul (p : MvPolynomial Y₁ ℂ) (q : MvPolynomial Y₂ ℂ) :
    (polySumEquiv e).symm (p ⊗ₜ[ℂ] q) = rename (e ∘ Sum.inl) p * rename (e ∘ Sum.inr) q := by
  change polyTensorToSum e (p ⊗ₜ[ℂ] q) = _
  simp [polyTensorToSum]

variable {ι₁ ι₂ ι : Type*} (s : ι₁ ⊕ ι₂ ≃ ι)
  (r₁ : ι₁ → MvPolynomial Y₁ ℂ) (r₂ : ι₂ → MvPolynomial Y₂ ℂ) (r : ι → MvPolynomial Y ℂ)
  (hr₁ : ∀ i, r (s (Sum.inl i)) = rename (e ∘ Sum.inl) (r₁ i))
  (hr₂ : ∀ i, r (s (Sum.inr i)) = rename (e ∘ Sum.inr) (r₂ i))

/-- The quotient map attached to a relation family on `Y` that is the disjoint union of renamed
relation families on `Y₁` and `Y₂`. -/
noncomputable def quotSumToTensor :
    MvPolynomial Y ℂ ⧸ Ideal.span (Set.range r) →ₐ[ℂ]
      (MvPolynomial Y₁ ℂ ⧸ Ideal.span (Set.range r₁)) ⊗[ℂ]
        (MvPolynomial Y₂ ℂ ⧸ Ideal.span (Set.range r₂)) :=
  Ideal.Quotient.liftₐ _
    ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ ℂ _) (Ideal.Quotient.mkₐ ℂ _)).comp
      (polySumToTensor e)) fun p hp => by
    have hle : Ideal.span (Set.range r) ≤ RingHom.ker
        ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ ℂ (Ideal.span (Set.range r₁)))
          (Ideal.Quotient.mkₐ ℂ (Ideal.span (Set.range r₂)))).comp (polySumToTensor e)) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨j, rfl⟩ := s.surjective i
      rw [SetLike.mem_coe, RingHom.mem_ker]
      rcases j with i₁ | i₂
      · have h0 : Ideal.Quotient.mk (Ideal.span (Set.range r₁)) (r₁ i₁) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i₁, rfl⟩)
        rw [hr₁]
        simp only [AlgHom.coe_comp, Function.comp_apply, polySumToTensor_rename_inl,
          Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, h0, TensorProduct.zero_tmul]
      · have h0 : Ideal.Quotient.mk (Ideal.span (Set.range r₂)) (r₂ i₂) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i₂, rfl⟩)
        rw [hr₂]
        simp only [AlgHom.coe_comp, Function.comp_apply, polySumToTensor_rename_inr,
          Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, h0, TensorProduct.tmul_zero]
    exact (RingHom.mem_ker).1 (hle hp)

theorem quotSumToTensor_mk (p : MvPolynomial Y ℂ) :
    quotSumToTensor e s r₁ r₂ r hr₁ hr₂ (Ideal.Quotient.mk (Ideal.span (Set.range r)) p) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ ℂ (Ideal.span (Set.range r₁)))
        (Ideal.Quotient.mkₐ ℂ (Ideal.span (Set.range r₂))) (polySumToTensor e p) := rfl

theorem quotSumToTensor_mk_rename_inl (p : MvPolynomial Y₁ ℂ) :
    quotSumToTensor e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r)) (rename (e ∘ Sum.inl) p)) =
      Ideal.Quotient.mk (Ideal.span (Set.range r₁)) p ⊗ₜ[ℂ] 1 := by
  rw [quotSumToTensor_mk, polySumToTensor_rename_inl, Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem quotSumToTensor_mk_rename_inr (q : MvPolynomial Y₂ ℂ) :
    quotSumToTensor e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r)) (rename (e ∘ Sum.inr) q)) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk (Ideal.span (Set.range r₂)) q := by
  rw [quotSumToTensor_mk, polySumToTensor_rename_inr, Algebra.TensorProduct.map_tmul, map_one]
  rfl

/-- The inverse of `quotSumToTensor`: rename each factor into `Y` and multiply. -/
noncomputable def quotTensorToSum :
    (MvPolynomial Y₁ ℂ ⧸ Ideal.span (Set.range r₁)) ⊗[ℂ]
        (MvPolynomial Y₂ ℂ ⧸ Ideal.span (Set.range r₂)) →ₐ[ℂ]
      MvPolynomial Y ℂ ⧸ Ideal.span (Set.range r) :=
  Algebra.TensorProduct.lift
    (Ideal.quotientMapₐ _ (rename (e ∘ Sum.inl)) (by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, ← hr₁]
      exact Ideal.subset_span ⟨_, rfl⟩))
    (Ideal.quotientMapₐ _ (rename (e ∘ Sum.inr)) (by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, ← hr₂]
      exact Ideal.subset_span ⟨_, rfl⟩))
    fun _ _ => Commute.all _ _

theorem quotTensorToSum_tmul (p : MvPolynomial Y₁ ℂ) (q : MvPolynomial Y₂ ℂ) :
    quotTensorToSum e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r₁)) p ⊗ₜ[ℂ]
          Ideal.Quotient.mk (Ideal.span (Set.range r₂)) q) =
      Ideal.Quotient.mk (Ideal.span (Set.range r))
        (rename (e ∘ Sum.inl) p * rename (e ∘ Sum.inr) q) := by
  rw [quotTensorToSum, Algebra.TensorProduct.lift_tmul, Ideal.quotient_map_mkₐ,
    Ideal.quotient_map_mkₐ, map_mul]
  rfl

theorem quotTensorToSum_tmul_one (p : MvPolynomial Y₁ ℂ) :
    quotTensorToSum e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r₁)) p ⊗ₜ[ℂ] 1) =
      Ideal.Quotient.mk (Ideal.span (Set.range r)) (rename (e ∘ Sum.inl) p) := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span (Set.range r₂))), quotTensorToSum_tmul, map_one,
    mul_one]

theorem quotTensorToSum_one_tmul (q : MvPolynomial Y₂ ℂ) :
    quotTensorToSum e s r₁ r₂ r hr₁ hr₂
        (1 ⊗ₜ[ℂ] Ideal.Quotient.mk (Ideal.span (Set.range r₂)) q) =
      Ideal.Quotient.mk (Ideal.span (Set.range r)) (rename (e ∘ Sum.inr) q) := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span (Set.range r₁))), quotTensorToSum_tmul, map_one,
    one_mul]

/-- **Quotients in a disjoint union of variables.** If the relations on `Y ≃ Y₁ ⊕ Y₂` are the
disjoint union of renamed relations on `Y₁` and on `Y₂`, the quotient ring is the tensor product of
the two quotient rings. -/
noncomputable def quotSumEquiv :
    (MvPolynomial Y ℂ ⧸ Ideal.span (Set.range r)) ≃ₐ[ℂ]
      (MvPolynomial Y₁ ℂ ⧸ Ideal.span (Set.range r₁)) ⊗[ℂ]
        (MvPolynomial Y₂ ℂ ⧸ Ideal.span (Set.range r₂)) :=
  AlgEquiv.ofAlgHom (quotSumToTensor e s r₁ r₂ r hr₁ hr₂) (quotTensorToSum e s r₁ r₂ r hr₁ hr₂)
    (by
      apply Algebra.TensorProduct.ext
      · apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro a
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Algebra.TensorProduct.includeLeft_apply, quotTensorToSum_tmul_one, AlgHom.id_apply]
        rw [quotSumToTensor_mk_rename_inl]
      · apply Ideal.Quotient.algHom_ext
        apply MvPolynomial.algHom_ext
        intro b
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply, quotTensorToSum_one_tmul, AlgHom.id_apply]
        rw [quotSumToTensor_mk_rename_inr])
    (by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro y
      obtain ⟨z, rfl⟩ := e.surjective y
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.id_apply]
      rcases z with a | b
      · have := quotSumToTensor_mk_rename_inl e s r₁ r₂ r hr₁ hr₂ (X a)
        rw [rename_X] at this
        rw [Function.comp_apply] at this
        rw [this, quotTensorToSum_tmul_one, rename_X]
        rfl
      · have := quotSumToTensor_mk_rename_inr e s r₁ r₂ r hr₁ hr₂ (X b)
        rw [rename_X] at this
        rw [Function.comp_apply] at this
        rw [this, quotTensorToSum_one_tmul, rename_X]
        rfl)

@[simp] theorem quotSumEquiv_apply (x : MvPolynomial Y ℂ ⧸ Ideal.span (Set.range r)) :
    quotSumEquiv e s r₁ r₂ r hr₁ hr₂ x = quotSumToTensor e s r₁ r₂ r hr₁ hr₂ x := rfl

@[simp] theorem quotSumEquiv_symm_apply
    (x : (MvPolynomial Y₁ ℂ ⧸ Ideal.span (Set.range r₁)) ⊗[ℂ]
        (MvPolynomial Y₂ ℂ ⧸ Ideal.span (Set.range r₂))) :
    (quotSumEquiv e s r₁ r₂ r hr₁ hr₂).symm x = quotTensorToSum e s r₁ r₂ r hr₁ hr₂ x := rfl

theorem quotSumToTensor_mk_X_inl (a : Y₁) :
    quotSumToTensor e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r)) (X (e (Sum.inl a)))) =
      Ideal.Quotient.mk (Ideal.span (Set.range r₁)) (X a) ⊗ₜ[ℂ] 1 := by
  simpa using quotSumToTensor_mk_rename_inl e s r₁ r₂ r hr₁ hr₂ (X a)

theorem quotSumToTensor_mk_X_inr (b : Y₂) :
    quotSumToTensor e s r₁ r₂ r hr₁ hr₂
        (Ideal.Quotient.mk (Ideal.span (Set.range r)) (X (e (Sum.inr b)))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk (Ideal.span (Set.range r₂)) (X b) := by
  simpa using quotSumToTensor_mk_rename_inr e s r₁ r₂ r hr₁ hr₂ (X b)

end PolynomialSum

/-! ### Coefficient, chart and torus rings of a disjoint union -/

section Rings

variable {V W E F : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq W] [Fintype W] [DecidableEq F] [Fintype F]
  (G : Multigraph V E) (H : Multigraph W F)

/-- Coefficient indices of the summands, placed in the disjoint union. -/
def coeffIdxSumEquiv (E F : Type) : IncCoeffIdx E ⊕ IncCoeffIdx F ≃ IncCoeffIdx (E ⊕ F) where
  toFun
    | Sum.inl (e, ab) => (Sum.inl e, ab)
    | Sum.inr (f, ab) => (Sum.inr f, ab)
  invFun
    | (Sum.inl e, ab) => Sum.inl (e, ab)
    | (Sum.inr f, ab) => Sum.inr (f, ab)
  left_inv := by rintro (⟨e, ab⟩ | ⟨f, ab⟩) <;> rfl
  right_inv := by rintro ⟨e | f, ab⟩ <;> rfl

@[simp] theorem coeffIdxSumEquiv_inl (e : E) (ab : Fin 2 × Fin 2) :
    coeffIdxSumEquiv E F (Sum.inl (e, ab)) = (Sum.inl e, ab) := rfl

@[simp] theorem coeffIdxSumEquiv_inr (f : F) (ab : Fin 2 × Fin 2) :
    coeffIdxSumEquiv E F (Sum.inr (f, ab)) = (Sum.inr f, ab) := rfl

/-- **Coefficient ring of a disjoint union.** `S_{G⊔H} ≃ S_G ⊗ S_H`. -/
noncomputable def coeffSumEquiv (E F : Type) :
    IncCoeffRing (E ⊕ F) ≃ₐ[ℂ] IncCoeffRing E ⊗[ℂ] IncCoeffRing F :=
  polySumEquiv (coeffIdxSumEquiv E F)

@[simp] theorem coeffSumEquiv_X_inl (e : E) (ab : Fin 2 × Fin 2) :
    coeffSumEquiv E F (X (Sum.inl e, ab)) = X (e, ab) ⊗ₜ[ℂ] (1 : IncCoeffRing F) :=
  polySumToTensor_X_inl (coeffIdxSumEquiv E F) (e, ab)

@[simp] theorem coeffSumEquiv_X_inr (f : F) (ab : Fin 2 × Fin 2) :
    coeffSumEquiv E F (X (Sum.inr f, ab)) = (1 : IncCoeffRing E) ⊗ₜ[ℂ] X (f, ab) :=
  polySumToTensor_X_inr (coeffIdxSumEquiv E F) (f, ab)

/-- Chart variables of the summands, placed in the disjoint union. -/
def chartVarSumEquiv (V W E F : Type) :
    IncChartVar V E ⊕ IncChartVar W F ≃ IncChartVar (V ⊕ W) (E ⊕ F) where
  toFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr (e, ab)) => Sum.inr (Sum.inl e, ab)
    | Sum.inr (Sum.inl w) => Sum.inl (Sum.inr w)
    | Sum.inr (Sum.inr (f, ab)) => Sum.inr (Sum.inr f, ab)
  invFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr w) => Sum.inr (Sum.inl w)
    | Sum.inr (Sum.inl e, ab) => Sum.inl (Sum.inr (e, ab))
    | Sum.inr (Sum.inr f, ab) => Sum.inr (Sum.inr (f, ab))
  left_inv := by rintro ((v | ⟨e, ab⟩) | (w | ⟨f, ab⟩)) <;> rfl
  right_inv := by rintro ((v | w) | ⟨e | f, ab⟩) <;> rfl

/-- Torus variables of the summands, placed in the disjoint union. -/
def torusVarSumEquiv (V W E F : Type) :
    IncTorusVar V E ⊕ IncTorusVar W F ≃ IncTorusVar (V ⊕ W) (E ⊕ F) where
  toFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr (Sum.inl v)) => Sum.inr (Sum.inl (Sum.inl v))
    | Sum.inl (Sum.inr (Sum.inr (e, ab))) => Sum.inr (Sum.inr (Sum.inl e, ab))
    | Sum.inr (Sum.inl w) => Sum.inl (Sum.inr w)
    | Sum.inr (Sum.inr (Sum.inl w)) => Sum.inr (Sum.inl (Sum.inr w))
    | Sum.inr (Sum.inr (Sum.inr (f, ab))) => Sum.inr (Sum.inr (Sum.inr f, ab))
  invFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr w) => Sum.inr (Sum.inl w)
    | Sum.inr (Sum.inl (Sum.inl v)) => Sum.inl (Sum.inr (Sum.inl v))
    | Sum.inr (Sum.inl (Sum.inr w)) => Sum.inr (Sum.inr (Sum.inl w))
    | Sum.inr (Sum.inr (Sum.inl e, ab)) => Sum.inl (Sum.inr (Sum.inr (e, ab)))
    | Sum.inr (Sum.inr (Sum.inr f, ab)) => Sum.inr (Sum.inr (Sum.inr (f, ab)))
  left_inv := by
    rintro ((v | v | ⟨e, ab⟩) | (w | w | ⟨f, ab⟩)) <;> rfl
  right_inv := by
    rintro ((v | w) | (v | w) | ⟨e | f, ab⟩) <;> rfl

/-- Torus relation indices of the summands, placed in the disjoint union. -/
def torusRelIdxSumEquiv (V W E F : Type) : (V ⊕ E) ⊕ (W ⊕ F) ≃ (V ⊕ W) ⊕ (E ⊕ F) where
  toFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr e) => Sum.inr (Sum.inl e)
    | Sum.inr (Sum.inl w) => Sum.inl (Sum.inr w)
    | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr f)
  invFun
    | Sum.inl (Sum.inl v) => Sum.inl (Sum.inl v)
    | Sum.inl (Sum.inr w) => Sum.inr (Sum.inl w)
    | Sum.inr (Sum.inl e) => Sum.inl (Sum.inr e)
    | Sum.inr (Sum.inr f) => Sum.inr (Sum.inr f)
  left_inv := by rintro ((v | e) | (w | f)) <;> rfl
  right_inv := by rintro ((v | w) | (e | f)) <;> rfl

/-- The chart equation of an edge of the first summand is the renamed chart equation of `G`. -/
theorem disjointSum_incChartEq_inl (σ : V ⊕ W → Bool) (e : E) :
    (G.disjointSum H).incChartEq σ (Sum.inl e) =
      rename (chartVarSumEquiv V W E F ∘ Sum.inl) (G.incChartEq (σ ∘ Sum.inl) e) := by
  simp only [incChartEq, map_sum, map_mul, rename_X, map_incCoord]
  rfl

/-- The chart equation of an edge of the second summand is the renamed chart equation of `H`. -/
theorem disjointSum_incChartEq_inr (σ : V ⊕ W → Bool) (f : F) :
    (G.disjointSum H).incChartEq σ (Sum.inr f) =
      rename (chartVarSumEquiv V W E F ∘ Sum.inr) (H.incChartEq (σ ∘ Sum.inr) f) := by
  simp only [incChartEq, map_sum, map_mul, rename_X, map_incCoord]
  rfl

/-- The torus relations of the summands, renamed, are the torus relations of the union. -/
theorem disjointSum_incTorusRel_inl (i : V ⊕ E) :
    (G.disjointSum H).incTorusRel (torusRelIdxSumEquiv V W E F (Sum.inl i)) =
      rename (torusVarSumEquiv V W E F ∘ Sum.inl) (G.incTorusRel i) := by
  rcases i with v | e
  · simp only [incTorusRel, map_sub, map_mul, rename_X, map_one]
    rfl
  · change rename _ ((G.disjointSum H).incChartEq (fun _ => false) (Sum.inl e)) = _
    rw [disjointSum_incChartEq_inl, rename_rename]
    simp only [incTorusRel, rename_rename]
    congr 2
    funext w
    rcases w with v | ⟨c, ab⟩ <;> rfl

theorem disjointSum_incTorusRel_inr (i : W ⊕ F) :
    (G.disjointSum H).incTorusRel (torusRelIdxSumEquiv V W E F (Sum.inr i)) =
      rename (torusVarSumEquiv V W E F ∘ Sum.inr) (H.incTorusRel i) := by
  rcases i with w | f
  · simp only [incTorusRel, map_sub, map_mul, rename_X, map_one]
    rfl
  · change rename _ ((G.disjointSum H).incChartEq (fun _ => false) (Sum.inr f)) = _
    rw [disjointSum_incChartEq_inr, rename_rename]
    simp only [incTorusRel, rename_rename]
    congr 2
    funext w
    rcases w with v | ⟨c, ab⟩ <;> rfl

/-- **Chart rings of a disjoint union.** The chart at `σ` is the tensor product of the charts of
the summands at the restrictions of `σ`. -/
noncomputable def chartSumEquiv (σ : V ⊕ W → Bool) :
    (G.disjointSum H).IncChartRing σ ≃ₐ[ℂ]
      G.IncChartRing (σ ∘ Sum.inl) ⊗[ℂ] H.IncChartRing (σ ∘ Sum.inr) :=
  quotSumEquiv (chartVarSumEquiv V W E F) (Equiv.refl (E ⊕ F))
    (G.incChartEq (σ ∘ Sum.inl)) (H.incChartEq (σ ∘ Sum.inr)) ((G.disjointSum H).incChartEq σ)
    (G.disjointSum_incChartEq_inl H σ) (G.disjointSum_incChartEq_inr H σ)

/-- **Torus rings of a disjoint union.** The common torus of `G ⊔ H` is the tensor product of the
common tori of `G` and `H`. -/
noncomputable def torusSumEquiv :
    (G.disjointSum H).IncTorusRing ≃ₐ[ℂ] G.IncTorusRing ⊗[ℂ] H.IncTorusRing :=
  quotSumEquiv (torusVarSumEquiv V W E F) (torusRelIdxSumEquiv V W E F)
    G.incTorusRel H.incTorusRel (G.disjointSum H).incTorusRel
    (G.disjointSum_incTorusRel_inl H) (G.disjointSum_incTorusRel_inr H)


/-! #### Generators -/

theorem chartSumEquiv_mk_X_inl (σ : V ⊕ W → Bool) (a : IncChartVar V E) :
    G.chartSumEquiv H σ (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inl a)))) =
      Ideal.Quotient.mk _ (X a) ⊗ₜ[ℂ] 1 :=
  quotSumToTensor_mk_X_inl (chartVarSumEquiv V W E F) (Equiv.refl (E ⊕ F))
    (G.incChartEq (σ ∘ Sum.inl)) (H.incChartEq (σ ∘ Sum.inr)) ((G.disjointSum H).incChartEq σ)
    (G.disjointSum_incChartEq_inl H σ) (G.disjointSum_incChartEq_inr H σ) a

theorem chartSumEquiv_mk_X_inr (σ : V ⊕ W → Bool) (b : IncChartVar W F) :
    G.chartSumEquiv H σ (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inr b)))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk _ (X b) :=
  quotSumToTensor_mk_X_inr (chartVarSumEquiv V W E F) (Equiv.refl (E ⊕ F))
    (G.incChartEq (σ ∘ Sum.inl)) (H.incChartEq (σ ∘ Sum.inr)) ((G.disjointSum H).incChartEq σ)
    (G.disjointSum_incChartEq_inl H σ) (G.disjointSum_incChartEq_inr H σ) b

theorem torusSumEquiv_mk_X_inl (a : IncTorusVar V E) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (torusVarSumEquiv V W E F (Sum.inl a)))) =
      Ideal.Quotient.mk _ (X a) ⊗ₜ[ℂ] 1 :=
  quotSumToTensor_mk_X_inl (torusVarSumEquiv V W E F) (torusRelIdxSumEquiv V W E F)
    G.incTorusRel H.incTorusRel (G.disjointSum H).incTorusRel
    (G.disjointSum_incTorusRel_inl H) (G.disjointSum_incTorusRel_inr H) a

theorem torusSumEquiv_mk_X_inr (b : IncTorusVar W F) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (torusVarSumEquiv V W E F (Sum.inr b)))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk _ (X b) :=
  quotSumToTensor_mk_X_inr (torusVarSumEquiv V W E F) (torusRelIdxSumEquiv V W E F)
    G.incTorusRel H.incTorusRel (G.disjointSum H).incTorusRel
    (G.disjointSum_incTorusRel_inl H) (G.disjointSum_incTorusRel_inr H) b

/-- The torus isomorphism sends the coordinate `t_v` of a vertex of `G` to `t_v ⊗ 1`. -/
@[simp] theorem torusSumEquiv_t_inl (v : V) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inl v)))) =
      Ideal.Quotient.mk _ (X (Sum.inl v)) ⊗ₜ[ℂ] 1 :=
  G.torusSumEquiv_mk_X_inl H (Sum.inl v)

/-- The torus isomorphism sends the coordinate `t_w` of a vertex of `H` to `1 ⊗ t_w`. -/
@[simp] theorem torusSumEquiv_t_inr (w : W) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inr w)))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk _ (X (Sum.inl w)) :=
  G.torusSumEquiv_mk_X_inr H (Sum.inl w)

/-- The torus isomorphism sends the inverse coordinate `s_v` of a vertex of `G` to `s_v ⊗ 1`. -/
@[simp] theorem torusSumEquiv_s_inl (v : V) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inl v))))) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))) ⊗ₜ[ℂ] 1 :=
  G.torusSumEquiv_mk_X_inl H (Sum.inr (Sum.inl v))

/-- The torus isomorphism sends the inverse coordinate `s_w` of a vertex of `H` to `1 ⊗ s_w`. -/
@[simp] theorem torusSumEquiv_s_inr (w : W) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl (Sum.inr w))))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl w))) :=
  G.torusSumEquiv_mk_X_inr H (Sum.inr (Sum.inl w))

/-- The torus isomorphism sends a coefficient of an edge of `G` to the same coefficient of `G`. -/
@[simp] theorem torusSumEquiv_coeff_inl (e : E) (ab : Fin 2 × Fin 2) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inl e, ab))))) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (e, ab)))) ⊗ₜ[ℂ] 1 :=
  G.torusSumEquiv_mk_X_inl H (Sum.inr (Sum.inr (e, ab)))

/-- The torus isomorphism sends a coefficient of an edge of `H` to the same coefficient of `H`. -/
@[simp] theorem torusSumEquiv_coeff_inr (f : F) (ab : Fin 2 × Fin 2) :
    G.torusSumEquiv H (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (Sum.inr f, ab))))) =
      1 ⊗ₜ[ℂ] Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (f, ab)))) :=
  G.torusSumEquiv_mk_X_inr H (Sum.inr (Sum.inr (f, ab)))

/-- **Chart restrictions of a disjoint union.** The torus isomorphism intertwines the chart
restriction of `G ⊔ H` at `σ` with the tensor product of the chart restrictions of `G` and `H` at
the restrictions of `σ`. -/
theorem torusSumEquiv_comp_incChartMap (σ : V ⊕ W → Bool) :
    (G.torusSumEquiv H).toAlgHom.comp ((G.disjointSum H).incChartMap σ) =
      (Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl))
        (H.incChartMap (σ ∘ Sum.inr))).comp (G.chartSumEquiv H σ).toAlgHom := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ((v | w) | ⟨e | f, ab⟩)
  · change G.torusSumEquiv H ((G.disjointSum H).incChartMap σ
        (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inl v))))) =
      Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl)) (H.incChartMap (σ ∘ Sum.inr))
        (G.chartSumEquiv H σ
          (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inl (Sum.inl v))))))
    rw [chartSumEquiv_mk_X_inl, Algebra.TensorProduct.map_tmul, map_one, incChartMap_mk, aeval_X,
      incChartMap_mk, aeval_X]
    simp only [incChartVal, Function.comp_apply]
    split_ifs
    · exact G.torusSumEquiv_mk_X_inl H (Sum.inr (Sum.inl v))
    · exact G.torusSumEquiv_mk_X_inl H (Sum.inl v)
  · change G.torusSumEquiv H ((G.disjointSum H).incChartMap σ
        (Ideal.Quotient.mk _ (X (Sum.inl (Sum.inr w))))) =
      Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl)) (H.incChartMap (σ ∘ Sum.inr))
        (G.chartSumEquiv H σ
          (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inr (Sum.inl w))))))
    rw [chartSumEquiv_mk_X_inr, Algebra.TensorProduct.map_tmul, map_one, incChartMap_mk, aeval_X,
      incChartMap_mk, aeval_X]
    simp only [incChartVal, Function.comp_apply]
    split_ifs
    · exact G.torusSumEquiv_mk_X_inr H (Sum.inr (Sum.inl w))
    · exact G.torusSumEquiv_mk_X_inr H (Sum.inl w)
  · change G.torusSumEquiv H ((G.disjointSum H).incChartMap σ
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl e, ab))))) =
      Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl)) (H.incChartMap (σ ∘ Sum.inr))
        (G.chartSumEquiv H σ
          (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inl (Sum.inr (e, ab)))))))
    rw [chartSumEquiv_mk_X_inl, Algebra.TensorProduct.map_tmul, map_one, incChartMap_mk, aeval_X,
      incChartMap_mk, aeval_X]
    exact G.torusSumEquiv_coeff_inl H e ab
  · change G.torusSumEquiv H ((G.disjointSum H).incChartMap σ
        (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr f, ab))))) =
      Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl)) (H.incChartMap (σ ∘ Sum.inr))
        (G.chartSumEquiv H σ
          (Ideal.Quotient.mk _ (X (chartVarSumEquiv V W E F (Sum.inr (Sum.inr (f, ab)))))))
    rw [chartSumEquiv_mk_X_inr, Algebra.TensorProduct.map_tmul, map_one, incChartMap_mk, aeval_X,
      incChartMap_mk, aeval_X]
    exact G.torusSumEquiv_coeff_inr H f ab

theorem torusSumEquiv_incChartMap (σ : V ⊕ W → Bool) (y : (G.disjointSum H).IncChartRing σ) :
    G.torusSumEquiv H ((G.disjointSum H).incChartMap σ y) =
      Algebra.TensorProduct.map (G.incChartMap (σ ∘ Sum.inl)) (H.incChartMap (σ ∘ Sum.inr))
        (G.chartSumEquiv H σ y) :=
  AlgHom.congr_fun (G.torusSumEquiv_comp_incChartMap H σ) y

end Rings

end BPFixedPoints.Multigraph
