import BPFixedPoints.Incidence.IncidenceDisjointUnion
import BPFixedPoints.Incidence.IncidenceDisjointUnionIso

/-!
# Symmetry, associativity and unit of the tensor formula for disjoint unions

The isomorphism `incidenceSumEquiv : 𝒰_{G⊔H} ≃ 𝒰_G ⊗ 𝒰_H` is compatible with the graph
isomorphisms of disjoint unions (`OrientedIso.sumComm`, `sumAssoc`, `sumEmpty`) and the
corresponding isomorphisms of tensor products:
* symmetry: `incidenceSumEquiv_sumComm`, with `Algebra.TensorProduct.comm`;
* associativity: `incidenceSumEquiv_sumAssoc`, with `Algebra.TensorProduct.assoc`;
* unit: `incidenceSumEmptyEquiv_eq_sumEmpty`, which identifies `𝒰_{G⊔∅} ≃ 𝒰_G ⊗ ℂ ≃ 𝒰_G` with
  the isomorphism induced by the graph isomorphism `G ⊔ ∅ ≅ G`.

Each statement is reduced to the corresponding identity of torus rings, which is checked on
generators. Nothing about gradings is proved here.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial
open scoped TensorProduct

/-- The associator of algebra tensor products is natural. -/
theorem tensorAssoc_map_map {A B C A' B' C' : Type*} [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [CommRing B'] [CommRing C'] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]
    [Algebra ℂ A'] [Algebra ℂ B'] [Algebra ℂ C']
    (f : A →ₐ[ℂ] A') (g : B →ₐ[ℂ] B') (h : C →ₐ[ℂ] C') (z : (A ⊗[ℂ] B) ⊗[ℂ] C) :
    Algebra.TensorProduct.assoc ℂ ℂ ℂ A' B' C'
        (Algebra.TensorProduct.map (Algebra.TensorProduct.map f g) h z) =
      Algebra.TensorProduct.map f (Algebra.TensorProduct.map g h)
        (Algebra.TensorProduct.assoc ℂ ℂ ℂ A B C z) := by
  induction z using TensorProduct.inductionOn with
  | tmul x c =>
    induction x using TensorProduct.inductionOn with
    | tmul a b => rfl
    | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {V W U E F D : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  [DecidableEq W] [Fintype W] [DecidableEq F] [Fintype F]
  [DecidableEq U] [Fintype U] [DecidableEq D] [Fintype D]
  (G : Multigraph V E) (H : Multigraph W F) (K : Multigraph U D)

/-! ### Symmetry -/

/-- Torus form of the symmetry compatibility. -/
theorem torusSumEquiv_sumComm (t : (G.disjointSum H).IncTorusRing) :
    H.torusSumEquiv G ((OrientedIso.sumComm G H).torusEquiv t) =
      Algebra.TensorProduct.comm ℂ _ _ (G.torusSumEquiv H t) := by
  have h : (H.torusSumEquiv G).toAlgHom.comp (OrientedIso.sumComm G H).torusEquiv.toAlgHom =
      (Algebra.TensorProduct.comm ℂ G.IncTorusRing H.IncTorusRing).toAlgHom.comp
        (G.torusSumEquiv H).toAlgHom := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro ((v | w) | (v | w) | ⟨e | f, ab⟩) <;>
      simp [OrientedIso.torusVarEquiv, OrientedIso.sumComm]
  exact AlgHom.congr_fun h t

/-- **Symmetry compatibility.** Under `G ⊔ H ≅ H ⊔ G`, the tensor formula for `H ⊔ G` is the
tensor formula for `G ⊔ H` followed by the exchange of tensor factors. -/
theorem incidenceSumEquiv_sumComm (x : (G.disjointSum H).IncidenceRing) :
    H.incidenceSumEquiv G ((OrientedIso.sumComm G H).incidenceEquiv x) =
      Algebra.TensorProduct.comm ℂ _ _ (G.incidenceSumEquiv H x) := by
  apply incidenceTensorIncl_injective H G
  rw [incidenceTensorIncl_incidenceSumEquiv, OrientedIso.incidenceEquiv_val, torusSumEquiv_sumComm,
    ← incidenceTensorIncl_incidenceSumEquiv, incidenceTensorIncl, incidenceTensorIncl,
    Algebra.TensorProduct.comm_comp_map_apply]

/-! ### Associativity -/

/-- The inclusion `𝒰_G ⊗ (𝒰_H ⊗ 𝒰_K) → T_G ⊗ (T_H ⊗ T_K)`. (The type is left to be inferred:
synthesizing the ring structure of a triple tensor product of torus rings from scratch fails.) -/
noncomputable def incidenceTensorIncl₃ :=
  Algebra.TensorProduct.map G.IncidenceRing.val (incidenceTensorIncl H K)

theorem incidenceTensorIncl₃_injective : Function.Injective (incidenceTensorIncl₃ G H K) := by
  have : Module.Flat ℂ G.IncTorusRing := Module.Flat.of_free
  have : Module.Free ℂ (H.IncidenceRing ⊗[ℂ] K.IncidenceRing) := Module.Free.of_divisionRing ℂ _
  have : Module.Flat ℂ (H.IncidenceRing ⊗[ℂ] K.IncidenceRing) := Module.Flat.of_free
  exact TensorProduct.map_injective_of_flat_flat G.IncidenceRing.val.toLinearMap
    (incidenceTensorIncl H K).toLinearMap Subtype.val_injective (incidenceTensorIncl_injective H K)

/-- `incidenceTensorIncl ∘ incidenceSumEquiv` is the torus isomorphism on the underlying element,
as algebra maps. -/
theorem incidenceTensorIncl_comp_incidenceSumEquiv :
    (incidenceTensorIncl G H).comp (G.incidenceSumEquiv H).toAlgHom =
      (G.torusSumEquiv H).toAlgHom.comp (G.disjointSum H).IncidenceRing.val :=
  AlgHom.ext fun x => G.incidenceTensorIncl_incidenceSumEquiv H x

/-- Torus form of the associativity compatibility. -/
theorem torusSumEquiv_sumAssoc (t : ((G.disjointSum H).disjointSum K).IncTorusRing) :
    Algebra.TensorProduct.map (AlgHom.id ℂ G.IncTorusRing) (H.torusSumEquiv K).toAlgHom
        (G.torusSumEquiv (H.disjointSum K) ((OrientedIso.sumAssoc G H K).torusEquiv t)) =
      Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _
        (Algebra.TensorProduct.map (G.torusSumEquiv H).toAlgHom (AlgHom.id ℂ K.IncTorusRing)
          ((G.disjointSum H).torusSumEquiv K t)) := by
  have h : ((Algebra.TensorProduct.map (AlgHom.id ℂ G.IncTorusRing)
        (H.torusSumEquiv K).toAlgHom).comp (G.torusSumEquiv (H.disjointSum K)).toAlgHom).comp
          (OrientedIso.sumAssoc G H K).torusEquiv.toAlgHom =
      ((Algebra.TensorProduct.assoc ℂ ℂ ℂ G.IncTorusRing H.IncTorusRing
          K.IncTorusRing).toAlgHom.comp
        (Algebra.TensorProduct.map (G.torusSumEquiv H).toAlgHom
          (AlgHom.id ℂ K.IncTorusRing))).comp ((G.disjointSum H).torusSumEquiv K).toAlgHom := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro (((v | w) | u) | ((v | w) | u) | ⟨(e | f) | d, ab⟩) <;>
      simp [OrientedIso.torusVarEquiv, OrientedIso.sumAssoc, Algebra.TensorProduct.one_def]
  exact AlgHom.congr_fun h t

theorem incidenceTensorIncl₃_tmul (a : G.IncidenceRing)
    (y : H.IncidenceRing ⊗[ℂ] K.IncidenceRing) :
    incidenceTensorIncl₃ G H K (a ⊗ₜ[ℂ] y) = a.val ⊗ₜ[ℂ] incidenceTensorIncl H K y := rfl

set_option synthInstance.maxHeartbeats 200000 in
/-- The triple inclusion commutes with the associators. -/
theorem incidenceTensorIncl₃_assoc (y : G.IncidenceRing ⊗[ℂ] H.IncidenceRing)
    (c : K.IncidenceRing) :
    incidenceTensorIncl₃ G H K (Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _ (y ⊗ₜ[ℂ] c)) =
      Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _ (incidenceTensorIncl G H y ⊗ₜ[ℂ] c.val) := by
  induction y using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

set_option synthInstance.maxHeartbeats 200000 in
/-- The triple inclusion after `id ⊗ incidenceSumEquiv`. -/
theorem incidenceTensorIncl₃_map_incidenceSumEquiv
    (z : G.IncidenceRing ⊗[ℂ] (H.disjointSum K).IncidenceRing) :
    incidenceTensorIncl₃ G H K
        (Algebra.TensorProduct.map (AlgHom.id ℂ _) (H.incidenceSumEquiv K).toAlgHom z) =
      Algebra.TensorProduct.map (AlgHom.id ℂ G.IncTorusRing) (H.torusSumEquiv K).toAlgHom
        (incidenceTensorIncl G (H.disjointSum K) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, incidenceTensorIncl₃_tmul, incidenceTensorIncl_tmul,
      Algebra.TensorProduct.map_tmul]
    exact congrArg (a.val ⊗ₜ[ℂ] ·) (H.incidenceTensorIncl_incidenceSumEquiv K b)
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

/-- The triple inclusion after `assoc ∘ (incidenceSumEquiv ⊗ id)`. -/
theorem incidenceTensorIncl₃_assoc_map_incidenceSumEquiv
    (z : (G.disjointSum H).IncidenceRing ⊗[ℂ] K.IncidenceRing) :
    incidenceTensorIncl₃ G H K (Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _
        (Algebra.TensorProduct.map (G.incidenceSumEquiv H).toAlgHom (AlgHom.id ℂ _) z)) =
      Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _
        (Algebra.TensorProduct.map (G.torusSumEquiv H).toAlgHom (AlgHom.id ℂ K.IncTorusRing)
          (incidenceTensorIncl (G.disjointSum H) K z)) := by
  have h : ((incidenceTensorIncl₃ G H K).comp
        (Algebra.TensorProduct.assoc ℂ ℂ ℂ G.IncidenceRing H.IncidenceRing
          K.IncidenceRing).toAlgHom).comp
          (Algebra.TensorProduct.map (G.incidenceSumEquiv H).toAlgHom
            (AlgHom.id ℂ K.IncidenceRing)) =
      ((Algebra.TensorProduct.assoc ℂ ℂ ℂ G.IncTorusRing H.IncTorusRing
          K.IncTorusRing).toAlgHom.comp
        (Algebra.TensorProduct.map (G.torusSumEquiv H).toAlgHom
          (AlgHom.id ℂ K.IncTorusRing))).comp (incidenceTensorIncl (G.disjointSum H) K) := by
    apply Algebra.TensorProduct.ext'
    intro w c
    change incidenceTensorIncl₃ G H K (Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _
        (G.incidenceSumEquiv H w ⊗ₜ[ℂ] c)) =
      Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _ (G.torusSumEquiv H w.val ⊗ₜ[ℂ] c.val)
    rw [incidenceTensorIncl₃_assoc, incidenceTensorIncl_incidenceSumEquiv]
  exact AlgHom.congr_fun h z

/-- **Associativity compatibility.** Under `(G ⊔ H) ⊔ K ≅ G ⊔ (H ⊔ K)`, the two iterated tensor
formulas differ by the associator of tensor products. -/
theorem incidenceSumEquiv_sumAssoc (x : ((G.disjointSum H).disjointSum K).IncidenceRing) :
    Algebra.TensorProduct.map (AlgHom.id ℂ G.IncidenceRing) (H.incidenceSumEquiv K).toAlgHom
        (G.incidenceSumEquiv (H.disjointSum K) ((OrientedIso.sumAssoc G H K).incidenceEquiv x)) =
      Algebra.TensorProduct.assoc ℂ ℂ ℂ _ _ _
        (Algebra.TensorProduct.map (G.incidenceSumEquiv H).toAlgHom (AlgHom.id ℂ K.IncidenceRing)
          ((G.disjointSum H).incidenceSumEquiv K x)) := by
  refine incidenceTensorIncl₃_injective G H K ?_
  rw [incidenceTensorIncl₃_map_incidenceSumEquiv, incidenceTensorIncl₃_assoc_map_incidenceSumEquiv,
    incidenceTensorIncl_incidenceSumEquiv, incidenceTensorIncl_incidenceSumEquiv,
    OrientedIso.incidenceEquiv_val, torusSumEquiv_sumAssoc]

/-! ### Unit -/

section Unit

variable {V₀ E₀ : Type} [DecidableEq V₀] [Fintype V₀] [DecidableEq E₀] [Fintype E₀]
  [IsEmpty V₀] [IsEmpty E₀] (G₀ : Multigraph V₀ E₀)

/-- The graph isomorphism `G ⊔ ∅ ≅ G` inverts the pullback along the summand inclusion. -/
theorem sumEmpty_torusEquiv_torusInl (t : G.IncTorusRing) :
    (OrientedIso.sumEmpty G G₀).torusEquiv (G.torusInl G₀ t) = t := by
  have h : (OrientedIso.sumEmpty G G₀).torusEquiv.toAlgHom.comp (G.torusInl G₀) =
      AlgHom.id ℂ G.IncTorusRing := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    rintro (v | v | ⟨e, ab⟩) <;>
      simp [torusInl_mk, torusVarSumEquiv, OrientedIso.torusVarEquiv, OrientedIso.sumEmpty]
  exact AlgHom.congr_fun h t

/-- **Unit compatibility.** The isomorphism `𝒰_{G⊔∅} ≃ 𝒰_G ⊗ ℂ ≃ 𝒰_G` coming from the tensor
formula is the isomorphism induced by the graph isomorphism `G ⊔ ∅ ≅ G`. -/
theorem incidenceSumEmptyEquiv_eq_sumEmpty (x : (G.disjointSum G₀).IncidenceRing) :
    G.incidenceSumEmptyEquiv G₀ x = (OrientedIso.sumEmpty G G₀).incidenceEquiv x := by
  apply (G.incidenceSumEmptyEquiv G₀).symm.injective
  rw [AlgEquiv.symm_apply_apply]
  apply Subtype.ext
  rw [incidenceSumEmptyEquiv_symm_val]
  apply (OrientedIso.sumEmpty G G₀).torusEquiv.injective
  rw [sumEmpty_torusEquiv_torusInl, OrientedIso.incidenceEquiv_val]

/-- **Sanity check.** `𝒰_{G⊔∅} ≃ 𝒰_G` intertwines the coefficient maps, through the renaming of
coefficients induced by `G ⊔ ∅ ≅ G`. -/
theorem incidenceSumEmptyEquiv_coeffHom (r : IncCoeffRing (E ⊕ E₀)) :
    G.incidenceSumEmptyEquiv G₀ ((G.disjointSum G₀).coeffHom r) =
      G.coeffHom ((OrientedIso.sumEmpty G G₀).coeffEquiv r) := by
  rw [incidenceSumEmptyEquiv_eq_sumEmpty, OrientedIso.incidenceEquiv_coeffHom]

end Unit

end BPFixedPoints.Multigraph
