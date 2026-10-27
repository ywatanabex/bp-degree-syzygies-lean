import BPFixedPoints.Incidence.Ring

/-! # Coefficient-module structures on the common torus and incidence ring -/

namespace BPFixedPoints.Multigraph

set_option synthInstance.maxHeartbeats 100000

variable {V E : Type} [DecidableEq V] [Fintype V] [DecidableEq E] [Fintype E]
  (G : Multigraph V E)

/-- Action of the coefficient ring on the common torus. -/
noncomputable def incTorusCoeffHom : IncCoeffRing E →ₐ[ℂ] G.IncTorusRing :=
  G.IncidenceRing.val.comp G.coeffHom

@[simp] theorem incTorusCoeffHom_apply (r : IncCoeffRing E) :
    G.incTorusCoeffHom r = (G.coeffHom r).val := rfl

@[simp] theorem incTorusCoeffHom_X (c : IncCoeffIdx E) :
    G.incTorusCoeffHom (MvPolynomial.X c) =
      Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel))
        (MvPolynomial.X (Sum.inr (Sum.inr c))) := by
  change (G.coeffHom (MvPolynomial.X c)).val = _
  simp [coeffHom]

/-- The defined incidence ring, regarded as a coefficient-ring submodule on the same set. -/
noncomputable def incidenceSubmodule :
    letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
    Submodule (IncCoeffRing E) G.IncTorusRing := by
  letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
  exact
    { carrier := G.IncidenceRing
      zero_mem' := G.IncidenceRing.zero_mem
      add_mem' := G.IncidenceRing.add_mem
      smul_mem' := fun r x hx =>
        G.IncidenceRing.mul_mem (G.coeffHom r).property hx }

/-- The submodule presentation and public `IncidenceRing` are isomorphic over the coefficient ring. -/
noncomputable def incidenceSubmoduleEquiv :
    letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
    letI : Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra
    G.incidenceSubmodule ≃ₗ[IncCoeffRing E] G.IncidenceRing := by
  letI : Algebra (IncCoeffRing E) G.IncTorusRing := G.incTorusCoeffHom.toRingHom.toAlgebra
  letI : Algebra (IncCoeffRing E) G.IncidenceRing := G.coeffHom.toRingHom.toAlgebra
  exact
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

end BPFixedPoints.Multigraph
