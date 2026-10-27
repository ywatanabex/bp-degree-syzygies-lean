import BPFixedPoints.Incidence.VertexPermutationCellChain
import BPFixedPoints.Incidence.VertexPermutationCellTower

/-!
# Transport of cubical-cell cohomology classes along a homeomorphism

For a homeomorphism `h : T ≅ T'` and binary covers `U`, `U'` of `T`, `T'` related by a vertex
bijection `ψ` (`h⁻¹ (U' (ψ v) i) = U v i`), the transport of sheaf cohomology along `h` (Mathlib's
map of Ext along the pushforward equivalence `topSheafEquivOfIso h`, followed by the identification
of the constant sheaves) sends the class of a cubical cocycle `z` of `U`, in the form produced by
`finiteCubicalActualAtEquiv`, to the class of the cocycle of `U'` obtained by pulling back the image
of `z` along `cellChainMap` (`cellTransport_class`). The proof combines the exact-functor naturality
of augmented Yoneda representatives (`VertexPermutationCellTower.lean`), the augmentation
compatibility of the comparison chain map (`VertexPermutationCellChain.lean`) and the sign `+1` of
the constant-sheaf identification (`VertexPermutationCellConstant.lean`). It holds in every
degree, including degree zero, and uses no relative acyclicity.
-/

namespace BPFixedPoints.Multigraph

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open SheafTools SheafTools.BinaryCells ExtResolutionTools

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1600000

noncomputable local instance cellTransportHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

noncomputable local instance cellTransportTopHasExt (S : TopCat.{0}) :
    HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} S) := HasExt.standard _

/-- Local cohomology on the whole space is identified with sheaf cohomology by precomposition. -/
theorem localSheafTopEquiv_apply {S : TopCat.{0}} (F : Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0})
    (n : ℕ) (y : F.H' n ⊤) :
    localSheafTopEquiv F n y = (Ext.mk₀ (freeSheafTopIso (T := S)).inv).comp y (zero_add n) := rfl

variable {T T' : TopCat.{0}} (h : T ≅ T') {V W : Type} [Fintype V] [DecidableEq V] [Fintype W]
  [DecidableEq W] (ψ : V ≃ W) (U : V → Fin 2 → Opens T) (U' : W → Fin 2 → Opens T')
  (hU : ∀ v i, (Opens.map h.hom).obj (U' (ψ v) i) = U v i)

/-- **Transport of the cubical-cell Yoneda classes.** The transport of sheaf cohomology along a
homeomorphism (Mathlib's map of Ext along the pushforward equivalence, followed by the
identification of the constant sheaves) sends the class of a cubical cocycle of `U` to the class
of the cocycle of `U'` obtained by pulling back its image along the comparison chain map. -/
theorem cellTransport_class (hcover : (⊤ : Opens T) ≤ ⨆ b, chartOpen U b)
    (hcover' : (⊤ : Opens T') ≤ ⨆ b, chartOpen U' b)
    (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) (n : ℕ)
    (z : (cubicalTower U).cycles F n) :
    letI := augmentation_epi U hcover
    letI := augmentation_epi U' hcover'
    (Ext.mk₀ ((topSheafEquivOfIsoConstant h).app (AddCommGrpCat.of (ULift ℤ))).inv).comp
        ((localSheafTopEquiv F n (augmentedComplexCocycleComparison (sheafComplex U) F
          (sheafComplex_exact U) (augmentation U) (augmentation_zero U) (augmentation_exact U) n z)
          ).mapExactFunctor (topSheafEquivOfIso h).functor) (zero_add n) =
      localSheafTopEquiv ((topSheafEquivOfIso h).functor.obj F) n
        (augmentedComplexCocycleComparison (sheafComplex U') ((topSheafEquivOfIso h).functor.obj F)
          (sheafComplex_exact U') (augmentation U') (augmentation_zero U') (augmentation_exact U') n
          ((complexMapSourceMap (topSheafEquivOfIso h).functor (sheafComplex_exact U)
            (sheafComplex_exact U') (cellChainMap h ψ U U' hU)).cycles _ n
              (towerMapCycles (topSheafEquivOfIso h).functor n z))) := by
  let _ := augmentation_epi U hcover
  let _ := augmentation_epi U' hcover'
  rw [augmentedComplexCocycleComparison_map (topSheafEquivOfIso h).functor (sheafComplex_exact U)
    (sheafComplex_exact U') (cellChainMap h ψ U U' hU) (augmentation U) (augmentation_zero U)
    (augmentation_exact U) (augmentation U') (augmentation_zero U') (augmentation_exact U')
    (topSheafEquivOfIsoFreeTop h) (cellChainComponent_augmentation h ψ U U' hU) n z,
    localSheafTopEquiv_apply, localSheafTopEquiv_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀_assoc, Ext.mk₀_comp_mk₀_assoc,
    freeSheafTopIso_topSheafEquivOfIso]

end BPFixedPoints.Multigraph
