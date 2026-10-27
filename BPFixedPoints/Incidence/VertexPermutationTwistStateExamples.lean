import BPFixedPoints.Incidence.VertexPermutationTwistStateFormula

/-!
# Checks of the state formula for vertex bijections

Three consequences of `vertexTwistStateFormula`, stated for the geometric map `vertexTwistHPerm`
of multi-twist cohomology (defined from the scheme isomorphism, not from states):
* **degree zero**: the unit class of `H⁰(O)` (the class of the constant global section `1`,
  `vertexNegativeUnit_globalZeroChain`) goes to the unit class (`vertexTwistHPerm_unit`);
* **a sign**: for `O(-2,-2)` on two vertices, the swap of the vertices sends the class of
  `H²` whose state is the unique state basis vector (the specified Laurent generator) to its
  negative (`vertexTwistHPerm_swap`); such a class exists (`vertexTwistSwapGenerator_exists`);
* **composition**: the geometric map of a composite bijection is the composite of the geometric
  maps (`vertexTwistHPerm_trans`), using the composition law of the signed relabeling
  (`hVertexPerm_trans`).
-/

namespace BPFixedPoints.Multigraph

open AlgebraicGeometry CategoryTheory TopologicalSpace ProjectiveLine CechProduct Finsupp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1800000

noncomputable local instance stateExamplesHasExt (S : TopCat.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) := HasExt.standard _

/-- The signed relabeling of states is compatible with composition of bijections. -/
theorem hVertexPerm_trans (R : Type) [CommRing R] {V W X : Type} [Fintype V] [Fintype W]
    [Fintype X] (ψ : V ≃ W) (χ : W ≃ X) (d : V → ℕ) (y : H R d) :
    hVertexPerm R (ψ.trans χ) d y = hVertexPerm R χ (fun w => d (ψ.symm w)) (hVertexPerm R ψ d y) := by
  induction y using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero, map_zero]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  | single κ r =>
    rw [hVertexPerm_single, hVertexPerm_single, hVertexPerm_single, vertexPermSign_trans,
      twistSupport_comp, mul_assoc]
    rfl

variable (R : Type) [CommRing R] [IsNoetherianRing R] {V W : Type} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] (ψ : V ≃ W)

/-- **Degree zero.** The geometric map sends the unit class of `H⁰(O)` on `(P¹)^V` (the class of the
constant global section `1`) to the unit class on `(P¹)^W`. -/
theorem vertexTwistHPerm_unit :
    vertexTwistHPerm R ψ (fun v => -((0 : V → ℕ) v : ℤ)) (fun w => -((0 : W → ℕ) w : ℤ))
      (fun v => by simp) 0 (vertexNegativeUnit R V) = vertexNegativeUnit R W := by
  apply vertexTwistActualStateAt_injective R W 0 0
  apply Subtype.ext
  have h1 := vertexTwistActualStateAt_vertexTwistHPerm R ψ 0 0 (vertexNegativeUnit R V)
  rw [vertexNegativeUnit_state, hVertexPerm_cohomologyUnit] at h1
  rw [vertexNegativeUnit_state]
  exact h1

/-- **Composition.** The geometric map of a composite bijection is the composite of the geometric
maps. -/
theorem vertexTwistHPerm_trans {X : Type} [Fintype X] [DecidableEq X] (χ : W ≃ X) (d : V → ℕ)
    (n : ℕ) (x : Sheaf.H.{1} (vertexTwistAbelianSheaf R V (fun v => -(d v : ℤ))) n) :
    vertexTwistHPerm R (ψ.trans χ) (fun v => -(d v : ℤ)) (fun u => -(d ((ψ.trans χ).symm u) : ℤ))
        (fun v => by simp) n x =
      vertexTwistHPerm R χ (fun w => -(d (ψ.symm w) : ℤ)) (fun u => -(d (ψ.symm (χ.symm u)) : ℤ))
        (fun w => by simp) n
        (vertexTwistHPerm R ψ (fun v => -(d v : ℤ)) (fun w => -(d (ψ.symm w) : ℤ))
          (fun v => by simp) n x) := by
  apply vertexTwistActualStateAt_injective R X (fun u => d (ψ.symm (χ.symm u))) n
  apply Subtype.ext
  have h1 := vertexTwistActualStateAt_vertexTwistHPerm R (ψ.trans χ) d n x
  have h2 := vertexTwistActualStateAt_vertexTwistHPerm R χ (fun w => d (ψ.symm w)) n
    (vertexTwistHPerm R ψ (fun v => -(d v : ℤ)) (fun w => -(d (ψ.symm w) : ℤ))
      (fun v => by simp) n x)
  have h3 := vertexTwistActualStateAt_vertexTwistHPerm R ψ d n x
  rw [h3] at h2
  exact h1.trans ((hVertexPerm_trans R ψ χ d _).trans h2.symm)

/-- **A sign check.** For `O(-2,-2)` on two vertices, the swap of the vertices sends the class of
`H²` whose state is the Laurent generator to its negative. -/
theorem vertexTwistHPerm_swap
    (g : Sheaf.H.{1} (vertexTwistAbelianSheaf R (Fin 2) (fun v => -((fun _ => 2 : Fin 2 → ℕ) v : ℤ))) 2)
    (hg : (vertexTwistActualStateAt R (Fin 2) (fun _ => 2) 2 g : H R (fun _ : Fin 2 => 2)) =
      Finsupp.single (fun _ => ⟨0, by simp [phi]⟩ : HBasis (fun _ : Fin 2 => 2)) 1) :
    vertexTwistHPerm R (Equiv.swap (0 : Fin 2) 1) (fun v => -((fun _ => 2 : Fin 2 → ℕ) v : ℤ))
      (fun w => -((fun _ => 2 : Fin 2 → ℕ) ((Equiv.swap (0 : Fin 2) 1).symm w) : ℤ))
      (fun _ => by simp) 2 g = -g := by
  apply vertexTwistActualStateAt_injective R (Fin 2) (fun _ => 2) 2
  apply Subtype.ext
  have h1 := vertexTwistActualStateAt_vertexTwistHPerm R (Equiv.swap (0 : Fin 2) 1) (fun _ => 2) 2 g
  refine h1.trans ?_
  rw [map_neg, Submodule.coe_neg, hg]
  erw [hVertexPerm_single]
  have hs : twistSupport (fun _ : Fin 2 => (2 : ℕ)) = {0, 1} := by
    ext v
    fin_cases v <;> simp [twistSupport]
  rw [hs, vertexPermSign_swap R (by decide : (0 : Fin 2) ≠ 1), mul_one, Finsupp.single_neg]

/-- The class used in `vertexTwistHPerm_swap` exists: some class of `H²(O(-2,-2))` has the Laurent
generator as its state. -/
theorem vertexTwistSwapGenerator_exists :
    ∃ g : Sheaf.H.{1} (vertexTwistAbelianSheaf R (Fin 2)
        (fun v => -((fun _ => 2 : Fin 2 → ℕ) v : ℤ))) 2,
      (vertexTwistActualStateAt R (Fin 2) (fun _ => 2) 2 g : H R (fun _ : Fin 2 => 2)) =
        Finsupp.single (fun _ => ⟨0, by simp [phi]⟩ : HBasis (fun _ : Fin 2 => 2)) 1 := by
  have hmem : Finsupp.single (fun _ => ⟨0, by simp [phi]⟩ : HBasis (fun _ : Fin 2 => 2)) (1 : R) ∈
      stateDegreePiece R (fun _ : Fin 2 => 2) 2 := by
    apply Finsupp.single_mem_supported
    change (cohomologyDegree (fun _ : Fin 2 => 2) : ℤ) = 2
    rw [cohomologyDegree_eq_card_twistSupport]
    have hs : twistSupport (fun _ : Fin 2 => (2 : ℕ)) = Finset.univ := by
      ext v
      simp [twistSupport]
    rw [hs]
    rfl
  let _ := vertexTwistStateCohomologyModule R (Fin 2) (fun _ => 2) 2
  obtain ⟨g, hg⟩ := (vertexTwistStateLinearEquiv R (Fin 2) (fun _ => 2) 2).surjective ⟨_, hmem⟩
  refine ⟨g, ?_⟩
  rw [← vertexTwistStateLinearEquiv_eq_actualStateAt, hg]

end BPFixedPoints.Multigraph
