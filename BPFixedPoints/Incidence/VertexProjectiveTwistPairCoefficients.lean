import BPFixedPoints.Incidence.VertexProjectiveTwistPairChartComparison
import BPFixedPoints.Incidence.SheafTwoOpenCechComparison
import BPFixedPoints.Incidence.VertexProjectiveTwistCechAcyclic

/-! # Original chart and pair coefficients on actual overlap sections

The section maps are induced by the specified original frames. The native
restriction difference keeps its left-minus-right sign and original transition.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory Opposite

/-- The native abelian section difference retains the original module presheaf restrictions and subtraction. -/
theorem moduleTwoOpenSectionDifference_apply (X : Scheme.{0}) (M : X.Modules)
    (U V : X.Opens) (x : Γ(M, U)) (y : Γ(M, V)) :
    twoOpenSectionDifference ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) U V (x,y) =
      M.presheaf.map (homOfLE inf_le_left).op x - M.presheaf.map (homOfLE inf_le_right).op y := rfl

end BPFixedPoints.SheafTools

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 800000
variable (R : Type) [CommRing R] (V : Type) [Fintype V]

/-- The originally specified pair frame gives coefficients on every actual subopen. -/
noncomputable def vertexTwistSheafPairCoefficient (a : V → ℤ) (σ τ : V → Fin 2)
    (right : Bool) (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ) :
    Γ(vertexTwistSheaf R V a, W) →ₗ[Γ(vertexScheme R V, W)] Γ(vertexScheme R V, W) :=
  ((SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
    (vertexChartPairOpen R V σ τ) (vertexTwistSheafPairIso R V a σ τ right)).hom.val.app
      (op (Over.mk (homOfLE hW)))).hom

/-- The original left chart coefficients on a pair subopen are its specified original left pair coefficients. -/
theorem vertexTwistSheafChartCoefficient_left_pair (a : V → ℤ) (σ τ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafPairCoefficient R V a σ τ false W hW x =
      vertexTwistSheafChartCoefficient R V a σ W (hW.trans inf_le_left) x := by
  have h := SheafTools.moduleLocalFrameRestriction_coefficients (vertexScheme R V)
    (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left))
    (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a σ)
    (Over.mk (homOfLE hW)) x
  change (show Γ(vertexScheme R V, W) from
    ((SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
      (vertexChartPairOpen R V σ τ) (vertexTwistSheafChartFrameRestriction R V a σ
        (vertexChartPairOpen R V σ τ) inf_le_left)).hom.val.app
          (op (Over.mk (homOfLE hW)))).hom x) =
    vertexTwistSheafChartCoefficient R V a σ W (hW.trans inf_le_left) x at h
  rw [vertexTwistSheafChartFrameRestriction_left_pair] at h
  exact h

/-- The original right chart coefficients on a pair subopen are its specified original right pair coefficients. -/
theorem vertexTwistSheafChartCoefficient_right_pair (a : V → ℤ) (σ τ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafPairCoefficient R V a σ τ true W hW x =
      vertexTwistSheafChartCoefficient R V a τ W (hW.trans inf_le_right) x := by
  have h := SheafTools.moduleLocalFrameRestriction_coefficients (vertexScheme R V)
    (homOfLE (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right))
    (vertexTwistSheaf R V a) (vertexTwistSheafChartIso R V a τ)
    (Over.mk (homOfLE hW)) x
  change (show Γ(vertexScheme R V, W) from
    ((SheafTools.moduleOverUnitIso (vertexScheme R V) (vertexTwistSheaf R V a)
      (vertexChartPairOpen R V σ τ) (vertexTwistSheafChartFrameRestriction R V a τ
        (vertexChartPairOpen R V σ τ) inf_le_right)).hom.val.app
          (op (Over.mk (homOfLE hW)))).hom x) =
    vertexTwistSheafChartCoefficient R V a τ W (hW.trans inf_le_right) x at h
  rw [vertexTwistSheafChartFrameRestriction_right_pair] at h
  exact h

/-- The original transition function acts through its native coefficient on every actual pair subopen. -/
noncomputable def vertexTwistSheafPairTransitionCoefficient (a : V → ℤ) (σ τ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ) :
    Γ(vertexScheme R V, W) :=
  SheafTools.moduleOverMultiplicationCoefficient (vertexScheme R V) (vertexChartPairOpen R V σ τ)
    (vertexTwistSheafPairUnit R V a σ τ : Γ((vertexChartPairOpen R V σ τ).toScheme, ⊤))
    (Over.mk (homOfLE hW))

/-- The original chart coefficients have the original transition on every pair subopen. -/
theorem vertexTwistSheafChartCoefficient_pair_transition (a : V → ℤ) (σ τ : V → Fin 2)
    (W : (vertexScheme R V).Opens) (hW : W ≤ vertexChartPairOpen R V σ τ)
    (x : Γ(vertexTwistSheaf R V a, W)) :
    vertexTwistSheafChartCoefficient R V a σ W (hW.trans inf_le_left) x =
      vertexTwistSheafChartCoefficient R V a τ W (hW.trans inf_le_right) x *
        vertexTwistSheafPairTransitionCoefficient R V a σ τ W hW := by
  rw [← vertexTwistSheafChartCoefficient_left_pair, ← vertexTwistSheafChartCoefficient_right_pair]
  exact SheafTools.moduleOverUnitIso_transition_coefficients (vertexScheme R V)
    (vertexChartPairOpen R V σ τ) (vertexTwistSheaf R V a)
    (vertexTwistSheafPairIso R V a σ τ false) (vertexTwistSheafPairIso R V a σ τ true)
    _ (vertexTwistSheafPairIso_transition R V a σ τ) (Over.mk (homOfLE hW)) x

/-- The native section restriction difference has its original left-minus-right transition formula. -/
theorem vertexTwistSheafChartCoefficient_section_difference (a : V → ℤ) (σ τ : V → Fin 2)
    (x : Γ(vertexTwistSheaf R V a, vertexChartOpen R V σ))
    (y : Γ(vertexTwistSheaf R V a, vertexChartOpen R V τ)) :
    vertexTwistSheafChartCoefficient R V a σ (vertexChartPairOpen R V σ τ) inf_le_left
      (SheafTools.twoOpenSectionDifference
        ((SheafOfModules.toSheaf (vertexScheme R V).ringCatSheaf).obj (vertexTwistSheaf R V a))
        (vertexChartOpen R V σ) (vertexChartOpen R V τ) (x,y)) =
    (vertexScheme R V).presheaf.map (homOfLE inf_le_left).op
      (vertexTwistSheafChartCoefficient R V a σ (vertexChartOpen R V σ) le_rfl x) -
    (vertexScheme R V).presheaf.map (homOfLE inf_le_right).op
      (vertexTwistSheafChartCoefficient R V a τ (vertexChartOpen R V τ) le_rfl y) *
        vertexTwistSheafPairTransitionCoefficient R V a σ τ (vertexChartPairOpen R V σ τ) le_rfl := by
  rw [SheafTools.moduleTwoOpenSectionDifference_apply,
    (vertexTwistSheafChartCoefficient R V a σ (vertexChartPairOpen R V σ τ) inf_le_left).map_sub]
  have hx := vertexTwistSheafChartCoefficient_restrict R V a σ
    (W := vertexChartPairOpen R V σ τ) (U := vertexChartOpen R V σ)
    (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V σ from inf_le_left) le_rfl x
  have hy := vertexTwistSheafChartCoefficient_restrict R V a τ
    (W := vertexChartPairOpen R V σ τ) (U := vertexChartOpen R V τ)
    (show vertexChartPairOpen R V σ τ ≤ vertexChartOpen R V τ from inf_le_right) le_rfl y
  have ht := vertexTwistSheafChartCoefficient_pair_transition R V a σ τ
    (vertexChartPairOpen R V σ τ) le_rfl
    ((vertexTwistSheaf R V a).presheaf.map (homOfLE inf_le_right).op y)
  exact congrArg₂ (fun u v : Γ(vertexScheme R V, vertexChartPairOpen R V σ τ) => u-v)
    hx (ht.trans (congrArg (fun z => z *
      vertexTwistSheafPairTransitionCoefficient R V a σ τ (vertexChartPairOpen R V σ τ) le_rfl) hy))

noncomputable local instance vertexPairCoefficientHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme R V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The native degree-zero Ext restriction difference has the same original chart coefficient formula. -/
theorem vertexTwistSheafChartCoefficient_ext_zero_difference (a : V → ℤ) (σ τ : V → Fin 2)
    (x : (vertexTwistAbelianSheaf R V a).H' 0 (vertexChartOpen R V σ))
    (y : (vertexTwistAbelianSheaf R V a).H' 0 (vertexChartOpen R V τ)) :
    vertexTwistSheafChartCoefficient R V a σ (vertexChartPairOpen R V σ τ) inf_le_left
      (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R V a) (vertexChartPairOpen R V σ τ)
        ((Opens.mayerVietorisSquare (vertexChartOpen R V σ) (vertexChartOpen R V τ)).fromBiprod
          (vertexTwistAbelianSheaf R V a) 0 ((AddCommGrpCat.biprodIsoProd _ _).inv (x,y)))) =
    (vertexScheme R V).presheaf.map (homOfLE inf_le_left).op
      (vertexTwistSheafChartCoefficient R V a σ (vertexChartOpen R V σ) le_rfl
        (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R V a) (vertexChartOpen R V σ) x)) -
    (vertexScheme R V).presheaf.map (homOfLE inf_le_right).op
      (vertexTwistSheafChartCoefficient R V a τ (vertexChartOpen R V τ) le_rfl
        (SheafTools.localSheafH0Equiv (vertexTwistAbelianSheaf R V a) (vertexChartOpen R V τ) y)) *
      vertexTwistSheafPairTransitionCoefficient R V a σ τ (vertexChartPairOpen R V σ τ) le_rfl := by
  have h := SheafTools.localSheafH0_fromBiprod (vertexTwistAbelianSheaf R V a)
    (vertexChartOpen R V σ) (vertexChartOpen R V τ) x y
  have hc := congrArg (fun z : Γ(vertexTwistSheaf R V a, vertexChartPairOpen R V σ τ) =>
    vertexTwistSheafChartCoefficient R V a σ (vertexChartPairOpen R V σ τ) inf_le_left z) h
  exact hc.trans (vertexTwistSheafChartCoefficient_section_difference R V a σ τ _ _)

end BPFixedPoints.ProjectiveLine
