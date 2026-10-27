import BPFixedPoints.Incidence.CechRestriction
import BPFixedPoints.Incidence.KoszulFaceTorus

/-! # Adjacent restrictions commute with common-torus evaluation -/

namespace BPFixedPoints.CechProduct

variable {V : Type*} [DecidableEq V]

@[simp] theorem exponentToInt_cast {q q' : Fin 3} (h : q = q') (m : FaceExponent q) :
    exponentToInt q' (AddEquiv.cast (M := FaceExponent) h m) = exponentToInt q m := by
  cases h
  rfl

@[simp] theorem faceToInt_chartMonoid (σ : V → Bool) (k : V → ℕ) (w : V) :
    faceToInt (chartFace σ) (chartMonoidEquiv σ k) w = (k w : ℤ) := by
  change exponentToInt (if σ w then 1 else 0) (chartNatEquiv (σ w) (k w)) = _
  cases σ w <;> rfl

theorem faceToInt_overlapExponent (σ : V → Bool) (v : V) (b : Bool)
    (k : V → ℕ) (w : V) :
    faceToInt (overlapFace σ v) (overlapExponent σ v b k) w =
      if w = v then (if b then -(k w : ℤ) else (k w : ℤ)) else (k w : ℤ) := by
  change exponentToInt (overlapFace σ v w) (overlapCoordinate σ v b w (k w)) = _
  by_cases hw : w = v
  · subst w
    simp only [overlapCoordinate, dite_true, AddMonoidHom.comp_apply,
      AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, exponentToInt_cast,
      ite_true]
    cases b <;> rfl
  · simp only [overlapCoordinate, dite_eq_right hw, ite_eq_right hw]
    change exponentToInt (overlapFace σ v w)
      (AddEquiv.cast (M := FaceExponent) (overlapFace_ne σ v w hw).symm
        (chartMonoidEquiv σ k w)) = _
    exact (exponentToInt_cast (overlapFace_ne σ v w hw).symm _).trans
      (faceToInt_chartMonoid σ k w)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open CechProduct IncidenceLaurent

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incFaceVertexUnit_chartFace (σ : V → Bool) (v : V) :
    G.incFaceVertexUnit (chartFace σ) v = G.incChartVertexUnit σ v := by
  apply Units.ext
  cases h : σ v <;>
    simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, chartFace, h]

theorem incFaceVertexUnit_overlap_other (σ : V → Bool) (v w : V) (hw : w ≠ v) :
    G.incFaceVertexUnit (overlapFace σ v) w = G.incChartVertexUnit σ w := by
  apply Units.ext
  cases h : σ w <;>
    simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, chartFace,
      overlapFace, hw, h]

theorem incFaceVertexUnit_overlap_false (σ : V → Bool) (v : V) :
    G.incFaceVertexUnit (chartFace (Function.update σ v false)) v =
      G.incFaceVertexUnit (overlapFace σ v) v := by
  apply Units.ext
  simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, chartFace, overlapFace]

theorem incFaceVertexUnit_overlap_true (σ : V → Bool) (v : V) :
    G.incFaceVertexUnit (chartFace (Function.update σ v true)) v =
      (G.incFaceVertexUnit (overlapFace σ v) v)⁻¹ := by
  apply Units.ext
  simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, chartFace, overlapFace]

theorem incFaceVertexUnit_chart_update_other (σ : V → Bool) (v w : V)
    (b : Bool) (hw : w ≠ v) :
    G.incFaceVertexUnit (chartFace (Function.update σ v b)) w = G.incChartVertexUnit σ w := by
  apply Units.ext
  cases h : σ w <;>
    simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation, chartFace, hw, h]

theorem unitMonomial_chartRestriction (σ : V → Bool) (v : V) (b : Bool) (k : V → ℕ) :
    unitMonomial (G.incFaceVertexUnit (overlapFace σ v))
        (Multiplicative.ofAdd (faceToInt (overlapFace σ v) (overlapExponent σ v b k))) =
      unitMonomial (G.incFaceVertexUnit (chartFace (Function.update σ v b)))
        (Multiplicative.ofAdd (faceToInt (chartFace (Function.update σ v b))
          (chartMonoidEquiv (Function.update σ v b) k))) := by
  change (∏ w, G.incFaceVertexUnit (overlapFace σ v) w ^
    faceToInt (overlapFace σ v) (overlapExponent σ v b k) w) =
      ∏ w, G.incFaceVertexUnit (chartFace (Function.update σ v b)) w ^
        faceToInt (chartFace (Function.update σ v b))
          (chartMonoidEquiv (Function.update σ v b) k) w
  apply Finset.prod_congr rfl
  intro w _
  rw [faceToInt_overlapExponent, faceToInt_chartMonoid]
  by_cases hw : w = v
  · subst w
    cases b
    · simp only [ite_true, Bool.false_eq_true, ite_false, G.incFaceVertexUnit_overlap_false]
    · simp only [ite_true, G.incFaceVertexUnit_overlap_true, zpow_neg, inv_zpow]
  · rw [ite_eq_right hw, G.incFaceVertexUnit_overlap_other σ v w hw,
      G.incFaceVertexUnit_chart_update_other σ v w b hw]

theorem faceEvaluate_chartRestriction (σ : V → Bool) (v : V) (b : Bool)
    (x : FaceRing ℂ (chartFace (Function.update σ v b))) :
    faceEvaluate (overlapFace σ v) (G.incFaceVertexUnit (overlapFace σ v))
        (chartRestriction ℂ σ v b x) =
      faceEvaluate (chartFace (Function.update σ v b))
        (G.incFaceVertexUnit (chartFace (Function.update σ v b))) x := by
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | single m r =>
    obtain ⟨k, rfl⟩ := (chartMonoidEquiv (Function.update σ v b)).surjective m
    rw [chartRestriction_single, faceEvaluate_single, faceEvaluate_single,
      G.unitMonomial_chartRestriction]

theorem incFaceAmbientToTorus_chartRestriction (σ : V → Bool) (v : V) (b : Bool)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ (chartFace (Function.update σ v b)))) :
    G.incFaceAmbientToTorus (overlapFace σ v)
        (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b p) =
      G.incFaceAmbientToTorus (chartFace (Function.update σ v b)) p := by
  have h : (G.incFaceAmbientToTorus (overlapFace σ v)).comp
      (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b) =
        G.incFaceAmbientToTorus (chartFace (Function.update σ v b)) := by
    apply MvPolynomial.algHom_ext'
    · apply AlgHom.ext
      intro r
      change G.incFaceAmbientToTorus (overlapFace σ v)
        (chartPolynomialRestriction ℂ (IncCoeffIdx E) σ v b (MvPolynomial.C r)) =
          G.incFaceAmbientToTorus (chartFace (Function.update σ v b)) (MvPolynomial.C r)
      simp [incFaceAmbientToTorus, chartPolynomialRestriction, G.faceEvaluate_chartRestriction]
    · intro c
      simp [incFaceAmbientToTorus, chartPolynomialRestriction]
  exact AlgHom.congr_fun h p

end BPFixedPoints.Multigraph
