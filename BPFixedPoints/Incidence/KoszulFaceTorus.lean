import BPFixedPoints.Incidence.KoszulFaces
import BPFixedPoints.Incidence.KoszulFaceEvaluation
import BPFixedPoints.Incidence.Torus

/-! # Maps from Čech incidence-face rings to the common torus -/

namespace BPFixedPoints.CechProduct

def faceOrientation {V : Type*} (q : V → Fin 3) : V → Bool := fun v => decide (q v = 1)

end BPFixedPoints.CechProduct

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- Every chart vertex coordinate is a unit on the common torus. -/
noncomputable def incChartVertexUnit (σ : V → Bool) (v : V) : G.IncTorusRingˣ where
  val := G.incChartVal σ (Sum.inl v)
  inv := if σ v then Ideal.Quotient.mk _ (X (Sum.inl v))
    else Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v)))
  val_inv := by
    cases h : σ v
    · simpa [incChartVal, h] using G.incTorus_ts v
    · simpa [incChartVal, h, mul_comm] using G.incTorus_ts v
  inv_val := by
    cases h : σ v
    · simpa [incChartVal, h, mul_comm] using G.incTorus_ts v
    · simpa [incChartVal, h] using G.incTorus_ts v

/-- Common-torus units representing face vertex coordinates. -/
noncomputable def incFaceVertexUnit (q : V → Fin 3) (v : V) : G.IncTorusRingˣ :=
  G.incChartVertexUnit (faceOrientation q) v

@[simp] theorem incFaceVertexUnit_val (q : V → Fin 3) (v : V) :
    (G.incFaceVertexUnit q v : G.IncTorusRing) = G.incChartVal (faceOrientation q) (Sum.inl v) := rfl

/-- Evaluate face polynomial/Laurent coordinates and coefficients on the common torus. -/
noncomputable def incFaceAmbientToTorus (q : V → Fin 3) :
    MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q) →ₐ[ℂ] G.IncTorusRing :=
  facePolynomialEvaluate q (G.incFaceVertexUnit q)
    (fun c => Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c))))

theorem incFaceAmbientToTorus_equation (q : V → Fin 3) (e : E) :
    G.incFaceAmbientToTorus q (G.incFaceEquation q e) = 0 := by
  have h := G.eval_incChartEq (faceOrientation q) e
  simp only [incChartEq, map_sum, map_mul, map_incCoord, aeval_X, incChartVal] at h
  simpa only [incFaceAmbientToTorus, incFaceEquation, map_sum, map_mul,
    facePolynomialEvaluate_X, facePolynomialEvaluate_C, map_incCoord,
    faceEvaluate_variable, incFaceVertexUnit_val, incChartVal, faceOrientation] using h

/-- Natural map from any incidence face ring to the common torus. -/
noncomputable def incFaceToTorus (q : V → Fin 3) : G.IncFaceRing q →ₐ[ℂ] G.IncTorusRing :=
  Ideal.Quotient.liftₐ _ (G.incFaceAmbientToTorus q) <| by
    intro p hp
    have hle : G.incFaceIdeal q ≤ RingHom.ker (G.incFaceAmbientToTorus q).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨e, rfl⟩
      exact G.incFaceAmbientToTorus_equation q e
    exact hle hp

@[simp] theorem incFaceToTorus_mk (q : V → Fin 3)
    (p : MvPolynomial (IncCoeffIdx E) (FaceRing ℂ q)) :
    G.incFaceToTorus q (Ideal.Quotient.mk _ p) = G.incFaceAmbientToTorus q p := rfl

@[simp] theorem incFaceToTorus_X (q : V → Fin 3) (c : IncCoeffIdx E) :
    G.incFaceToTorus q (Ideal.Quotient.mk _ (X c)) =
      Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr c))) := by
  simp [incFaceAmbientToTorus]

@[simp] theorem incFaceToTorus_C_variable (q : V → Fin 3) (v : V) :
    G.incFaceToTorus q (Ideal.Quotient.mk _ (C (faceVariable ℂ q v))) =
      G.incChartVal (faceOrientation q) (Sum.inl v) := by
  simp [incFaceAmbientToTorus]

/-- Monomial evaluation formula for comparison with boundary chart restrictions. -/
theorem incFaceToTorus_C_single (q : V → Fin 3) (m : FaceMonoid q) (r : ℂ) :
    G.incFaceToTorus q (Ideal.Quotient.mk _ (C (AddMonoidAlgebra.single m r))) =
      r • (IncidenceLaurent.unitMonomial (G.incFaceVertexUnit q)
        (Multiplicative.ofAdd (faceToInt q m)) : G.IncTorusRing) := by
  simp [incFaceAmbientToTorus]

end BPFixedPoints.Multigraph
