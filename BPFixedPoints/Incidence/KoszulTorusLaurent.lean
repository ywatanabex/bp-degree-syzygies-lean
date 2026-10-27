import BPFixedPoints.Incidence.KoszulFaceTorus

/-! # Comparison from the common torus to a Laurent ring using free coordinates -/

namespace BPFixedPoints.Multigraph

open MvPolynomial CechProduct IncidenceLaurent

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

theorem incLaurentDen_unit :
    IsUnit (polynomialMap (incFreeDen (V := V) (E := E))) := by
  rw [incFreeDen, map_prod]
  exact IsUnit.prod_iff.mpr fun v _ => polynomialMap_X_unit (Sum.inl v)

/-- Localization comparison map sending all free coordinates to Laurent coordinates. -/
noncomputable def incLocalToLaurent :
    IncLocalRing V E →ₐ[ℂ] LaurentRing (IncFreeVar V E) ℂ :=
  localizationMap incFreeDen incLaurentDen_unit

@[simp] theorem incLocalToLaurent_algebraMap (p : IncFreeRing V E) :
    incLocalToLaurent (algebraMap (IncFreeRing V E) (IncLocalRing V E) p) =
      polynomialMap p :=
  localizationMap_algebraMap incFreeDen incLaurentDen_unit p

/-- Map the common torus to the Laurent ring using the selected chart's free coordinates. -/
noncomputable def incTorusToLaurent (σ : V → Bool) :
    G.IncTorusRing →ₐ[ℂ] LaurentRing (IncFreeVar V E) ℂ :=
  incLocalToLaurent.comp (G.incTorusToLocal σ)

@[simp] theorem incTorusToLaurent_chartVertex (σ : V → Bool) (v : V) :
    G.incTorusToLaurent σ (G.incChartVal σ (Sum.inl v)) =
      polynomialMap (X (Sum.inl v)) := by
  cases h : σ v <;> simp [incTorusToLaurent, incChartVal, incLocalVal, h]

@[simp] theorem incTorusToLaurent_coeff (σ : V → Bool) (e : E) (α β : Fin 2) :
    G.incTorusToLaurent σ (Ideal.Quotient.mk _ (X (Sum.inr (Sum.inr (e, α, β))))) =
      polynomialMap (G.incFreeCoeff e (incFlip (σ (G.fst e)) α)
        (incFlip (σ (G.snd e)) β)) := by
  simp [incTorusToLaurent, incLocalVal]

theorem incTorusToLaurent_vertexUnit (q : V → Fin 3) (v : V) :
    Units.map (G.incTorusToLaurent (faceOrientation q)).toMonoidHom (G.incFaceVertexUnit q v) =
      monomialUnit (leftExponent (J := E × Fin 3) (Pi.single v 1)) := by
  apply Units.ext
  change G.incTorusToLaurent (faceOrientation q) (G.incChartVal (faceOrientation q) (Sum.inl v)) =
    AddMonoidAlgebra.single (leftExponent (Pi.single v 1)) 1
  rw [G.incTorusToLaurent_chartVertex, polynomialMap_X, natExponent_single]
  congr 1
  funext i
  rcases i with w | j <;> simp [leftExponent, Pi.single_apply]

end BPFixedPoints.Multigraph
