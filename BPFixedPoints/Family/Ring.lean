import BPFixedPoints.Degree.Equations

/-! # Coordinate ring of the total admissible BP space -/

namespace BPFixedPoints

namespace Multigraph

open MvPolynomial BP

variable {V E : Type} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] (G : Multigraph V E)

/-- Variables of the total space: a_e, b_i and messages y_α. -/
abbrev FamVar (V E : Type) := E ⊕ V ⊕ Dart E

/-- Variable a_e. -/
noncomputable def famA (e : E) : MvPolynomial (FamVar V E) ℂ := X (Sum.inl e)
/-- Variable b_i. -/
noncomputable def famB (i : V) : MvPolynomial (FamVar V E) ℂ := X (Sum.inr (Sum.inl i))
/-- Variable y_α. -/
noncomputable def famY (α : Dart E) : MvPolynomial (FamVar V E) ℂ := X (Sum.inr (Sum.inr α))

/-- Cavity-field polynomial X_α=b_{t(α)}∏_{h(γ)=t(α),γ≠ᾱ}y_γ. -/
noncomputable def famCavity (α : Dart E) : MvPolynomial (FamVar V E) ℂ :=
  famB (G.tail α) * ∏ γ ∈ (G.inDarts (G.tail α)).erase (rev α), famY γ

/-- Total-field polynomial F_i=b_i∏_{h(α)=i}y_α. -/
noncomputable def famTotalField (i : V) : MvPolynomial (FamVar V E) ℂ :=
  famB i * ∏ α ∈ G.inDarts i, famY α

/-- BP residual f_α=y_α(X_α+a_e)−(a_e X_α+1). -/
noncomputable def famResidual (α : Dart E) : MvPolynomial (FamVar V E) ℂ :=
  famY α * (G.famCavity α + famA α.1) - (famA α.1 * G.famCavity α + 1)

/-- Denominator of the parameter torus and admissible open set: ∏a·∏b·∏y·∏(X_α+a)·∏(1+F_i). -/
noncomputable def famDen : MvPolynomial (FamVar V E) ℂ :=
  (∏ e, famA e) * (∏ i, famB i) * (∏ α, famY α) * (∏ α, (G.famCavity α + famA α.1)) *
    ∏ i, (1 + G.famTotalField i)

/-- Coordinate ring A_G=ℂ[a,b,y][1/(∏a·∏b·D)]/(f_α) of the total admissible BP space 𝒳_G. -/
abbrev FamilyRing :=
  Localization.Away G.famDen ⧸
    Ideal.span (Set.range fun α => algebraMap _ (Localization.Away G.famDen) (G.famResidual α))

end Multigraph

end BPFixedPoints
