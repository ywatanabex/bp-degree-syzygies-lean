import BPFixedPoints.Incidence.IncidenceFaceRefinement

/-! # The all-Laurent incidence face is the original common torus

The existing injection of every face into the torus is surjective for the
all-Laurent face: it contains both vertex coordinates and their inverses, as
well as the original universal coefficient variables.
-/

namespace BPFixedPoints.Multigraph
open MvPolynomial CechProduct IncidenceLaurent
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The original inverse vertex coordinate is the negative Laurent monomial. -/
theorem incFaceToTorus_laurent_inverse (v : V) :
    G.incFaceToTorus (fun _ => 2)
      (Ideal.Quotient.mk _ (C (AddMonoidAlgebra.single (Pi.single v (-1 : ℤ)) 1))) =
        Ideal.Quotient.mk _ (X (Sum.inr (Sum.inl v))) := by
  rw [G.incFaceToTorus_C_single]
  have he : faceToInt (fun _ : V => 2) (Pi.single v (-1 : ℤ)) = Pi.single v (-1 : ℤ) := rfl
  rw [he, unitMonomial_single]
  simp [incFaceVertexUnit, incChartVertexUnit, incChartVal, faceOrientation]

/-- Every actual common-torus element has an original all-Laurent face representative. -/
theorem incFaceToTorus_laurent_surjective :
    Function.Surjective (G.incFaceToTorus (fun _ => 2)) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hv (i : IncTorusVar V E) : ∃ y, G.incFaceToTorus (fun _ => 2) y =
      Ideal.Quotient.mk (Ideal.span (Set.range G.incTorusRel)) (X i) := by
    rcases i with v | v | c
    · refine ⟨Ideal.Quotient.mk _ (C (faceVariable ℂ (fun _ => 2) v)), ?_⟩
      rw [G.incFaceToTorus_C_variable]
      simp [incChartVal, faceOrientation]
    · exact ⟨_, G.incFaceToTorus_laurent_inverse v⟩
    · exact ⟨_, G.incFaceToTorus_X (fun _ => 2) c⟩
  induction p using MvPolynomial.induction_on with
  | C c =>
      refine ⟨algebraMap ℂ _ c, ?_⟩
      rw [AlgHom.commutes]
      rfl
  | add p q hp hq =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hq
      exact ⟨a+b, by rw [map_add, ha, hb, map_add]⟩
  | mul_X p i hp =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hv i
      exact ⟨a*b, by rw [map_mul, ha, hb, map_mul]⟩

/-- Natural identification, using the existing torus evaluation map. -/
noncomputable def incLaurentFaceEquiv :
    G.IncFaceRing (fun _ => 2) ≃ₐ[ℂ] G.IncTorusRing :=
  AlgEquiv.ofBijective (G.incFaceToTorus (fun _ => 2))
    ⟨G.incFaceToTorus_injective _, G.incFaceToTorus_laurent_surjective⟩

end BPFixedPoints.Multigraph
