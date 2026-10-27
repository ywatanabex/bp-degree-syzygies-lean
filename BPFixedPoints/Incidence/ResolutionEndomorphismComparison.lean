import BPFixedPoints.Incidence.TorProductCoordinates

/-! # Augmentation-preserving resolution endomorphisms specialize to the identity -/

set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.Multigraph

open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

noncomputable local instance resolutionEndomorphismComparisonOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

variable (L : Module.End (IncCoeffRing E) (G.IncResolutionBasis →₀ IncCoeffRing E))
  (hdegree : ∀ (n : ℕ) {x}, x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n →
    L x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n)
  (hchain : ∀ x, G.incResolutionDifferential (L x) = L (G.incResolutionDifferential x))

noncomputable def incResolutionEndomorphism :
    G.incFreeResolution.complex ⟶ G.incFreeResolution.complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((L.comp (gradedPiece (IncCoeffRing E) G.incResolutionDegree n).subtype).codRestrict _
      (fun x => hdegree n x.property))) (fun n => by
        simp only [G.incFreeResolution_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact hchain x.val)

include hdegree hchain in
/-- Specialize a homotopy with the identity map at the origin. -/
theorem incResolutionEndomorphism_atOrigin
    (haug : ∀ x : G.IncFreeTerm 0,
      G.incResolutionTorusAugmentation (L x.val) = G.incResolutionTorusAugmentation x.val)
    (n : ℕ) (x : G.IncFreeTerm n) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] L x.val = (1 : ℂ) ⊗ₜ[IncCoeffRing E] x.val := by
  let f := G.incResolutionEndomorphism L hdegree hchain
  have h : f ≫ G.incFreeResolution.π = (𝟙 _) ≫ G.incFreeResolution.π := by
    apply HomologicalComplex.to_single_hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact haug x
  have he := specialized_lifts_eq
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)
    G.incFreeResolution f (𝟙 _) h G.incFreeResolution_minimal G.incFreeResolution_minimal n
  have hh := congrArg (fun u => u.hom ((1 : ℂ) ⊗ₜ[IncCoeffRing E] x)) he
  have hj := congrArg ((gradedPiece (IncCoeffRing E) G.incResolutionDegree n).subtype.baseChange ℂ) hh
  exact hj

end BPFixedPoints.Multigraph
