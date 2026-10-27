import BPFixedPoints.Incidence.GradedMixedTensor
import BPFixedPoints.Incidence.ResolutionTorProduct

/-! # Specialize two maps from a projective free complex to the incidence resolution -/
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
namespace BPFixedPoints.Multigraph
open Finsupp ResolutionTools CategoryTheory
open scoped TensorProduct

variable {V E B : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E) (db : B → ℕ) (D : Module.End (IncCoeffRing E) (B →₀ IncCoeffRing E))
  (hd : HasDegree (fun b => (db b : ℤ)) (fun b => (db b : ℤ)) (-1) D) (hD : D * D = 0)

noncomputable local instance resolutionMapComparisonOriginAlgebra : Algebra (IncCoeffRing E) ℂ :=
  (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ).toAlgebra

noncomputable def incResolutionMap
    (L : (B →₀ IncCoeffRing E) →ₗ[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E))
    (hdegree : ∀ n {x}, x ∈ gradedPiece (IncCoeffRing E) db n →
      L x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n)
    (hchain : ∀ x, G.incResolutionDifferential (L x) = L (D x)) :
    gradedFreeComplex db D hd hD ⟶ G.incFreeResolution.complex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((L.comp (gradedPiece (IncCoeffRing E) db n).subtype).codRestrict _
      (fun x => hdegree n x.property))) (fun n => by
        rw [G.incFreeResolution_d, gradedFreeComplex_d]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        exact hchain x.val)

include hd hD in
theorem incResolutionMap_atOrigin
    (L M : (B →₀ IncCoeffRing E) →ₗ[IncCoeffRing E] (G.IncResolutionBasis →₀ IncCoeffRing E))
    (hL : ∀ n {x}, x ∈ gradedPiece (IncCoeffRing E) db n →
      L x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n)
    (hM : ∀ n {x}, x ∈ gradedPiece (IncCoeffRing E) db n →
      M x ∈ gradedPiece (IncCoeffRing E) G.incResolutionDegree n)
    (hcL : ∀ x, G.incResolutionDifferential (L x) = L (D x))
    (hcM : ∀ x, G.incResolutionDifferential (M x) = M (D x))
    (hmin : ∀ x, D x ∈ incCoeffAugmentationIdeal E • (⊤ : Submodule (IncCoeffRing E) (B →₀ IncCoeffRing E)))
    (haug : ∀ x : gradedPiece (IncCoeffRing E) db 0,
      G.incResolutionTorusAugmentation (L x.val) = G.incResolutionTorusAugmentation (M x.val))
    (n : ℕ) (x : gradedPiece (IncCoeffRing E) db n) :
    (1 : ℂ) ⊗ₜ[IncCoeffRing E] L x.val = (1 : ℂ) ⊗ₜ[IncCoeffRing E] M x.val := by
  let f := G.incResolutionMap db D hd hD L hL hcL
  let g := G.incResolutionMap db D hd hD M hM hcM
  have h : f ≫ G.incFreeResolution.π = g ≫ G.incFreeResolution.π := by
    apply HomologicalComplex.to_single_hom_ext
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact haug x
  have he := specialized_lifts_eq
    (MvPolynomial.constantCoeff : IncCoeffRing E →+* ℂ)
    G.incFreeResolution f g h
    (gradedFreeComplex_minimal db D hd hD (incCoeffAugmentationIdeal E) hmin)
    G.incFreeResolution_minimal n
  have hh := congrArg (fun u => u.hom ((1 : ℂ) ⊗ₜ[IncCoeffRing E] x)) he
  exact congrArg ((gradedPiece (IncCoeffRing E) G.incResolutionDegree n).subtype.baseChange ℂ) hh

end BPFixedPoints.Multigraph
