import BPFixedPoints.Incidence.ProjectiveLineProper
import BPFixedPoints.Incidence.IncidenceProjectiveZeroSections

/-! # Properness of the actual finite projective product and incidence projection

Mathlib's base-change and composition theorems propagate projective-line
properness to the actual products over the original coefficient scheme. The
independent incidence zero scheme is closed in that product, and hence proper.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable (R : Type*) [CommRing R]

/-- The genuine finite product is proper over the original coefficient scheme, including the empty product. -/
instance powerToBase_isProper (n : ℕ) : IsProper (powerToBase R n) := by
  induction n with
  | zero => change IsProper (𝟙 (Spec (CommRingCat.of R))); infer_instance
  | succ n ih =>
    haveI : IsProper (powerToBase R n) := ih
    have he : powerToBase R (n+1) = (powerSuccessorIso R n).hom ≫
        pullback.fst (toSpecBase R) (powerToBase R n) ≫ toSpecBase R := by
      change _ = (Over.prodLeftIsoPullback (overBase R) (powerOverBase R n)).hom ≫
        pullback.fst _ _ ≫ _
      rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
      exact (prod.fst : overBase R ⨯ powerOverBase R n ⟶ overBase R).w.symm
    rw [he]
    infer_instance

/-- The original-labelled projective product is proper over its original coefficient scheme. -/
instance vertexToBase_isProper (V : Type) [Fintype V] : IsProper (vertexToBase R V) := by
  change IsProper (powerToBase R (Fintype.card V))
  infer_instance

end BPFixedPoints.ProjectiveLine

namespace BPFixedPoints.Multigraph
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]
  (G : Multigraph V E)

/-- The independently defined projective incidence zero scheme is proper over coefficient space. -/
instance incidenceProjectiveZeroToBase_isProper : IsProper G.incidenceProjectiveZeroToBase := by
  dsimp only [incidenceProjectiveZeroToBase]
  infer_instance

/-- The original geometric coefficient projection of the glued incidence scheme is proper. -/
instance incidenceCoefficientMorphism_isProper : IsProper G.incidenceCoefficientMorphism := by
  rw [← G.incidenceProjectiveMorphism_toBase]
  infer_instance

/-- Properness holds after every actual scheme base change of the coefficient space. -/
theorem incidenceProjectiveZero_baseChange_proper {T : Scheme}
    (f : T ⟶ Spec (CommRingCat.of (IncCoeffRing E))) :
    IsProper (pullback.snd G.incidenceProjectiveZeroToBase f) := by
  infer_instance

end BPFixedPoints.Multigraph
