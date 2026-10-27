import BPFixedPoints.Incidence.ProjectiveLiftComparison
import BPFixedPoints.Incidence.DerivedSpecialization

/-! # Lifts with the same augmentation agree after specialization of minimal complexes -/

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace BPFixedPoints.ResolutionTools

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u
variable {R k : Type u} [CommRing R] [CommRing k] (φ : R →+* k)
  {K : ChainComplex (ModuleCat.{u} R) ℕ} [∀ n, Projective (K.X n)]
  {M : ModuleCat.{u} R} (P : ProjectiveResolution M)

theorem specialized_lifts_eq (f g : K ⟶ P.complex) (h : f ≫ P.π = g ≫ P.π)
    (hK : ∀ i j, LinearMap.range (K.d i j).hom ≤
      RingHom.ker φ • (⊤ : Submodule R (K.X j)))
    (hP : ∀ i j, LinearMap.range (P.complex.d i j).hom ≤
      RingHom.ker φ • (⊤ : Submodule R (P.complex.X j))) (n : ℕ) :
    (ModuleCat.extendScalars φ).map (f.f n) = (ModuleCat.extendScalars φ).map (g.f n) := by
  let F := ModuleCat.extendScalars φ
  let H := projectiveLiftHomotopy P f g h
  have hc := congrArg (fun u : K.X n ⟶ P.complex.X n => F.map u)
    (H.comm n)
  change F.map (f.f n) = F.map
    (K.d n ((ComplexShape.down ℕ).next n) ≫ H.hom ((ComplexShape.down ℕ).next n) n +
      H.hom n ((ComplexShape.down ℕ).prev n) ≫ P.complex.d ((ComplexShape.down ℕ).prev n) n + g.f n) at hc
  have hKzero (i j : ℕ) : F.map (K.d i j) = 0 := extendScalars_map_eq_zero φ _ (hK i j)
  have hPzero (i j : ℕ) : F.map (P.complex.d i j) = 0 := extendScalars_map_eq_zero φ _ (hP i j)
  rw [F.map_add, F.map_add, F.map_comp, F.map_comp, hKzero, hPzero,
    zero_comp, comp_zero, zero_add, zero_add] at hc
  exact hc

end BPFixedPoints.ResolutionTools
