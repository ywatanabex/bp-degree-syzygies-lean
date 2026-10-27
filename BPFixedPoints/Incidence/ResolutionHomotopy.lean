import BPFixedPoints.Incidence.Perturbation
import Mathlib.Algebra.Module.Submodule.Basic

/-!
# Extract exactness from contractions

Obtain homogeneous exactness from a homotopy identity on the total module,
then transfer it to a free model along a chain retraction. Degrees are any
family of submodules, treating integer-graded bicomplexes and naturally graded
free resolutions with the same lemmas.
-/

namespace BPFixedPoints.ResolutionTools

section Homotopy

variable {R M H : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]

/-- For a cycle in the projection kernel, contraction homotopy provides a preimage. -/
theorem boundary_of_homotopy
    (D h : Module.End R M) (i : H →ₗ[R] M) (p : M →ₗ[R] H)
    (hhom : D.comp h + h.comp D + i.comp p = LinearMap.id)
    {x : M} (hDx : D x = 0) (hpx : p x = 0) : D (h x) = x := by
  have he := LinearMap.congr_fun hhom x
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hDx, hpx, map_zero, add_zero] using he

/-- If projection vanishes in positive degrees, degree-raising homotopy supplies homogeneous preimages. -/
theorem homogeneous_exact_of_homotopy
    (D h : Module.End R M) (i : H →ₗ[R] M) (p : M →ₗ[R] H)
    (hhom : D.comp h + h.comp D + i.comp p = LinearMap.id)
    (piece : ℕ → Submodule R M)
    (hh : ∀ n x, x ∈ piece (n + 1) → h x ∈ piece (n + 2))
    (hp : ∀ n x, x ∈ piece (n + 1) → p x = 0) :
    ∀ n x, x ∈ piece (n + 1) → D x = 0 →
      ∃ y, y ∈ piece (n + 2) ∧ D y = x := by
  intro n x hx hDx
  exact ⟨h x, hh n x hx, boundary_of_homotopy D h i p hhom hDx (hp n x hx)⟩

end Homotopy

section Retraction

variable {R M H U : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H]
  [AddCommGroup U] [Module R U]

variable (D : Module.End R M) (d : Module.End R H)
  (i : H →ₗ[R] M) (p : M →ₗ[R] H)
  (hi : D.comp i = i.comp d) (hp : p.comp D = d.comp p)
  (hpi : p.comp i = LinearMap.id)
  (Mpiece : ℕ → Submodule R M) (Hpiece : ℕ → Submodule R H)
  (higrade : ∀ n x, x ∈ Hpiece n → i x ∈ Mpiece n)
  (hpgrade : ∀ n x, x ∈ Mpiece n → p x ∈ Hpiece n)

include hi hp hpi higrade hpgrade in
/-- Degree-preserving chain retractions preserve positive-degree homogeneous exactness. -/
theorem homogeneous_exact_of_retraction
    (hexact : ∀ n x, x ∈ Mpiece (n + 1) → D x = 0 →
      ∃ y, y ∈ Mpiece (n + 2) ∧ D y = x) :
    ∀ n x, x ∈ Hpiece (n + 1) → d x = 0 →
      ∃ y, y ∈ Hpiece (n + 2) ∧ d y = x := by
  intro n x hx hdx
  have hix : D (i x) = 0 := by
    calc
      D (i x) = i (d x) := LinearMap.congr_fun hi x
      _ = 0 := by rw [hdx, map_zero]
  obtain ⟨y, hy, hDy⟩ := hexact n (i x) (higrade _ x hx) hix
  refine ⟨p y, hpgrade _ y hy, ?_⟩
  calc
    d (p y) = p (D y) := (LinearMap.congr_fun hp y).symm
    _ = p (i x) := by rw [hDy]
    _ = x := LinearMap.congr_fun hpi x

include hi hp hpi higrade hpgrade in
/-- Exactness at the augmentation kernel also transfers along chain retractions. -/
theorem augmentation_exact_of_retraction
    (ε : M →ₗ[R] U)
    (hεD : ε.comp D = 0)
    (hdzero : ∀ x, x ∈ Hpiece 0 → d x = 0)
    (hexact : ∀ x, x ∈ Mpiece 0 → D x = 0 → ε x = 0 →
      ∃ y, y ∈ Mpiece 1 ∧ D y = x) :
    ∀ x, x ∈ Hpiece 0 →
      ((ε.comp i) x = 0 ↔ ∃ y, y ∈ Hpiece 1 ∧ d y = x) := by
  intro x hx
  constructor
  · intro hεx
    have hix : D (i x) = 0 := by
      calc
        D (i x) = i (d x) := LinearMap.congr_fun hi x
        _ = 0 := by rw [hdzero x hx, map_zero]
    obtain ⟨y, hy, hDy⟩ := hexact (i x) (higrade 0 x hx) hix hεx
    refine ⟨p y, hpgrade 1 y hy, ?_⟩
    calc
      d (p y) = p (D y) := (LinearMap.congr_fun hp y).symm
      _ = p (i x) := by rw [hDy]
      _ = x := LinearMap.congr_fun hpi x
  · rintro ⟨y, _, rfl⟩
    change ε (i (d y)) = 0
    calc
      ε (i (d y)) = ε (D (i y)) := congrArg ε (LinearMap.congr_fun hi y).symm
      _ = 0 := LinearMap.congr_fun hεD (i y)

include hpgrade in
/-- Homotopy equivalences preserve augmentation surjectivity. -/
theorem augmentation_surjective_of_homotopy
    (h : Module.End R M)
    (hhom : D.comp h + h.comp D + i.comp p = LinearMap.id)
    (ε : M →ₗ[R] U) (hεD : ε.comp D = 0)
    (hεsurj : ∀ u, ∃ x, x ∈ Mpiece 0 ∧ D x = 0 ∧ ε x = u) :
    ∀ u, ∃ x, x ∈ Hpiece 0 ∧ (ε.comp i) x = u := by
  intro u
  obtain ⟨x, hx, hDx, hεx⟩ := hεsurj u
  refine ⟨p x, hpgrade 0 x hx, ?_⟩
  have he := congrArg ε (LinearMap.congr_fun hhom x)
  have hεh : ε (D (h x)) = 0 := LinearMap.congr_fun hεD (h x)
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hDx, map_zero, add_zero, map_add, hεh, zero_add, hεx] using he

end Retraction

end BPFixedPoints.ResolutionTools
