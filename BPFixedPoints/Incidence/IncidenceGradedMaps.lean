import BPFixedPoints.Incidence.IncidenceGradedMapsScaling
import BPFixedPoints.Incidence.IncidenceGraphMapRings
import BPFixedPoints.Incidence.NaturalGradedResolution

/-!
# Graph maps induce graded maps of incidence rings (`alg:functoriality`, grading)

For a graph map `φ : GraphMap G H` the incidence ring map `𝒰_φ = φ.incidenceHom : 𝒰_G → 𝒰_H`
(the restriction of the substitution `t_v ↦ t_{φ v}`, `s_v ↦ s_{φ v}`, `c ↦ ε c'`) preserves the
natural coefficient grading `incidenceCoefficientPiece` (vertex coordinates in degree `0`,
coefficients in degree `1`).

* **Torus level.** The substitution of torus variables commutes with coefficient scaling
  `c ↦ a c` (`torusPolyHom_comp_incTorusScalePoly`), hence so do the torus ring map
  (`torusHom_incTorusScale`) and the incidence ring map (`incidenceHom_incidenceScale`). No order
  on the edges is needed here.
* **Grading.** By the scaling characterization of the natural grading
  (`mem_incidenceCoefficientPiece_iff_scale`, in `IncidenceGradedMapsScaling.lean`), `𝒰_φ` sends
  the degree-`n` piece of `𝒰_G` into the degree-`n` piece of `𝒰_H` for every `n`
  (`incidenceHom_mem_incidenceCoefficientPiece`, `map_incidenceCoefficientPiece_le`).
* **Graded algebra maps.** With the graded algebra structures `incidenceCoefficientGradedAlgebra`
  (as local instances), `𝒰_φ` is a Mathlib `GradedAlgHom` (`incidenceGradedHom`); it commutes with
  taking homogeneous components (`incidenceHom_decompose`) and satisfies the identity and
  composition laws (`incidenceGradedHom_refl`, `incidenceGradedHom_trans`).
* **Factors.** The same holds for vertex maps
  (`VertexMap.incidenceHom_mem_incidenceCoefficientPiece`, `VertexMap.incidenceGradedHom`) and
  signed edge maps
  (`SignedEdgeMap.signedIncidenceHom_mem_incidenceCoefficientPiece`,
  `SignedEdgeMap.signedIncidenceGradedHom`), and the graded map of a graph map is the composite of
  those of its two factors (`GraphMap.incidenceGradedHom_eq_comp`).

The results hold for all graph maps; the noncontracting condition of the paper is not used. The
graded algebra structures need linear orders on the edge types only because the natural grading is
defined through the chart presentations. Not covered: chart ring maps of graph maps, gradings of
`Tor` or of free resolutions, and the identification of `IncidenceRing` with sheaf global sections.
The disjoint union formula is treated in `IncidenceGradedMapsDisjointUnion.lean`.
-/

set_option linter.unusedSectionVars false

namespace BPFixedPoints.Multigraph

open MvPolynomial

namespace GraphMap

/-! ### Graph maps commute with coefficient scaling -/

section Scaling

variable {V W E E' : Type} {G : Multigraph V E} {H : Multigraph W E'}
  [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq E] [Fintype E]
  [DecidableEq E'] [Fintype E'] (φ : GraphMap G H)

/-- The substitution of torus variables of a graph map commutes with coefficient scaling: both
fix the vertex variables, and a coefficient goes to a signed coefficient. -/
theorem torusPolyHom_comp_incTorusScalePoly (a : ℂ) :
    φ.torusPolyHom.comp (incTorusScalePoly a) = (incTorusScalePoly a).comp φ.torusPolyHom := by
  apply MvPolynomial.algHom_ext
  rintro (v | v | c)
  · simp [incTorusScalePoly, incTorusScaleVal, torusVal]
  · simp [incTorusScalePoly, incTorusScaleVal, torusVal]
  · simp only [AlgHom.comp_apply, incTorusScalePoly, aeval_X, incTorusScaleVal, map_mul,
      torusPolyHom_X, torusVal, map_intCast, algHom_C, algebraMap_eq]
    ring

/-- **The torus ring map of a graph map commutes with coefficient scaling.** -/
theorem torusHom_incTorusScale (a : ℂ) (x : G.IncTorusRing) :
    φ.torusHom (G.incTorusScale a x) = H.incTorusScale a (φ.torusHom x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [incTorusScale_mk, torusHom_mk, torusHom_mk, incTorusScale_mk]
  exact congrArg _ (AlgHom.congr_fun (φ.torusPolyHom_comp_incTorusScalePoly a) p)

/-- **The incidence ring map of a graph map commutes with coefficient scaling.** -/
theorem incidenceHom_incidenceScale (a : ℂ) (x : G.IncidenceRing) :
    φ.incidenceHom (G.incidenceScale a x) = H.incidenceScale a (φ.incidenceHom x) :=
  Subtype.ext (φ.torusHom_incTorusScale a x.val)

end Scaling

/-! ### Graph maps preserve the natural grading -/

section Grading

variable {V W E E' : Type} {G : Multigraph V E} {H : Multigraph W E'}
  [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [LinearOrder E] [Fintype E]
  [LinearOrder E'] [Fintype E'] (φ : GraphMap G H)

/-- **A graph map preserves the natural coefficient degree**: `𝒰_φ` sends the degree-`n` piece of
`𝒰_G` into the degree-`n` piece of `𝒰_H`. -/
theorem incidenceHom_mem_incidenceCoefficientPiece {n : ℕ} {x : G.IncidenceRing}
    (hx : x ∈ G.incidenceCoefficientPiece n) :
    φ.incidenceHom x ∈ H.incidenceCoefficientPiece n := by
  rw [mem_incidenceCoefficientPiece_iff_scale] at hx ⊢
  intro a
  rw [← incidenceHom_incidenceScale, hx a]
  exact φ.incidenceHom.toLinearMap.map_smul _ _

/-- The image of the degree-`n` piece under a graph map lies in the degree-`n` piece. -/
theorem map_incidenceCoefficientPiece_le (n : ℕ) :
    (G.incidenceCoefficientPiece n).map φ.incidenceHom.toLinearMap ≤
      H.incidenceCoefficientPiece n := by
  rintro _ ⟨x, hx, rfl⟩
  exact φ.incidenceHom_mem_incidenceCoefficientPiece hx

attribute [local instance] incidenceCoefficientGradedAlgebra

/-- **The graded incidence ring map** of a graph map: `𝒰_φ` as a homomorphism of graded
`ℂ`-algebras for the natural coefficient gradings. -/
noncomputable def incidenceGradedHom :
    G.incidenceCoefficientPiece →ₐᵍ[ℂ] H.incidenceCoefficientPiece where
  toAlgHom := φ.incidenceHom
  map_mem := φ.incidenceHom_mem_incidenceCoefficientPiece

/-- The graded incidence ring map is the incidence ring map. -/
@[simp] theorem incidenceGradedHom_apply (x : G.IncidenceRing) :
    φ.incidenceGradedHom x = φ.incidenceHom x := rfl

/-- A graph map commutes with taking homogeneous components. -/
theorem incidenceHom_decompose (x : G.IncidenceRing) (n : ℕ) :
    φ.incidenceHom (DirectSum.decompose G.incidenceCoefficientPiece x n : G.IncidenceRing) =
      (DirectSum.decompose H.incidenceCoefficientPiece (φ.incidenceHom x) n : H.IncidenceRing) :=
  map_directSumDecompose G.incidenceCoefficientPiece H.incidenceCoefficientPiece
    φ.incidenceGradedHom

end Grading

/-! ### Identity and composition -/

section Laws

variable {V W X E E' E'' : Type} {G : Multigraph V E} {H : Multigraph W E'}
  {K : Multigraph X E''}
  [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W] [DecidableEq X] [Fintype X]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E'] [LinearOrder E''] [Fintype E'']

attribute [local instance] incidenceCoefficientGradedAlgebra

/-- **Identity law** for the graded incidence ring map. -/
theorem incidenceGradedHom_refl (G : Multigraph V E) :
    (refl G).incidenceGradedHom = GradedAlgHom.id ℂ G.incidenceCoefficientPiece :=
  GradedAlgHom.ext fun x => incidenceHom_refl_apply G x

/-- **Composition law** for the graded incidence ring map. -/
theorem incidenceGradedHom_trans (φ : GraphMap G H) (ψ : GraphMap H K) :
    (φ.trans ψ).incidenceGradedHom = ψ.incidenceGradedHom.comp φ.incidenceGradedHom :=
  GradedAlgHom.ext fun x => incidenceHom_trans_apply φ ψ x

end Laws

end GraphMap

/-! ### The two factor maps -/

section Factors

variable {V W E E' : Type} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
  [LinearOrder E] [Fintype E] [LinearOrder E'] [Fintype E']

/-- **A vertex map preserves the natural coefficient degree.** -/
theorem VertexMap.incidenceHom_mem_incidenceCoefficientPiece {G : Multigraph V E}
    {H : Multigraph W E} (φ : VertexMap G H) {n : ℕ} {x : G.IncidenceRing}
    (hx : x ∈ G.incidenceCoefficientPiece n) :
    φ.incidenceHom x ∈ H.incidenceCoefficientPiece n := by
  rw [← VertexMap.toGraphMap_incidenceHom]
  exact φ.toGraphMap.incidenceHom_mem_incidenceCoefficientPiece hx

/-- **A signed edge map preserves the natural coefficient degree.** -/
theorem SignedEdgeMap.signedIncidenceHom_mem_incidenceCoefficientPiece {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeMap G H) {n : ℕ} {x : G.IncidenceRing}
    (hx : x ∈ G.incidenceCoefficientPiece n) :
    φ.signedIncidenceHom x ∈ H.incidenceCoefficientPiece n := by
  rw [← SignedEdgeMap.toGraphMap_incidenceHom]
  exact φ.toGraphMap.incidenceHom_mem_incidenceCoefficientPiece hx

attribute [local instance] incidenceCoefficientGradedAlgebra

/-- The incidence ring map of a vertex map, as a homomorphism of graded algebras. -/
noncomputable def VertexMap.incidenceGradedHom {G : Multigraph V E} {H : Multigraph W E}
    (φ : VertexMap G H) : G.incidenceCoefficientPiece →ₐᵍ[ℂ] H.incidenceCoefficientPiece where
  toAlgHom := φ.incidenceHom
  map_mem := φ.incidenceHom_mem_incidenceCoefficientPiece

/-- The signed incidence ring map of a signed edge map, as a homomorphism of graded algebras. -/
noncomputable def SignedEdgeMap.signedIncidenceGradedHom {G : Multigraph V E}
    {H : Multigraph V E'} (φ : SignedEdgeMap G H) :
    G.incidenceCoefficientPiece →ₐᵍ[ℂ] H.incidenceCoefficientPiece where
  toAlgHom := φ.signedIncidenceHom
  map_mem := φ.signedIncidenceHom_mem_incidenceCoefficientPiece

/-- **Graded factorization.** The graded incidence ring map of a graph map is the composite of
those of its vertex factor and its edge factor. -/
theorem GraphMap.incidenceGradedHom_eq_comp {G : Multigraph V E} {H : Multigraph W E'}
    (φ : GraphMap G H) :
    φ.incidenceGradedHom =
      φ.edgeFactor.signedIncidenceGradedHom.comp φ.vertexFactor.incidenceGradedHom :=
  GradedAlgHom.ext fun x => φ.incidenceHom_eq_comp_apply x

end Factors

end BPFixedPoints.Multigraph
