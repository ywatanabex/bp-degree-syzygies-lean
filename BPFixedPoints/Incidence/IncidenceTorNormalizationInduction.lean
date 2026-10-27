import BPFixedPoints.Incidence.IncidenceTorExteriorIsomorphism

/-! # Induction on exterior cohomology through Tor

Over `ℂ`, every class of actual cohomology `H^j` of the `q`-th exterior bundle is reached from Tor:
* if `j ≤ q`, then `j = q - p` with `p = q - j ≤ q`, and the Tor-to-exterior isomorphism
  `incidenceTorExteriorEquiv` (bidegree `(p, q)`) is surjective onto `H^{q-p}`;
* if `j > q`, the cohomology vanishes (`exteriorBundleCohomology_eq_zero_of_lt`).

This case split recurs in the proofs of the graph-map laws of exterior cohomology
(`IncidenceGraphMapExterior`). It is packaged here once:
* `exteriorCohomology_induction_on_tor`: an induction principle (`@[elab_as_elim]`, usable with
  `induction j, x using exteriorCohomology_induction_on_tor`) whose motive may depend on the
  cohomological degree; its two cases are the images of Tor classes in degree `q - p` and the zero
  class in degrees above `q`, so no transport along `j = q - p` is needed;
* `exteriorCohomology_induction₂_on_tor`: the same for two classes at once (for products);
* `exteriorCohomology_ext_via_tor`: two families of additive maps out of exterior cohomology agree
  in every degree once they agree on the images of Tor classes.

`BPFixedPoints.Incidence.IncidenceTorNormalizationGraphMaps` re-proves the identity, composition,
scalar, product and vertex-map laws of `IncidenceGraphMapExterior` with these principles.
Nothing here is specific to graph maps, and nothing beyond the coefficient field `ℂ` is treated.
-/

namespace BPFixedPoints.Multigraph
open CategoryTheory TopologicalSpace AlgebraicGeometry ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
noncomputable section

variable {V E : Type} [DecidableEq V] [Fintype V] [LinearOrder E] [Fintype E]

local instance incidenceTorNormalizationInductionHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (vertexScheme ℂ V)) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- **Induction on exterior cohomology through Tor.** A property of classes of actual cohomology
of the `q`-th exterior bundle over `ℂ`, in all cohomological degrees, holds once it holds for the
image of every Tor class of bidegree `(p, q)` with `p ≤ q` (in degree `q - p`) and for the zero
class in every degree above `q`. -/
@[elab_as_elim]
theorem exteriorCohomology_induction_on_tor {G : Multigraph V E} {q : ℕ}
    {motive : (j : ℕ) → Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j → Prop}
    (tor : ∀ (p : ℕ) (hp : p ≤ q) (y : G.incidenceTorInternalPiece p q),
      motive (q - p) (G.incidenceTorExteriorEquiv hp y))
    (vanish : ∀ j, q < j → motive j 0)
    (j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j) : motive j x := by
  by_cases hj : j ≤ q
  · obtain ⟨p, hp, rfl⟩ : ∃ p, p ≤ q ∧ j = q - p := ⟨q - j, Nat.sub_le q j, by omega⟩
    obtain ⟨y, rfl⟩ := (G.incidenceTorExteriorEquiv hp).surjective x
    exact tor p hp y
  · rw [G.exteriorBundleCohomology_eq_zero_of_lt ℂ (by omega : q < j) x]
    exact vanish j (by omega)

/-- **Induction on pairs of exterior classes through Tor.** A property of pairs of classes of the
`q`-th and `q'`-th exterior bundles over `ℂ` holds once it holds for pairs of images of Tor
classes and for pairs in which one class is zero in a degree above its exterior degree. -/
@[elab_as_elim]
theorem exteriorCohomology_induction₂_on_tor {G : Multigraph V E} {q q' : ℕ}
    {motive : (i j : ℕ) → Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) i →
      Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q') j → Prop}
    (tor : ∀ (p p' : ℕ) (hp : p ≤ q) (hp' : p' ≤ q') (y : G.incidenceTorInternalPiece p q)
      (y' : G.incidenceTorInternalPiece p' q'),
      motive (q - p) (q' - p') (G.incidenceTorExteriorEquiv hp y) (G.incidenceTorExteriorEquiv hp' y'))
    (vanish_left : ∀ i j (x' : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q') j), q < i → motive i j 0 x')
    (vanish_right : ∀ i j (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) i), q' < j → motive i j x 0)
    (i j : ℕ) (x : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) i)
    (x' : Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q') j) : motive i j x x' := by
  induction i, x using exteriorCohomology_induction_on_tor with
  | tor p hp y =>
    induction j, x' using exteriorCohomology_induction_on_tor with
    | tor p' hp' y' => exact tor p p' hp hp' y y'
    | vanish j hj => exact vanish_right _ j _ hj
  | vanish i hi => exact vanish_left i j x' hi

/-- **Extensionality through Tor.** Two families, indexed by the cohomological degree, of additive
maps out of the actual cohomology of the `q`-th exterior bundle over `ℂ` agree in every degree once
they agree on the image of every Tor class of bidegree `(p, q)` with `p ≤ q`. -/
theorem exteriorCohomology_ext_via_tor {G : Multigraph V E} {q : ℕ} {A : ℕ → Type*}
    [∀ j, AddZeroClass (A j)] {f g : ∀ j, Sheaf.H.{1} (G.exteriorBundleAbelian ℂ q) j →+ A j}
    (h : ∀ (p : ℕ) (hp : p ≤ q) (y : G.incidenceTorInternalPiece p q),
      f (q - p) (G.incidenceTorExteriorEquiv hp y) = g (q - p) (G.incidenceTorExteriorEquiv hp y))
    (j : ℕ) : f j = g j := by
  ext x
  induction j, x using exteriorCohomology_induction_on_tor with
  | tor p hp y => exact h p hp y
  | vanish j _ => rw [map_zero, map_zero]

end
end BPFixedPoints.Multigraph
