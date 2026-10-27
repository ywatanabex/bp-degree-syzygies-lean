import BPFixedPoints.Incidence.VertexProjectiveTwistAbelianLinearity
import BPFixedPoints.Incidence.BinaryCoverCellSheafCup

/-! # Actual twist cup cochains on the original vertex cell resolution

Evaluate the original geometric section product on the original actual
cell diagonal. This retains native Leibniz signs and the independently
specified geometric coefficient action, before the comparison with the
coefficient cup or with the canonical derived Ext cup.
-/

namespace BPFixedPoints.ProjectiveLine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite SheafTools
open SheafTools.AbelianTensor SheafTools.BinaryCells SchemeTools
open scoped BPFixedPoints.SheafTools.AbelianTensor
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
noncomputable section
variable (R : Type) [CommRing R] (V : Type) [Fintype V] [DecidableEq V]

/-- The original actual cell complex for the original vertex binary charts. -/
abbrev vertexTwistCupSource := sheafComplex (vertexCoordinateOpen R V)

/-- The original geometric twist product evaluated on the original actual cubical cell diagonal. -/
def vertexTwistCellCupAt (a b : V → ℤ) (n i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) :
    (vertexTwistCupSource R V).X n ⟶ vertexTwistAbelianSheaf R V (a+b) :=
  actualCellCupAt (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j f g

/-- The actual geometric cup on the original cell cochains has the original sum degree. -/
def vertexTwistCellCup (a b : V → ℤ) (i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) :
    (vertexTwistCupSource R V).X (i+j) ⟶ vertexTwistAbelianSheaf R V (a+b) :=
  vertexTwistCellCupAt R V a b (i+j) i j f g

/-- The actual geometric cup on the original cell cochains retains the original signed Leibniz differential. -/
theorem vertexTwistCellCupAt_boundary (a b : V → ℤ) (n i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) :
    (vertexTwistCupSource R V).d (n+1) n ≫ vertexTwistCellCupAt R V a b n i j f g =
      vertexTwistCellCupAt R V a b (n+1) (i+1) j ((vertexTwistCupSource R V).d (i+1) i ≫ f) g +
        ((-1 : ℤˣ)^i) • vertexTwistCellCupAt R V a b (n+1) i (j+1) f ((vertexTwistCupSource R V).d (j+1) j ≫ g) :=
  actualCellCupAt_boundary _ _ n i j f g

/-- Closed original twist cochains have a closed actual geometric cup. -/
theorem vertexTwistCellCupAt_closed (a b : V → ℤ) (n i j : ℕ)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b)
    (hf : (vertexTwistCupSource R V).d (i+1) i ≫ f = 0)
    (hg : (vertexTwistCupSource R V).d (j+1) j ≫ g = 0) :
    (vertexTwistCupSource R V).d (n+1) n ≫ vertexTwistCellCupAt R V a b n i j f g = 0 :=
  actualCellCupAt_closed _ _ n i j f g hf hg

/-- The actual cell cup retains the independently specified original left geometric scalar endomorphism. -/
theorem vertexTwistCellCupAt_left_scalar (a b : V → ℤ) (n i j : ℕ) (r : R)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) :
    vertexTwistCellCupAt R V a b n i j
      (f ≫ schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r) g =
        vertexTwistCellCupAt R V a b n i j f g ≫
          schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r := by
  have e : (f ≫ schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r) ⊗ₘ g =
      (f ⊗ₘ g) ≫ (schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V a) r ⊗ₘ
        𝟙 (vertexTwistAbelianSheaf R V b)) := by
    rw [tensorHom_comp_tensorHom,Category.comp_id]
  change (actualTensorDiagonalMap (vertexCoordinateOpen R V)).f n ≫
    actualTensorProjection (vertexCoordinateOpen R V) n i j ≫ _ ≫ vertexTwistAbelianProduct R V a b = _
  rw [e]
  simp only [Category.assoc]
  rw [vertexTwistAbelianProduct_left_scalar]
  rfl

/-- The actual cell cup retains the independently specified original right geometric scalar endomorphism. -/
theorem vertexTwistCellCupAt_right_scalar (a b : V → ℤ) (n i j : ℕ) (r : R)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) :
    vertexTwistCellCupAt R V a b n i j f
      (g ≫ schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) =
        vertexTwistCellCupAt R V a b n i j f g ≫
          schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V (a+b)) r := by
  have e : f ⊗ₘ (g ≫ schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) =
      (f ⊗ₘ g) ≫ (𝟙 (vertexTwistAbelianSheaf R V a) ⊗ₘ
        schemeBaseAbelianScalar (vertexToBase R V) (vertexTwistSheaf R V b) r) := by
    rw [tensorHom_comp_tensorHom,Category.comp_id]
  change (actualTensorDiagonalMap (vertexCoordinateOpen R V)).f n ≫
    actualTensorProjection (vertexCoordinateOpen R V) n i j ≫ _ ≫ vertexTwistAbelianProduct R V a b = _
  rw [e]
  simp only [Category.assoc]
  rw [vertexTwistAbelianProduct_right_scalar]
  rfl

/-- The native tensor bidegree evaluates to the original mixed-face coefficient product. -/
theorem vertexTwistTensorCochain_face (a b : V → ℤ) (n i j : ℕ) (h : i+j=n)
    (f : (vertexTwistCupSource R V).X i ⟶ vertexTwistAbelianSheaf R V a)
    (g : (vertexTwistCupSource R V).X j ⟶ vertexTwistAbelianSheaf R V b) (q : V → Fin 3)
    (x : ((vertexTwistCupSource R V).X i).obj.obj (op (binaryCoverFaceOpen (vertexCoordinateOpen R V) q)))
    (y : ((vertexTwistCupSource R V).X j).obj.obj (op (binaryCoverFaceOpen (vertexCoordinateOpen R V) q))) :
    vertexTwistSheafFaceSectionsEquiv R V (a+b) q
      ((actualTensorInclusion (vertexCoordinateOpen R V) i j n h ≫
        actualTensorCochain (vertexCoordinateOpen R V) (vertexTwistAbelianSectionPairing R V a b) n i j f g).hom.app _
          (sheafPureSection _ _ _ x y)) =
      vertexTwistSheafFaceSectionsEquiv R V a q (f.hom.app _ x) *
        vertexTwistSheafFaceSectionsEquiv R V b q (g.hom.app _ y) := by
  rw [actualTensorCochain_pure]
  exact vertexTwistSectionProduct_face R V a b q _ _

end
end BPFixedPoints.ProjectiveLine
