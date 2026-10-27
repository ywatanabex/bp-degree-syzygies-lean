import BPFixedPoints.Incidence.SchemeModuleTensorSections

/-! # Finite iterated tensors of actual scheme-module sheaves

Every binary tensor is the original pointwise module tensor followed by
native sheafification. The empty tensor is the actual structure module.
Functoriality retains the original factor maps, including empty families.
-/

namespace BPFixedPoints.SheafTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable (X : Scheme.{0})

/-- Original factor isomorphisms induce an actual tensor-sheaf isomorphism. -/
noncomputable def moduleTensorIso {M₁ M₂ N₁ N₂ : X.Modules} (f : M₁ ≅ M₂) (g : N₁ ≅ N₂) :
    moduleTensor X M₁ N₁ ≅ moduleTensor X M₂ N₂ where
  hom := moduleTensorMap X f.hom g.hom
  inv := moduleTensorMap X f.inv g.inv
  hom_inv_id := by rw [← moduleTensorMap_comp, f.hom_inv_id, g.hom_inv_id, moduleTensorMap_id]
  inv_hom_id := by rw [← moduleTensorMap_comp, f.inv_hom_id, g.inv_hom_id, moduleTensorMap_id]

/-- Actual ordered finite tensor of the specified original sheaf modules. -/
noncomputable def moduleTensorFamily : (n : ℕ) → (Fin n → X.Modules) → X.Modules
  | 0, _ => SheafOfModules.unit X.ringCatSheaf
  | n+1, M => moduleTensor X (M 0) (moduleTensorFamily n (fun i => M i.succ))

/-- Original factor maps induce a map of the actual finite tensor sheaves. -/
noncomputable def moduleTensorFamilyMap : (n : ℕ) → (M N : Fin n → X.Modules) →
    (∀ i, M i ⟶ N i) → (moduleTensorFamily X n M ⟶ moduleTensorFamily X n N)
  | 0, _, _, _ => 𝟙 _
  | n+1, M, N, f => moduleTensorMap X (f 0)
      (moduleTensorFamilyMap n (fun i => M i.succ) (fun i => N i.succ) (fun i => f i.succ))

/-- Identity maps remain the original identity on every actual finite tensor. -/
theorem moduleTensorFamilyMap_id (n : ℕ) : ∀ (M : Fin n → X.Modules),
    moduleTensorFamilyMap X n M M (fun i => 𝟙 (M i)) = 𝟙 _ := by
  induction n with
  | zero => intro M; rfl
  | succ n ih =>
      intro M
      dsimp only [moduleTensorFamilyMap]
      rw [ih, moduleTensorMap_id]
      rfl

/-- Original factorwise compositions remain the actual composition on every finite tensor. -/
theorem moduleTensorFamilyMap_comp (n : ℕ) : ∀ (M N P : Fin n → X.Modules)
    (f : ∀ i, M i ⟶ N i) (g : ∀ i, N i ⟶ P i),
    moduleTensorFamilyMap X n M P (fun i => f i ≫ g i) =
      moduleTensorFamilyMap X n M N f ≫ moduleTensorFamilyMap X n N P g := by
  induction n with
  | zero => intro M N P f g; simp only [moduleTensorFamilyMap, Category.id_comp]; rfl
  | succ n ih =>
      intro M N P f g
      dsimp only [moduleTensorFamilyMap]
      rw [ih, moduleTensorMap_comp]

/-- Original factorwise isomorphisms give an actual finite tensor-sheaf isomorphism. -/
noncomputable def moduleTensorFamilyIso (n : ℕ) (M N : Fin n → X.Modules) (e : ∀ i, M i ≅ N i) :
    moduleTensorFamily X n M ≅ moduleTensorFamily X n N where
  hom := moduleTensorFamilyMap X n M N (fun i => (e i).hom)
  inv := moduleTensorFamilyMap X n N M (fun i => (e i).inv)
  hom_inv_id := by
    rw [← moduleTensorFamilyMap_comp]
    simpa only [Iso.hom_inv_id] using moduleTensorFamilyMap_id X n M
  inv_hom_id := by
    rw [← moduleTensorFamilyMap_comp]
    simpa only [Iso.inv_hom_id] using moduleTensorFamilyMap_id X n N

/-- A zero-length family has the original structure module as its actual tensor. -/
theorem moduleTensorFamily_eq_unit_of_zero {n : ℕ} (hn : n = 0) (M : Fin n → X.Modules) :
    moduleTensorFamily X n M = SheafOfModules.unit X.ringCatSheaf := by
  cases hn
  rfl

/-- A singleton actual tensor is the original sheaf via the native right unit comparison. -/
noncomputable def moduleTensorFamilySingletonIso (M : Fin 1 → X.Modules) :
    moduleTensorFamily X 1 M ≅ M 0 :=
  moduleTensorRightUnitIso X (M 0)

/-- Every finite tensor of original structure modules is the original structure module. -/
noncomputable def moduleTensorFamilyUnitIso : (n : ℕ) →
    moduleTensorFamily X n (fun _ => SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf
  | 0 => Iso.refl _
  | n+1 => moduleTensorLeftUnitIso X _ ≪≫ moduleTensorFamilyUnitIso n

end BPFixedPoints.SheafTools
