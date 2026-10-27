import BPFixedPoints.Incidence.SheafFlasqueCohomology
import Mathlib.Topology.Sheaves.Functors

/-! # Vanishing on an actual open restriction implies ambient local Ext vanishing

The restriction is Mathlib's naive pullback by the original open embedding.
Its exactness follows from the native adjunctions and pullback comparison.
Native injective presentations, flasque vanishing and the long exact sequence
then transfer positive cohomology vanishing to the original local Ext groups.
-/

namespace BPFixedPoints.SheafTools
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

variable {X Y : TopCat.{0}} {f : X ⟶ Y} (hf : Topology.IsOpenEmbedding f)

/-- Native naive restriction along the original open embedding. -/
noncomputable abbrev openAbelianSheafRestriction :
    Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  hf.sheafPullback AddCommGrpCat.{0}

instance openAbelianSheafRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (openAbelianSheafRestriction hf) := by
  have := Topology.IsOpenEmbedding.functor_isContinuous hf
  dsimp only [openAbelianSheafRestriction, Topology.IsOpenEmbedding.sheafPullback]
  have : (hf.functor.sheafPushforwardContinuous AddCommGrpCat.{0}
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).IsRightAdjoint := inferInstance
  infer_instance

instance openAbelianSheafRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (openAbelianSheafRestriction hf) := by
  have : (TopCat.Sheaf.pullback AddCommGrpCat.{0} f).IsLeftAdjoint :=
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} f).isLeftAdjoint
  have : PreservesFiniteColimits (TopCat.Sheaf.pullback AddCommGrpCat.{0} f) := inferInstance
  exact preservesFiniteColimits_of_natIso (hf.sheafPullbackIso AddCommGrpCat.{0})

instance openAbelianSheafRestriction_additive : (openAbelianSheafRestriction hf).Additive := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (openAbelianSheafRestriction hf)
  exact Functor.additive_of_preservesBinaryBiproducts _

instance openAbelianSheafRestriction_preservesZeroMorphisms :
    (openAbelianSheafRestriction hf).PreservesZeroMorphisms where
  map_zero _ _ := by apply Sheaf.hom_ext; ext U; rfl

/-- Actual open restriction preserves native short exact sequences. -/
theorem openAbelianSheafRestriction_shortExact {S : ShortComplex (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})}
    (hS : S.ShortExact) : (S.map (openAbelianSheafRestriction hf)).ShortExact := by
  have := openAbelianSheafRestriction_preservesZeroMorphisms hf
  have := openAbelianSheafRestriction_preservesFiniteLimits hf
  have := openAbelianSheafRestriction_preservesFiniteColimits hf
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map _

/-- The actual naive open restriction of a flasque sheaf is flasque. -/
theorem openAbelianSheafRestriction_isFlasque (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})
    [TopCat.Sheaf.IsFlasque F] :
    TopCat.Sheaf.IsFlasque ((openAbelianSheafRestriction hf).obj F) where
  epi {_U _V} i := by
    change Epi (F.obj.map (hf.functor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi (F := F.obj) ((hf.functor.map i.unop).op)

noncomputable local instance openCohomologySourceHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _
noncomputable local instance openCohomologyTargetHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) := HasExt.standard _

/-- Local Ext vanishes when all positive genuine cohomology of the actual open restriction vanishes. -/
theorem openRestriction_local_cohomology_eq_zero (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})
      (hF : ∀ (k : ℕ) (x : Sheaf.H.{1} ((openAbelianSheafRestriction hf).obj F) (k+1)), x = 0)
      (x : F.H' (n+1) (hf.functor.obj ⊤)), x = 0 := by
  induction n with
  | zero =>
      intro F hF x
      have := openAbelianSheafRestriction_preservesZeroMorphisms hf
      let S := sheafInjectiveShortComplex F
      have hS := sheafInjectiveShortComplex_shortExact F
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
      let T := S.map (openAbelianSheafRestriction hf)
      have hT := openAbelianSheafRestriction_shortExact hf hS
      have hx : x.comp (Ext.mk₀ S.f) (add_zero 1) = 0 := Ext.eq_zero_of_injective _
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
        ((freeOpenAbelianSheaf (T := Y)).obj (hf.functor.obj ⊤)) hS x hx rfl
      let s := localSheafH0Equiv S.X₃ (hf.functor.obj ⊤) y
      obtain ⟨t, ht⟩ := Sheaf.H.longSequence_equiv₀_exact₃ hT isTerminalTop s
        (hF 0 _)
      change S.g.hom.app (op (hf.functor.obj ⊤)) t = s at ht
      let z := (localSheafH0Equiv S.X₂ (hf.functor.obj ⊤)).symm t
      have he : z.comp (Ext.mk₀ S.g) (add_zero 0) = y := by
        apply (localSheafH0Equiv S.X₃ (hf.functor.obj ⊤)).injective
        rw [localSheafH0Equiv_postcomp]
        simpa only [z, s, AddEquiv.apply_symm_apply] using ht
      have hy0 : y.comp hS.extClass rfl = 0 := by
        rw [← he]
        simp only [Ext.comp_assoc_of_second_deg_zero,
          ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]
      exact hy.symm.trans hy0
  | succ n ih =>
      intro F hF x
      have := openAbelianSheafRestriction_preservesZeroMorphisms hf
      let S := sheafInjectiveShortComplex F
      have hS := sheafInjectiveShortComplex_shortExact F
      have : Injective S.X₂ := inferInstanceAs (Injective (Injective.under F))
      have : TopCat.Sheaf.IsFlasque S.X₂ := injectiveSheaf_isFlasque (Injective.under F)
      let T := S.map (openAbelianSheafRestriction hf)
      have hT := openAbelianSheafRestriction_shortExact hf hS
      have : TopCat.Sheaf.IsFlasque T.X₂ := openAbelianSheafRestriction_isFlasque hf S.X₂
      have hQ (k : ℕ) (y : Sheaf.H.{1} T.X₃ (k+1)) : y = 0 := by
        obtain ⟨z, hz⟩ := Sheaf.H.longSequence_exact₃ hT y rfl (hF (k+1) _)
        have hz0 : z = 0 := flasque_global_cohomology_eq_zero T.X₂ k z
        rw [hz0, map_zero] at hz
        exact hz.symm
      have hx : x.comp (Ext.mk₀ S.f) (add_zero (n+1+1)) = 0 := Ext.eq_zero_of_injective _
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
        ((freeOpenAbelianSheaf (T := Y)).obj (hf.functor.obj ⊤)) hS x hx rfl
      have hy0 : y = 0 := ih S.X₃ hQ y
      rw [hy0, Ext.zero_comp] at hy
      exact hy.symm

end BPFixedPoints.SheafTools
