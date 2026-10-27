import BPFixedPoints.Incidence.BinaryCoverCellAvailability
import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # The original cubical cell presheaf complex is positively exact

At W the terms use exactly the original cells whose original face opens
contain W, and exactly their original overlap dimensions. Restrictions are
the original inclusions of these cell bases. The original boundary is fixed
globally; local choices enter only the exactness proof through its prism.
-/

namespace BPFixedPoints.SheafTools.BinaryCells
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Finsupp
open CechCubicalCell ResolutionTools
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable {T : Type} [TopologicalSpace T] {V : Type} [Fintype V] [DecidableEq V]
variable (U : V → Fin 2 → Opens T) (R : Type*) [CommRing R]

/-- Original available cells in their original degree on W. -/
noncomputable abbrev chains (W : Opens T) (n : ℕ) : Submodule R (Cells R V) :=
  available U W R ⊓ supported R R {q | cellDegree q = -(n : ℤ)}

@[reducible] noncomputable local instance chainsAddCommGroup (W : Opens T) (n : ℕ) :
    AddCommGroup (chains U R W n) := (chains U R W n).addCommGroup
@[reducible] noncomputable local instance chainsModule (W : Opens T) (n : ℕ) :
    Module R (chains U R W n) := (chains U R W n).module

/-- The original boundary with one globally fixed base vertex; its value is independent of that choice. -/
noncomputable def differential (W : Opens T) (n : ℕ) : chains U R W (n+1) →ₗ[R] chains U R W n :=
  ((CechCubicalCell.contraction R (fun _ : V => 0)).d.comp (chains U R W (n+1)).subtype).codRestrict _
    fun x => by
      constructor
      · exact available_boundary U W R (fun _ => 0) x.val x.property.1
      · change (CechCubicalCell.contraction R (fun _ : V => 0)).d x.val ∈
          supported R R {q | cellDegree q = -(n : ℤ)}
        have he : -((n+1 : ℕ) : ℤ)+1 = -(n : ℤ) := by omega
        simpa only [he] using (contraction_degrees R (fun _ : V => 0)).d
          (-((n+1 : ℕ) : ℤ)) x.val x.property.2

/-- The original available-cell boundary squares to zero. -/
theorem differential_square (W : Opens T) (n : ℕ) :
    (differential U R W n).comp (differential U R W (n+1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (CechCubicalCell.contraction R (fun _ : V => 0)).d_sq x.val

/-- Exactness is supplied on every actual open, including opens contained in no original chart. -/
theorem differential_range_eq_ker (W : Opens T) (n : ℕ) :
    LinearMap.range (differential U R W (n+1)) = LinearMap.ker (differential U R W n) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (differential_square U R W n) y
  · intro hx
    have hd : (CechCubicalCell.contraction R (fun _ : V => 0)).d x.val = 0 := congrArg Subtype.val hx
    obtain ⟨z,hz,hg,he⟩ := available_positive_primitive U W R (n+1) (by omega)
      x.val x.property.1 x.property.2 hd
    exact ⟨⟨z,hz,hg⟩,Subtype.ext he⟩

/-- The actual original chain complex on an open. -/
noncomputable def openComplex (W : Opens T) : ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => chains U R W n) (differential U R W) (differential_square U R W)

/-- Actual local positive exactness of the original available-cell complex. -/
theorem openComplex_exact (W : Opens T) (n : ℕ) : (openComplex U R W).ExactAt (n+1) :=
  linearChainComplex_exactAt_succ _ _ _ (differential_range_eq_ker U R W) n

/-- Restricting the actual open retains every originally available cell. -/
theorem chains_mono {W Z : Opens T} (h : Z ≤ W) (n : ℕ) : chains U R W n ≤ chains U R Z n := by
  intro x hx
  refine ⟨?_,hx.2⟩
  intro q hq
  exact h.trans (hx.1 hq)

/-- The original cell presheaf: restriction includes the same cells with the same coefficients. -/
noncomputable def presheaf (n : ℕ) : (Opens T)ᵒᵖ ⥤ ModuleCat R where
  obj W := ModuleCat.of R (chains U R W.unop n)
  map f := ModuleCat.ofHom (Submodule.inclusion (chains_mono U R (leOfHom f.unop) n))
  map_id W := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The original cell boundary commutes with each original open restriction. -/
noncomputable def presheafDifferential (n : ℕ) : presheaf U R (n+1) ⟶ presheaf U R n where
  app W := ModuleCat.ofHom (differential U R W.unop n)
  naturality {W Z} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact Subtype.ext rfl

/-- The original presheaf boundary squares to zero on every actual open. -/
theorem presheafDifferential_square (n : ℕ) :
    presheafDifferential U R (n+1) ≫ presheafDifferential U R n = 0 := by
  apply NatTrans.ext
  funext W
  exact ModuleCat.hom_ext (differential_square U R W.unop n)

/-- The actual original cubical cell presheaf chain complex. -/
noncomputable def presheafComplex : ChainComplex ((Opens T)ᵒᵖ ⥤ ModuleCat R) ℕ :=
  ChainComplex.of (presheaf U R) (presheafDifferential U R) (presheafDifferential_square U R)

/-- Positive exactness of the original cubical cell presheaf complex, by its actual open evaluations. -/
theorem presheafComplex_exact (n : ℕ) : (presheafComplex U R).ExactAt (n+1) := by
  let S := ShortComplex.mk (presheafDifferential U R (n+1)) (presheafDifferential U R n)
    (presheafDifferential_square U R n)
  have hs : S.Exact := by
    rw [ShortComplex.exact_iff_isZero_homology,IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext W
    let E := (evaluation (Opens T)ᵒᵖ (ModuleCat R)).obj W
    have hW : (S.map E).Exact := by
      apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      exact differential_range_eq_ker U R W.unop n
    exact (IsZero.of_iso ((ShortComplex.exact_iff_isZero_homology _).mp hW)
      (S.mapHomologyIso E).symm).eq_of_src _ _
  rw [HomologicalComplex.exactAt_iff' _ (n+2) (n+1) n (by simp) (by simp)]
  change (ShortComplex.mk ((presheafComplex U R).d (n+2) (n+1))
    ((presheafComplex U R).d (n+1) n) _).Exact
  dsimp only [presheafComplex]
  have hd₁ : ChainComplex.of.d (presheaf U R) (presheafDifferential U R) (n+2) (n+1) =
      presheafDifferential U R (n+1) := ChainComplex.of_d _ _ (n+1)
  simpa only [hd₁,ChainComplex.of_d] using hs

/-- Original available chains vanish above the actual number of original binary directions. -/
theorem chains_zero_above (W : Opens T) (n : ℕ) (hn : Fintype.card V < n) (x : chains U R W n) : x = 0 := by
  apply Subtype.ext
  apply Finsupp.ext
  intro q
  exact (mem_supported' R _).mp x.property.2 q (by
    change -(CechProduct.faceDegree q : ℤ) ≠ -(n : ℤ)
    have hq := faceDegree_le_card q
    omega)

/-- The actual original presheaf cell complex is bounded by the original number of directions. -/
theorem presheafComplex_isZero_above (n : ℕ) (hn : Fintype.card V < n) :
    IsZero ((presheafComplex U R).X n) := by
  change IsZero (presheaf U R n)
  rw [IsZero.iff_id_eq_zero]
  apply NatTrans.ext
  funext W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact chains_zero_above U R W.unop n hn x

end BPFixedPoints.SheafTools.BinaryCells
