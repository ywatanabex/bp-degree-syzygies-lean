import BPFixedPoints.Incidence.CechCubicalCellSubface
import BPFixedPoints.Incidence.ResolutionTools

/-! # The exact original face-supported cell chain complex

The chain terms retain the original subfaces and original overlap dimensions.
The boundary is the original tensor boundary, and every positive primitive is
the specified face-preserving tensor prism. No cohomology or exactness input
is assumed for this local cell complex.
-/

namespace BPFixedPoints.CechCubicalCell
open Finsupp CechProduct ResolutionTools CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1500000
variable (R : Type*) [CommRing R] {V : Type} [Fintype V] [DecidableEq V]

/-- Original face-supported chains of original overlap dimension `n`. -/
noncomputable abbrev faceChains (p : V → Fin 3) (n : ℕ) : Submodule R (Cells R V) :=
  subfaces R p ⊓ supported R R {q | cellDegree q = -(n : ℤ)}

@[reducible] noncomputable local instance faceChainsAddCommGroup (p : V → Fin 3) (n : ℕ) :
    AddCommGroup (faceChains R p n) := (faceChains R p n).addCommGroup
@[reducible] noncomputable local instance faceChainsModule (p : V → Fin 3) (n : ℕ) :
    Module R (faceChains R p n) := (faceChains R p n).module

/-- The original boundary restricted to its actual original source and target degrees. -/
noncomputable def faceDifferential (b : V → Fin 2) (p : V → Fin 3) (n : ℕ) :
    faceChains R p (n+1) →ₗ[R] faceChains R p n :=
  (((contraction R b).d).comp (faceChains R p (n+1)).subtype).codRestrict _ fun x => by
    constructor
    · exact contraction_d_subfaces R b p x.val x.property.1
    · have he : -((n+1 : ℕ) : ℤ)+1 = -(n : ℤ) := by omega
      change (contraction R b).d x.val ∈ supported R R {q | cellDegree q = -(n : ℤ)}
      simpa only [he] using (contraction_degrees R b).d (-((n+1 : ℕ) : ℤ)) x.val x.property.2

/-- The restricted boundary retains exactly the original full cell boundary. -/
theorem faceDifferential_val (b : V → Fin 2) (p : V → Fin 3) (n : ℕ)
    (x : faceChains R p (n+1)) :
    (faceDifferential R b p n x).val = (contraction R b).d x.val := rfl

/-- The original restricted cell differentials square to zero. -/
theorem faceDifferential_square (b : V → Fin 2) (p : V → Fin 3) (n : ℕ) :
    (faceDifferential R b p n).comp (faceDifferential R b p (n+1)) = 0 := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact LinearMap.congr_fun (contraction R b).d_sq x.val

/-- The original prism restricted to its actual next overlap dimension and original face. -/
noncomputable def facePrism (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (n : ℕ) :
    faceChains R p n →ₗ[R] faceChains R p (n+1) :=
  (((contraction R b).h).comp (faceChains R p n).subtype).codRestrict _ fun x => by
    constructor
    · exact contraction_h_subfaces R b p hb x.val x.property.1
    · have he : -(n : ℤ)+(-1) = -((n+1 : ℕ) : ℤ) := by omega
      change (contraction R b).h x.val ∈ supported R R {q | cellDegree q = -((n+1 : ℕ) : ℤ)}
      simpa only [he] using (contraction_degrees R b).h (-(n : ℤ)) x.val x.property.2

/-- Every original positive cycle is the original boundary of its specified original prism. -/
theorem faceDifferential_prism_of_closed (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (n : ℕ)
    (x : faceChains R p (n+1)) (hx : faceDifferential R b p n x = 0) :
    faceDifferential R b p (n+1) (facePrism R b p hb (n+1) x) = x := by
  apply Subtype.ext
  have hd : (contraction R b).d x.val = 0 := congrArg Subtype.val hx
  exact (contraction_positive_primitive R b (n+1) (by omega) x.val x.property.2 hd).2

/-- The original boundary image equals the original boundary kernel in every positive degree. -/
theorem faceDifferential_range_eq_ker (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (n : ℕ) :
    LinearMap.range (faceDifferential R b p (n+1)) = LinearMap.ker (faceDifferential R b p n) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (faceDifferential_square R b p n) y
  · intro hx
    exact ⟨facePrism R b p hb (n+1) x,faceDifferential_prism_of_closed R b p hb n x hx⟩

/-- The actual degreewise original cell chain complex. -/
noncomputable def faceChainComplex (b : V → Fin 2) (p : V → Fin 3) :
    ChainComplex (ModuleCat R) ℕ :=
  linearChainComplex (fun n => faceChains R p n) (faceDifferential R b p)
    (faceDifferential_square R b p)

/-- Positive exactness for the original cell complex inside every original face containing the base vertex. -/
theorem faceChainComplex_exact (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) (n : ℕ) :
    (faceChainComplex R b p).ExactAt (n+1) :=
  linearChainComplex_exactAt_succ _ _ _ (faceDifferential_range_eq_ker R b p hb) n

/-- In original dimension zero the boundary is zero, with no assumption on the base vertex. -/
theorem contraction_d_zero_degree (b : V → Fin 2) (x : Cells R V)
    (hx : x ∈ supported R R {q | cellDegree q = 0}) : (contraction R b).d x = 0 := by
  have hd := (contraction_degrees R b).d 0 x hx
  apply Finsupp.ext
  intro q
  exact (mem_supported' R _).mp hd q (by change -(faceDegree q : ℤ) ≠ 0+1; omega)

/-- The augmentation is the original sum of original degree-zero vertex coefficients. -/
noncomputable def faceAugmentation (b : V → Fin 2) (p : V → Fin 3) :
    faceChains R p 0 →ₗ[R] Components R V :=
  (contraction R b).p.comp (faceChains R p 0).subtype

/-- The actual original augmentation kills the actual original boundary. -/
theorem faceAugmentation_boundary (b : V → Fin 2) (p : V → Fin 3) :
    (faceAugmentation R b p).comp (faceDifferential R b p 0) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (contraction R b).p_d x.val

/-- The original augmentation kernel is precisely the original degree-one boundary image. -/
theorem faceAugmentation_range_eq_ker (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    LinearMap.range (faceDifferential R b p 0) = LinearMap.ker (faceAugmentation R b p) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact LinearMap.congr_fun (faceAugmentation_boundary R b p) y
  · intro hx
    refine ⟨facePrism R b p hb 0 x,?_⟩
    apply Subtype.ext
    change (contraction R b).d ((contraction R b).h x.val) = x.val
    have hd : (contraction R b).d x.val = 0 := contraction_d_zero_degree R b x.val x.property.2
    have hp : (contraction R b).p x.val = 0 := hx
    have he := LinearMap.congr_fun (contraction R b).homotopy x.val
    simpa only [Module.End.mul_apply,LinearMap.add_apply,LinearMap.comp_apply,
      Module.End.one_apply,hd,hp,map_zero,add_zero] using he

/-- The original component inclusion is a section of the augmentation inside the same original face. -/
noncomputable def faceAugmentationSection (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    Components R V →ₗ[R] faceChains R p 0 :=
  (contraction R b).i.codRestrict _ fun y => by
    constructor
    · exact contraction_i_subfaces R b p hb y
    · have hy : y ∈ supported R R {q : V → Fin 1 | (0 : ℤ) = 0} := fun _ _ => rfl
      change (contraction R b).i y ∈ supported R R {q | cellDegree q = -(0 : ℤ)}
      simpa only [zero_add,Nat.cast_zero,neg_zero] using (contraction_degrees R b).i 0 y hy

/-- The original augmentation and its original basepoint section compose to the identity. -/
theorem faceAugmentation_section (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    (faceAugmentation R b p).comp (faceAugmentationSection R b p hb) = LinearMap.id := by
  apply LinearMap.ext
  intro y
  exact LinearMap.congr_fun (contraction R b).p_i y

/-- The original augmentation is actually onto its original component, for every original face. -/
theorem faceAugmentation_surjective (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    Function.Surjective (faceAugmentation R b p) := by
  intro y
  exact ⟨faceAugmentationSection R b p hb y,LinearMap.congr_fun (faceAugmentation_section R b p hb) y⟩

/-- The actual original chain differential is killed by the actual original augmentation. -/
theorem faceAugmentation_zero (b : V → Fin 2) (p : V → Fin 3) :
    (faceChainComplex R b p).d 1 0 ≫ ModuleCat.ofHom (faceAugmentation R b p) = 0 := by
  dsimp only [faceChainComplex]
  rw [linearChainComplex_d]
  exact ModuleCat.hom_ext (faceAugmentation_boundary R b p)

/-- Native augmented exactness, retaining the original degree-zero target and original maps. -/
theorem faceChainComplex_augmented_exact (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    (ShortComplex.mk ((faceChainComplex R b p).d 1 0)
      (ModuleCat.ofHom (faceAugmentation R b p)) (faceAugmentation_zero R b p)).Exact := by
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  change LinearMap.range ((faceChainComplex R b p).d 1 0).hom = LinearMap.ker (faceAugmentation R b p)
  dsimp only [faceChainComplex]
  rw [linearChainComplex_d]
  exact faceAugmentation_range_eq_ker R b p hb

/-- Native augmented epimorphism, supplied by the original basepoint section. -/
theorem faceAugmentation_epi (b : V → Fin 2) (p : V → Fin 3)
    (hb : FaceRefines (fun v => (b v).castSucc) p) :
    Epi (ModuleCat.ofHom (faceAugmentation R b p)) :=
  (ModuleCat.epi_iff_surjective _).mpr (faceAugmentation_surjective R b p hb)

end BPFixedPoints.CechCubicalCell
