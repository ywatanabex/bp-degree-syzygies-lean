import BPFixedPoints.Incidence.CechTwoMiddleProjection

/-! # Original full degree-one cohomology and its original contraction -/

namespace BPFixedPoints.CechProduct
open Finsupp
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
variable (R : Type) [CommRing R]

@[reducible] noncomputable local instance middleCyclesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (twoMiddleCycles R d) := (twoMiddleCycles R d).addCommGroup

/-- Original degree-zero chains, without a closedness assumption on primitives. -/
abbrev twoZeroChains : Submodule R (C R (Fin 2)) :=
  supported R R {b | (cechDegree b : ℤ) = 0}

@[reducible] noncomputable local instance zeroChainsAddCommGroup :
    AddCommGroup (twoZeroChains R) := (twoZeroChains R).addCommGroup

@[reducible] noncomputable local instance middleStatesAddCommGroup (d : Fin 2 → ℕ) :
    AddCommGroup (twoMiddleStatePiece R d) := (twoMiddleStatePiece R d).addCommGroup

@[reducible] noncomputable local instance zeroChainsModule :
    Module R (twoZeroChains R) := (twoZeroChains R).module

@[reducible] noncomputable local instance middleCyclesModule (d : Fin 2 → ℕ) :
    Module R (twoMiddleCycles R d) := (twoMiddleCycles R d).module

@[reducible] noncomputable local instance middleStatesModule (d : Fin 2 → ℕ) :
    Module R (twoMiddleStatePiece R d) := (twoMiddleStatePiece R d).module

/-- The original differential from original degree-zero chains into original middle cocycles. -/
noncomputable def twoMiddleBoundary (d : Fin 2 → ℕ) : twoZeroChains R →ₗ[R] twoMiddleCycles R d :=
  ((contraction R d).d.comp (twoZeroChains R).subtype).codRestrict _ fun x => by
    constructor
    · change (contraction R d).d x.val ∈ supported R R {b | (cechDegree b : ℤ) = 1}
      simpa only [zero_add] using contraction_d_degree R d 0 x.val x.property
    · exact LinearMap.congr_fun (contraction R d).d_sq x.val

/-- The original full inclusion supplies original degree-one cocycle representatives. -/
noncomputable def twoMiddleInclusion (d : Fin 2 → ℕ) :
    twoMiddleStatePiece R d →ₗ[R] twoMiddleCycles R d :=
  ((contraction R d).i.comp (twoMiddleStatePiece R d).subtype).codRestrict _ fun s => by
    constructor
    · change (contraction R d).i s.val ∈ supported R R {b | (cechDegree b : ℤ) = 1}
      simpa only [add_zero] using contraction_i_degree R d 1 s.val s.property
    · exact LinearMap.congr_fun (contraction R d).d_i s.val

/-- The specified projection and inclusion retain the original full contraction identity. -/
theorem twoMiddleStateProjection_inclusion (d : Fin 2 → ℕ) (s : twoMiddleStatePiece R d) :
    twoMiddleStateProjection R d (twoMiddleInclusion R d s) = s := by
  apply Subtype.ext
  exact LinearMap.congr_fun (contraction R d).p_i s.val

/-- The original full state projection is onto the original degree-one state piece. -/
theorem twoMiddleStateProjection_surjective (d : Fin 2 → ℕ) :
    Function.Surjective (twoMiddleStateProjection R d) :=
  fun s => ⟨twoMiddleInclusion R d s,twoMiddleStateProjection_inclusion R d s⟩

/-- Original degree-zero boundaries are exactly the kernel of the original full middle projection. -/
theorem twoMiddleBoundary_range (d : Fin 2 → ℕ) :
    LinearMap.range (twoMiddleBoundary R d) = LinearMap.ker (twoMiddleStateProjection R d) := by
  ext c
  constructor
  · rintro ⟨x,rfl⟩
    apply Subtype.ext
    exact LinearMap.congr_fun (contraction R d).p_d x.val
  · intro hc
    have hp : (contraction R d).p c.val = 0 := congrArg Subtype.val hc
    have hh : (contraction R d).h c.val ∈ twoZeroChains R := by
      simpa only [add_neg_cancel] using contraction_h_degree R d 1 c.val c.property.1
    refine ⟨⟨(contraction R d).h c.val,hh⟩,?_⟩
    apply Subtype.ext
    change (contraction R d).d ((contraction R d).h c.val) = c.val
    have he := GradedContraction.ChainPairing.cycle_decomposition (a := contraction R d) c.property.2
    simpa only [hp,map_zero,add_zero] using he.symm

attribute [local irreducible] contraction twoMiddleBoundary twoMiddleCycles
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.respectTransparency.instanceSearchTypes true

/-- Degree-one cohomology of the original full coefficient complex, using its original degree-zero boundaries. -/
noncomputable abbrev twoMiddleCohomology (d : Fin 2 → ℕ) : Type :=
  (twoMiddleCycles R d) ⧸ LinearMap.range (twoMiddleBoundary R d)

/-- Original cohomology is computed by the specified original full contraction, over every commutative base ring. -/
noncomputable def twoMiddleCohomologyStateEquiv (d : Fin 2 → ℕ) :
    twoMiddleCohomology R d ≃ₗ[R] twoMiddleStatePiece R d :=
  quotientEquivOfExact R (A := twoZeroChains R) (B := twoMiddleCycles R d)
    (D := twoMiddleStatePiece R d) (twoMiddleBoundary R d) (twoMiddleStateProjection R d)
    (twoMiddleBoundary_range R d) (twoMiddleStateProjection_surjective R d)

/-- Each original cocycle class has its original full state projection. -/
theorem twoMiddleCohomologyStateEquiv_mk (d : Fin 2 → ℕ) (c : twoMiddleCycles R d) :
    twoMiddleCohomologyStateEquiv R d (Submodule.Quotient.mk c) = twoMiddleStateProjection R d c := rfl

end BPFixedPoints.CechProduct
