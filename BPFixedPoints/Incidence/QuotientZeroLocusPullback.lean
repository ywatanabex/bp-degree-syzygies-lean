import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Base change of genuine quotient zero schemes

Equality of extended ideals gives the pushout of quotient rings and therefore
an actual pullback square of affine schemes. The quotient morphism may be any
map satisfying the original commutative square.
-/

namespace BPFixedPoints.SchemeTools
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false

/-- The actual quotient square is a pushout whenever its target ideal is the
extension of the source ideal. -/
theorem quotientSquare_isPushout (R B : CommRingCat.{0}) (f : R ⟶ B)
    (I : Ideal R) (J : Ideal B) (hJ : J = I.map f.hom)
    (g : CommRingCat.of (R ⧸ I) ⟶ CommRingCat.of (B ⧸ J))
    (hg : f ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ g) :
    IsPushout f (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk J)) g where
  w := hg
  isColimit' := ⟨PushoutCocone.isColimitAux' _ fun s => by
    have hk : J ≤ RingHom.ker s.inl.hom := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro p hp
      have he := congrArg (fun a : R ⟶ s.pt => a.hom p) s.condition
      change s.inl.hom (f.hom p) = s.inr.hom (Ideal.Quotient.mk I p) at he
      change s.inl.hom (f.hom p) = 0
      exact he.trans (by rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero])
    let d : CommRingCat.of (B ⧸ J) ⟶ s.pt :=
      CommRingCat.ofHom (Ideal.Quotient.lift J s.inl.hom hk)
    refine ⟨d, ?_, ?_, ?_⟩
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro b
      rfl
    · apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
      have he := congrArg (fun a : R ⟶ CommRingCat.of (B ⧸ J) => a.hom p) hg
      change Ideal.Quotient.mk J (f.hom p) = g.hom (Ideal.Quotient.mk I p) at he
      change d.hom (g.hom (Ideal.Quotient.mk I p)) = s.inr.hom (Ideal.Quotient.mk I p)
      rw [← he]
      exact congrArg (fun a : R ⟶ s.pt => a.hom p) s.condition
    · intro d' hleft _
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro z
      obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact congrArg (fun a : B ⟶ s.pt => a.hom b) hleft⟩

/-- Pulling back an actual affine zero scheme gives the quotient by the extended ideal. -/
theorem quotientSquare_isPullback (R B : CommRingCat.{0}) (f : R ⟶ B)
    (I : Ideal R) (J : Ideal B) (hJ : J = I.map f.hom)
    (g : CommRingCat.of (R ⧸ I) ⟶ CommRingCat.of (B ⧸ J))
    (hg : f ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ g) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) (Spec.map g)
      (Spec.map f) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (quotientSquare_isPushout R B f I J hJ g hg)

end BPFixedPoints.SchemeTools
