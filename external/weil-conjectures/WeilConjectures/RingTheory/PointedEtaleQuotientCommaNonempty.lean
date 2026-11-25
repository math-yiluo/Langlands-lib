/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PointedEtaleQuotientFunctor
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import WeilConjectures.RingTheory.EtaleAlgebraLift
import Mathlib.RingTheory.RingHom.Etale
import WeilConjectures.RingTheory.PointedEtaleQuotientPointBijective

/-! # Nonemptiness of pointed base-change comma categories

Source: Stacks Project, Tag 04D1; the pointed form of Tag 05WS.
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace Algebra

private theorem exists_etale_pushout {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) (hπ : Function.Surjective π) (T : CommAlgCat.{u} B)
    (hT : Etale B T) :
    ∃ S : CommAlgCat.{u} A, Etale A S ∧
      ∃ f : CommRingCat.of S ⟶ CommRingCat.of T,
        CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π)
          f (CommRingCat.ofHom (algebraMap B T)) := by
  classical
  let I := RingHom.ker π
  let eB := π.quotientKerEquivOfSurjective hπ
  let : Algebra (A ⧸ I) B := eB.toRingHom.toAlgebra
  let : Algebra (A ⧸ I) T :=
    ((algebraMap B T).comp eB.toRingHom).toAlgebra
  have : IsScalarTower (A ⧸ I) B T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Etale (A ⧸ I) B := (RingHom.etale_algebraMap).mp
    (RingHom.Etale.of_bijective eB.bijective)
  have := hT
  have : Etale (A ⧸ I) T := Etale.comp (A ⧸ I) B T
  obtain ⟨m, P, L, hS, _, e, he⟩ := exists_etale_coefficientLift I T
  let S := CommAlgCat.of A L.LiftRing
  let f : CommRingCat.of S ⟶ CommRingCat.of T := CommRingCat.ofHom L.reduction
  have hf (a : A) : L.reduction (algebraMap A L.LiftRing a) =
      algebraMap B T (π a) := by
    change L.reduction (Ideal.Quotient.mk L.liftIdeal (MvPolynomial.C a)) = _
    simp only [SquareJacobianPresentation.CoefficientLift.reduction,
      Ideal.Quotient.lift_mk, SquareJacobianPresentation.CoefficientLift.polynomialReduction,
      MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    rfl
  let s : PushoutCocone (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π) :=
    PushoutCocone.mk f (CommRingCat.ofHom (algebraMap B T)) (by
      ext a
      exact hf a)
  have hs : IsColimit s := PushoutCocone.isColimitAux' s fun t ↦ by
    let J := I.map (algebraMap A S)
    have hkill : J ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change t.inl.hom (algebraMap A S a) = 0
      have hp : π a = 0 := ha
      have hw := congrArg (fun f ↦ f a) t.condition
      simpa [hp] using hw
    let γ := Ideal.Quotient.lift J t.inl.hom hkill
    let g : T →+* t.pt := γ.comp e.symm.toRingHom
    have hg (x : S) : g (L.reduction x) = t.inl.hom x := by
      change γ (e.symm (L.reduction x)) = _
      rw [← he x, e.symm_apply_apply]
      exact Ideal.Quotient.lift_mk J t.inl.hom hkill
    refine ⟨CommRingCat.ofHom g, ?_, ?_, ?_⟩
    · exact CommRingCat.hom_ext (RingHom.ext hg)
    · ext b
      obtain ⟨a, rfl⟩ := hπ b
      change g (algebraMap B T (π a)) = t.inr.hom (π a)
      rw [← hf, hg]
      exact congrArg (fun f ↦ f a) t.condition
    · intro k hk _
      ext x
      obtain ⟨q, rfl⟩ := e.surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
      rw [he]
      change k.hom (L.reduction y) = g (L.reduction y)
      rw [hg]
      exact congrArg (fun f ↦ f y) hk
  exact ⟨S, hS, f, IsPushout.of_isColimit hs⟩

private theorem comma_nonempty_of_point_surjective
    {C D : Type u} [Category.{v} C] [Category.{v} D]
    (H : C ⥤ D) (K : C) (L : D) (c : H.obj K ≅ L)
    (hPoint : ∀ S, Function.Surjective (fun f : S ⟶ K ↦ H.map f))
    (P : ObjectProperty C) (Q : ObjectProperty D)
    (hH : ∀ S, P S → Q (H.obj S))
    (hLift : ∀ T, Q T → ∃ S, P S ∧ Nonempty (H.obj S ≅ T))
    (T : ObjectProperty.FullSubcategory (fun X : Over L ↦ Q X.left)) :
    let F := ObjectProperty.lift (fun X : Over L ↦ Q X.left)
      ((ObjectProperty.ι (fun X : Over K ↦ P X.left)) ⋙ Over.post H ⋙ Over.map c.hom)
      (fun S ↦ hH S.obj.left S.property)
    Nonempty (StructuredArrow T F) := by
  classical
  obtain ⟨S, hS, ⟨e⟩⟩ := hLift T.obj.left T.property
  obtain ⟨q, hq⟩ := hPoint S (e.hom ≫ T.obj.hom ≫ c.inv)
  let S' : ObjectProperty.FullSubcategory (fun X : Over K ↦ P X.left) :=
    ⟨Over.mk q, hS⟩
  refine ⟨StructuredArrow.mk (Y := S') (ObjectProperty.homMk ?_)⟩
  refine Over.homMk e.inv ?_
  change e.inv ≫ (H.map q ≫ c.hom) = T.obj.hom
  change H.map q = e.hom ≫ T.obj.hom ≫ c.inv at hq
  rw [hq]
  simp



/-- Every pointed etale B-algebra has a map to a pointed base change.
Source: Stacks Project, Tag 04D1; step 2 of
`lem-sbc-pointed-etale-quotient-final`.
(blueprint: lem-sbc-pointed-etale-quotient-comma-nonempty)

Proof: Identify B with A/ker π. Apply the existing coefficient-lift theorem to
the underlying B-algebra of T. Its explicit Jacobian quotient S is etale over A,
and its reduction map is a pushout with π: factor any test cocone through the
quotient and the specified reduction equivalence. Uniqueness follows from
surjectivity of reduction. This yields an isomorphism e:H(S) -> T over B.

Maps S -> K correspond bijectively to maps H(S) -> H(K), by the proved
point-bijection theorem. Lift the point e followed by T -> L and c inverse
through that bijection, thereby giving S its A-algebra map to K. The equation
of the lifted point says that e inverse is a pointed map T -> F(S). This is
the required structured arrow. The lift ring is the genuine coefficient-lift
quotient already constructed in the library. -/
theorem pointedEtaleQuotient_comma_nonempty
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ≅ CommAlgCat.of B L)
    (T : ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left)) :
    Nonempty (StructuredArrow T (pointedEtaleBaseChange π c.hom)) := by
  classical
  let H := quotientBaseChange π
  apply comma_nonempty_of_point_surjective H (CommAlgCat.of A K)
    (CommAlgCat.of B L) c
    (fun S ↦ (quotientBaseChange_point_bijective A K B π hπ S).surjective)
    (fun S ↦ Etale A S) (fun S ↦ Etale B S) (fun S hS ↦ quotientBaseChange_etale π S hS) ?_ T
  intro T hT
  obtain ⟨S, hS, f, hp⟩ := exists_etale_pushout π hπ T hT
  let d : (Under.pushout (CommRingCat.ofHom π)).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj S) ≅
        (commAlgCatEquivUnder (CommRingCat.of B)).functor.obj T :=
    Under.isoMk hp.isoPushout.symm (by exact hp.inr_isoPushout_inv)
  exact ⟨S, hS, ⟨(commAlgCatEquivUnder (CommRingCat.of B)).inverse.mapIso d ≪≫
    ((commAlgCatEquivUnder (CommRingCat.of B)).unitIso.app T).symm⟩⟩


end Algebra
