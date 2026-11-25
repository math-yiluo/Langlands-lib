/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PointedEtaleQuotientFunctor
import WeilConjectures.RingTheory.PointedEtaleQuotientPointBijective
import WeilConjectures.RingTheory.EtaleAlgebraLift
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Surjective

/-! # Lifting morphisms of pointed etale algebras across a quotient

Source: Stacks Project, Tag 04D1, applied relative to a pointed etale algebra;
the lifting step of Tag 05WS.
-/

@[expose] public section

universe u
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

private theorem unpointed_morphism_lift {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) (hπ : Function.Surjective π)
    (S : CommAlgCat.{u} A) (hS : Etale A S) (T : CommAlgCat.{u} B) (hT : Etale B T)
    (f : (quotientBaseChange π).obj S ⟶ T) :
    let H := (quotientBaseChange π)
    ∃ (W : CommAlgCat.{u} A), Etale A W ∧
      ∃ (g : S ⟶ W) (e : H.obj W ≅ T), H.map g ≫ e.hom = f := by
  classical
  let H := (quotientBaseChange π)
  let V := H.obj S
  let q := pushout.inl (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π)
  let P := fun {X Y : Type u} [CommRing X] [CommRing Y] (f : X →+* Y) ↦
    Function.Surjective f
  have : (RingHom.toMorphismProperty P).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := P)).mpr
      RingHom.surjective_isStableUnderBaseChange
  have hq : Function.Surjective q.hom := MorphismProperty.of_isPushout
    (P := RingHom.toMorphismProperty P)
    (IsPushout.of_hasPushout (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π)) hπ
  let : Algebra V T := f.hom.toRingHom.toAlgebra
  have : IsScalarTower B V T := IsScalarTower.of_algebraMap_eq fun b ↦
    (f.hom.commutes b).symm
  have : Etale B V := quotientBaseChange_etale π S hS
  have := hT
  have hTV : Etale V T := Etale.of_restrictScalars B V T
  obtain ⟨W, hW, w, hp⟩ := exists_etale_pushout q.hom hq (CommAlgCat.of V T) hTV
  let : Algebra A W := ((algebraMap S W).comp (algebraMap A S)).toAlgebra
  have : IsScalarTower A S W := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have := hS
  have := hW
  have hWA : Etale A W := Etale.comp A S W
  let W' := CommAlgCat.of A W
  let g : S ⟶ W' := CommAlgCat.ofHom (IsScalarTower.toAlgHom A S W)
  have hp0 := IsPushout.of_hasPushout (CommRingCat.ofHom (algebraMap A S))
    (CommRingCat.ofHom π)
  have hp2 : CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A W))
      (CommRingCat.ofHom π) w (CommRingCat.ofHom (algebraMap B T)) := by
    convert hp0.paste_horiz hp using 1
    ext b
    exact (f.hom.commutes b).symm
  let d : (Under.pushout (CommRingCat.ofHom π)).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj W') ≅
        (commAlgCatEquivUnder (CommRingCat.of B)).functor.obj T :=
    Under.isoMk hp2.isoPushout.symm (by exact hp2.inr_isoPushout_inv)
  let e : H.obj W' ≅ T := (commAlgCatEquivUnder (CommRingCat.of B)).inverse.mapIso d ≪≫
    ((commAlgCatEquivUnder (CommRingCat.of B)).unitIso.app T).symm
  refine ⟨W', hWA, g, e, ?_⟩
  apply (commAlgCatEquivUnder (CommRingCat.of B)).functor.map_injective
  apply Under.UnderMorphism.ext
  change pushout.desc (CommRingCat.ofHom (algebraMap S W) ≫
      pushout.inl (CommRingCat.ofHom (algebraMap A W)) (CommRingCat.ofHom π))
    (pushout.inr (CommRingCat.ofHom (algebraMap A W)) (CommRingCat.ofHom π)) _ ≫
      hp2.isoPushout.inv = CommRingCat.ofHom f.hom.toRingHom
  apply pushout.hom_ext
  · simp only [Category.assoc, pushout.inl_desc_assoc, hp2.inl_isoPushout_inv]
    exact hp.w
  · simp only [pushout.inr_desc_assoc, hp2.inr_isoPushout_inv]
    ext b
    exact (f.hom.commutes b).symm

private theorem pointed_morphism_lift_of_point_bijective
    {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) (K : C) (L : D) (c : H.obj K ≅ L)
    (hPoint : ∀ S, Function.Bijective (fun f : S ⟶ K ↦ H.map f))
    (P : ObjectProperty C) (Q : ObjectProperty D) (hH : ∀ S, P S → Q (H.obj S))
    (hLift : ∀ S, P S → ∀ T, Q T → ∀ f : H.obj S ⟶ T,
      ∃ W, P W ∧ ∃ (g : S ⟶ W) (e : H.obj W ≅ T), H.map g ≫ e.hom = f)
    (S : ObjectProperty.FullSubcategory (fun X : Over K ↦ P X.left))
    (T : ObjectProperty.FullSubcategory (fun X : Over L ↦ Q X.left)) :
    let F := ObjectProperty.lift (fun X : Over L ↦ Q X.left)
      ((ObjectProperty.ι (fun X : Over K ↦ P X.left)) ⋙ Over.post H ⋙ Over.map c.hom)
      (fun S ↦ hH S.obj.left S.property)
    ∀ f : F.obj S ⟶ T, ∃ (W : ObjectProperty.FullSubcategory (fun X : Over K ↦ P X.left))
      (g : S ⟶ W) (e : F.obj W ≅ T), F.map g ≫ e.hom = f := by
  classical
  intro F f
  obtain ⟨W, hW, g, e, hg⟩ := hLift S.obj.left S.property T.obj.left T.property f.hom.left
  obtain ⟨q, hq⟩ := (hPoint W).surjective (e.hom ≫ T.obj.hom ≫ c.inv)
  change H.map q = e.hom ≫ T.obj.hom ≫ c.inv at hq
  have hgp : g ≫ q = S.obj.hom := by
    apply (hPoint S.obj.left).injective
    change H.map (g ≫ q) = H.map S.obj.hom
    rw [H.map_comp, hq, ← Category.assoc, ← Category.assoc, hg]
    have hf := Over.w f.hom
    change f.hom.left ≫ T.obj.hom = H.map S.obj.hom ≫ c.hom at hf
    simpa using congrArg (· ≫ c.inv) hf
  let W' : ObjectProperty.FullSubcategory (fun X : Over K ↦ P X.left) :=
    ⟨Over.mk q, hW⟩
  let g' : S ⟶ W' := ObjectProperty.homMk (Over.homMk g hgp)
  refine ⟨W', g', ObjectProperty.isoMk _ (Over.isoMk e ?_), ?_⟩
  · change e.hom ≫ T.obj.hom = H.map q ≫ c.hom
    rw [hq]
    simp
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hg

/-- Lift an etale extension of a base-changed pointed algebra, including its structure map.
Source: Stacks Project, Tag 04D1; the relative form of the lifting argument of
`lem-sbc-pointed-etale-quotient-final`.
(blueprint: lem-sbc-pointed-etale-quotient-morphism-lift)

Proof: Let U be the underlying A-algebra of S and V = H(U). The canonical U -> V
is surjective, by stability of surjectivity under ring pushouts. Regard the
underlying algebra of T as a V-algebra via f. It is etale over V: both V and T
are etale over B, and a map between etale B-algebras is etale, by
`Etale.of_restrictScalars`. Identify V with U/ker(U -> V). Apply the explicit
coefficient-lift construction of Tag 04D1 over U to this etale V-algebra. Its
ring W is etale over U and its reduction is T with its specified V-structure
map. Composition makes W etale over A.

The canonical K -> H(K) is an isomorphism because ker π acts trivially on K.
Compose it with c to identify K with L. Point W by W -> T -> L -> K. The
commutativity of f with the points ensures that U -> W preserves the K-points.
Thus W is a pointed etale A-algebra S' and the structure map is g:S -> S'.
The reduction square U -> W, V -> T is a ring pushout. Pasting it with the
pushout A -> U, B -> V identifies H(W) with T. This identifies the base-changed
structure map with f. The same point equation gives a pointed isomorphism
e:F(S') -> T, and hence F(g) followed by e is f. No nilpotence or local-ring
hypothesis on U is used. The lift ring is the explicit Jacobian quotient,
not unspecified data selected from a bare existence assertion. -/
theorem pointedEtaleQuotient_morphism_lift
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π)
    (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ≅ CommAlgCat.of B L)
    (S : ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left))
    (T : ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left))
    (f : (pointedEtaleBaseChange π c.hom).obj S ⟶ T) :
    ∃ (S' : ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left))
      (g : S ⟶ S') (e : (pointedEtaleBaseChange π c.hom).obj S' ≅ T),
      (pointedEtaleBaseChange π c.hom).map g ≫ e.hom = f := by
  exact pointed_morphism_lift_of_point_bijective (quotientBaseChange π)
    (CommAlgCat.of A K) (CommAlgCat.of B L) c
    (fun S ↦ quotientBaseChange_point_bijective A K B π hπ S)
    (fun S ↦ Etale A S) (fun T ↦ Etale B T)
    (fun S hS ↦ quotientBaseChange_etale π S hS)
    (fun S hS T hT f ↦ unpointed_morphism_lift π hπ S hS T hT f) S T f

end Algebra
