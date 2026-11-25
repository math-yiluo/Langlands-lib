/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Extension of scalars along a surjection

Source: Stacks Project, Tag 05WS; the quotient description is the pushout universal
property for commutative rings.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Extension of scalars, constructed by pushout in commutative rings. -/
noncomputable def quotientBaseChange {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) : CommAlgCat.{u} A ⥤ CommAlgCat.{u} B :=
  (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    Under.pushout (CommRingCat.ofHom π) ⋙
      (commAlgCatEquivUnder (CommRingCat.of B)).inverse

noncomputable instance {A B : Type u} [CommRing A] [CommRing B] (π : A →+* B) :
    (quotientBaseChange π).IsLeftAdjoint := by
  unfold quotientBaseChange
  infer_instance

/-- Extension of scalars along a surjection `π : A → B` with kernel `I` sends `C` to
`C ⧸ I C`, where `C ⧸ I C` carries a `B`-algebra structure compatible with `π`. Since `π`
is surjective, this is the structure induced by `π`.
Source: Stacks Project, Tag 05WS (the ring pushout calculation).
(blueprint: lem-sbc-surjective-quotient-base-change)

Proof: The maps C -> Q and B -> Q form a pushout: for maps C -> T and B -> T agreeing on
A, the map C -> T kills IC, and so factors uniquely through Q. The factor respects the
B-action since this can be checked after π. The pushout used in quotientBaseChange is
uniquely isomorphic to this explicit pushout. Transport through the equivalence with
commutative B-algebras yields the claimed isomorphism. This argument includes I = 0 and
does not assume C is local. -/
noncomputable def quotientBaseChangeObjIso
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C] [Algebra A C]
    (π : A →+* B) (hπ : Function.Surjective π)
    (I : Ideal A) (hker : RingHom.ker π = I)
    [Algebra B (C ⧸ I.map (algebraMap A C))]
    (hcomp : (algebraMap B (C ⧸ I.map (algebraMap A C))).comp π =
      (Ideal.Quotient.mk _).comp (algebraMap A C)) :
    (quotientBaseChange π).obj (CommAlgCat.of A C) ≅
      CommAlgCat.of B (C ⧸ I.map (algebraMap A C)) :=
  let J := I.map (algebraMap A C)
  let s : PushoutCocone (CommRingCat.ofHom (algebraMap A C)) (CommRingCat.ofHom π) :=
    PushoutCocone.mk (CommRingCat.ofHom (Ideal.Quotient.mk J))
      (CommRingCat.ofHom (algebraMap B (C ⧸ J))) (by
        ext a
        exact (RingHom.congr_fun hcomp a).symm)
  have hs : IsColimit s := PushoutCocone.isColimitAux' s fun t ↦ by
    have hkill' : J ≤ RingHom.ker t.inl.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change t.inl.hom (algebraMap A C a) = 0
      have hp : π a = 0 := RingHom.mem_ker.mp (hker.symm ▸ ha)
      have hw := congrArg (fun f ↦ f a) t.condition
      simpa [hp] using hw
    have hkill : ∀ x ∈ J, t.inl.hom x = 0 := fun x hx ↦ hkill' hx
    refine ⟨CommRingCat.ofHom (Ideal.Quotient.lift J t.inl.hom hkill), ?_, ?_, ?_⟩
    · ext x
      exact Ideal.Quotient.lift_mk J t.inl.hom hkill
    · ext b
      obtain ⟨a, rfl⟩ := hπ b
      change Ideal.Quotient.lift J t.inl.hom hkill (algebraMap B (C ⧸ J) (π a)) =
        t.inr.hom (π a)
      rw [show algebraMap B (C ⧸ J) (π a) = Ideal.Quotient.mk J (algebraMap A C a) from
        RingHom.congr_fun hcomp a]
      exact (Ideal.Quotient.lift_mk J t.inl.hom hkill).trans
        (congrArg (fun f ↦ f a) t.condition)
    · intro m hm _
      ext x
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact (congrArg (fun f ↦ f c) hm).trans
        (Ideal.Quotient.lift_mk J t.inl.hom hkill).symm
  have hp := IsPushout.of_isColimit hs
  let e : (Under.pushout (CommRingCat.ofHom π)).obj
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj (CommAlgCat.of A C)) ≅
      CommRingCat.mkUnder (CommRingCat.of B) (C ⧸ J) :=
    Under.isoMk hp.isoPushout.symm hp.inr_isoPushout_inv
  let e' : (commAlgCatEquivUnder (CommRingCat.of B)).inverse.obj
      (CommRingCat.mkUnder (CommRingCat.of B) (C ⧸ J)) ≅ CommAlgCat.of B (C ⧸ J) :=
    CommAlgCat.isoMk (@AlgEquiv.ofRingEquiv B (C ⧸ J) (C ⧸ J) _ _ _
      (algebraMap B (C ⧸ J)).toAlgebra _ (.refl _) fun _ ↦ rfl)
  (commAlgCatEquivUnder (CommRingCat.of B)).inverse.mapIso e ≪≫ e'

end Algebra
