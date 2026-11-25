/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange
import Mathlib.RingTheory.RingHom.Etale

/-! # The pointed extension-of-scalars functor

Source: Stacks Project, Tag 05WS, and the first step of
`lem-sbc-pointed-etale-quotient-final`.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Etaleness is preserved by the pushout defining extension of scalars.
Source: Stacks Project, Tag 00U2 (base change of etale ring maps).
(blueprint: lem-sbc-pointed-etale-quotient-functor)

Proof: Apply stability under cobase change of the etale ring-map property to
A -> S and A -> B. The other side of the pushout is the structural B-algebra map. -/
theorem quotientBaseChange_etale {A B : Type u} [CommRing A] [CommRing B]
    (π : A →+* B) (S : CommAlgCat.{u} A) (hS : Etale A S) :
    Etale B ((quotientBaseChange π).obj S) := by
  have : (RingHom.toMorphismProperty RingHom.Etale).IsStableUnderCobaseChange :=
    (RingHom.isStableUnderCobaseChange_toMorphismProperty_iff (P := RingHom.Etale)).mpr
      RingHom.Etale.isStableUnderBaseChange
  have h := MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty RingHom.Etale)
    (IsPushout.of_hasPushout
      (CommRingCat.ofHom (algebraMap A S)) (CommRingCat.ofHom π)).flip
    ((RingHom.etale_algebraMap).mpr hS)
  exact (RingHom.etale_algebraMap).mp h

/-- Postcompose the base-changed point with the specified comparison to L, then restrict
 to etale algebras. This is a construction, with no choice of lifted etale algebras.
Source: Stacks Project, Tag 05WS.
(blueprint: lem-sbc-pointed-etale-quotient-functor) -/
noncomputable def pointedEtaleBaseChange {A K B L : Type u}
    [CommRing A] [CommRing K] [Algebra A K]
    [CommRing B] [CommRing L] [Algebra B L]
    (π : A →+* B) (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ⟶
      CommAlgCat.of B L) :
    ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left) ⥤
      ObjectProperty.FullSubcategory (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left) :=
  ObjectProperty.lift _
    ((ObjectProperty.ι (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left)) ⋙
      Over.post (quotientBaseChange π) ⋙ Over.map c)
    (fun S ↦ quotientBaseChange_etale π S.obj.left S.property)

/-- The underlying algebra diagram of pointed base change is extension of scalars.
Source: Stacks Project, Tag 05WS.
(blueprint: lem-sbc-pointed-etale-quotient-functor) -/
noncomputable def pointedEtaleBaseChange_forgetIso {A K B L : Type u}
    [CommRing A] [CommRing K] [Algebra A K]
    [CommRing B] [CommRing L] [Algebra B L]
    (π : A →+* B) (c : (quotientBaseChange π).obj (CommAlgCat.of A K) ⟶
      CommAlgCat.of B L) :
    ((ObjectProperty.ι (fun X : Over (CommAlgCat.of A K) ↦ Etale A X.left)) ⋙
      Over.forget (CommAlgCat.of A K)) ⋙ quotientBaseChange π ≅
    pointedEtaleBaseChange π c ⋙
      ((ObjectProperty.ι (fun X : Over (CommAlgCat.of B L) ↦ Etale B X.left)) ⋙
        Over.forget (CommAlgCat.of B L)) := Iso.refl _

end Algebra
