/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import WeilConjectures.RingTheory.SurjectiveQuotientBaseChange
public import Mathlib.CategoryTheory.Limits.Final
import WeilConjectures.RingTheory.PointedEtaleQuotientPoint
import WeilConjectures.RingTheory.PointedEtaleQuotientCommaNonempty
import WeilConjectures.RingTheory.PointedEtaleQuotientCommaRefinement

/-! # Finality of pointed etale base change

Source: Stacks Project, Tag 05WS, with the pointed-algebra argument of
`IsStrictHenselization.surjective_quotient`.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace Algebra

/-- Base change of pointed etale algebras along a surjective local map is final.
Source: Stacks Project, Tag 05WS; pointed-colimit proof as recorded in
lem-sbc-strict-henselization-surjective-quotient.
(blueprint: lem-sbc-pointed-etale-quotient-final)

Proof: The residue-field map induced by π is an isomorphism. Transport the
separable closures across it and identify H(K) with L, where H is extension of
scalars. Apply H to each pointed algebra S -> K and compose with this comparison;
etaleness is stable under base change. This constructs F. Its underlying algebra
diagram is definitionally H applied to the original diagram.

The coefficient-lift theorem produces an etale lift of every underlying target
algebra. The bijection on maps into K supplies its compatible point, so every
comma category (T down F) is nonempty. For two comma objects, choose a common
source successor using filteredness. Equalize their induced arrows in the target,
which is also filtered. Lift that equalizing etale morphism relative to its source
algebra using the same coefficient-lift construction. Its reduction isomorphism
produces a common successor in the comma category. Thus the two objects are
linked by a two-arrow zigzag. The connected-comma criterion gives finality.
No strict henselization C or colimit hypothesis is used. -/
theorem pointedEtaleQuotient_final
    (A K B L : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing B] [IsLocalRing B] [Field L]
    [Algebra (IsLocalRing.ResidueField B) L]
    [IsSepClosure (IsLocalRing.ResidueField B) L]
    [Algebra B L] [IsScalarTower B (IsLocalRing.ResidueField B) L]
    (π : A →+* B) (hπ : Function.Surjective π) :
    let P : ObjectProperty (Over (CommAlgCat.of A K)) := fun X ↦ Etale A X.left
    let Q : ObjectProperty (Over (CommAlgCat.of B L)) := fun X ↦ Etale B X.left
    ∃ F : P.FullSubcategory ⥤ Q.FullSubcategory, F.Final ∧
      Nonempty ((P.ι ⋙ Over.forget (CommAlgCat.of A K)) ⋙ quotientBaseChange π ≅
        F ⋙ (Q.ι ⋙ Over.forget (CommAlgCat.of B L))) := by
  classical
  obtain ⟨c⟩ := pointedEtaleQuotient_point_iso A K B L π hπ
  let F := pointedEtaleBaseChange π c.hom
  refine ⟨F, ?_, ⟨pointedEtaleBaseChange_forgetIso π c.hom⟩⟩
  refine ⟨fun T ↦ ?_⟩
  have : Nonempty (StructuredArrow T F) :=
    pointedEtaleQuotient_comma_nonempty A K B L π hπ c T
  apply zigzag_isConnected
  intro X Y
  obtain ⟨Z, ⟨f⟩, ⟨g⟩⟩ :=
    pointedEtaleQuotient_comma_refinement A K B L π hπ c T X Y
  exact (Relation.ReflTransGen.single (show Zag X Z from Or.inl ⟨f⟩)).trans
    (Relation.ReflTransGen.single (show Zag Z Y from Or.inr ⟨g⟩))

end Algebra
