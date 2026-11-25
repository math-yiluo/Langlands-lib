/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.CategoryTheory.EssentiallySmall

import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Essential smallness of pointed etale algebras

Source: Stacks Project, Tag 04GW (pointed-algebra category); Mathlib finite-type algebra
smallness (blueprint: lem-sc-pointed-etale-essentially-small).

The category embeds fully faithfully into finitely generated algebras pointed into `K`.
Mathlib proves essential smallness of that costructured arrow category.
-/

@[expose] public section
universe u
open CategoryTheory
namespace Algebra

/-- Essential smallness follows from finite-presentation representatives of affine etale
algebras and the set of pointings into a fixed K.
Source: Stacks Project, Algebra, Tag 04GW.
(blueprint: lem-sc-pointed-etale-essentially-small).

Proof: An etale algebra is finitely presented, hence finitely generated. Send a pointed
etale algebra to the same algebra and pointing in the costructured arrow category of
`FGAlgCat R` over `CommAlgCat.of R K`. This functor is fully faithful: both categories
have exactly the algebra maps commuting with the pointings. Mathlib proves `FGAlgCat R`
essentially small, and its costructured arrow category is essentially small because
`CommAlgCat R` is locally small. Pull essential smallness back along this functor. -/
theorem pointedEtale_essentiallySmall
    (R K : Type u) [CommRing R] [IsLocalRing R] [Field K]
    [Algebra (IsLocalRing.ResidueField R) K]
    [IsSepClosure (IsLocalRing.ResidueField R) K] [Algebra R K]
    [IsScalarTower R (IsLocalRing.ResidueField R) K] :
    let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
    EssentiallySmall.{u} P.FullSubcategory := by
  let P : ObjectProperty (Over (CommAlgCat.of R K)) := fun X ↦ Etale R X.left
  let Q : ObjectProperty (CommAlgCat R) := fun A ↦ FiniteType R A
  let F : P.FullSubcategory ⥤ CostructuredArrow Q.ι (CommAlgCat.of R K) :=
    { obj := fun A ↦
        CostructuredArrow.mk (Y := (⟨A.obj.left, by
          have : Etale R A.obj.left := A.property
          infer_instance⟩ : Q.FullSubcategory)) A.obj.hom
      map := fun f ↦ CostructuredArrow.homMk (ObjectProperty.homMk f.hom.left)
        (Over.w f.hom) }
  have hF : F.FullyFaithful :=
    { preimage := fun f ↦ ObjectProperty.homMk
        (Over.homMk f.left.hom (CostructuredArrow.w f)) }
  have : F.Full := hF.full
  have : F.Faithful := hF.faithful
  exact essentiallySmall_of_fully_faithful F
end Algebra
