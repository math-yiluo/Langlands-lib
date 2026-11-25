/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.EssentiallySmall

import Mathlib.Algebra.Category.CommAlgCat.FiniteType

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace RingTheory

/-- Essential smallness of the category of etale algebras trivial modulo the ideal.
Source: Stacks Project, Tag 0A02, the set-theoretic point in the construction;
Mathlib `FGAlgCat` and `essentiallySmall_of_fully_faithful`.
(blueprint: lem-weil-pbc-pair-henselization-essentially-small).

Proof: An etale ring map is finitely presented, hence of finite type. The equivalence
between rings under `B` and commutative `B`-algebras restricts to a fully faithful functor
from this full subcategory to `FGAlgCat B`. Mathlib proves that the latter is essentially
small using quotients of polynomial rings on finitely many variables. Essential smallness
pulls back along the fully faithful functor; the quotient condition needs no extra argument. -/
theorem pair_henselization_essentiallySmall (B : Type u) [CommRing B] (J : Ideal B) :
    EssentiallySmall.{u} (ObjectProperty.FullSubcategory
      (fun C : Under (CommRingCat.of B) ↦
        AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
          Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
            (Ideal.le_comap_map)))) := by
  let P : ObjectProperty (Under (CommRingCat.of B)) := fun C ↦
    AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map C.hom) ∧
      Function.Bijective (Ideal.quotientMap (J.map C.hom.hom) C.hom.hom
        (Ideal.le_comap_map))
  let F := P.ι ⋙ (commAlgCatEquivUnder (CommRingCat.of B)).inverse
  have hF : ∀ C : P.FullSubcategory, Algebra.FiniteType B (F.obj C) := by
    intro C
    have h : C.obj.hom.hom.Etale :=
      (AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mp
        C.property.1
    have hf := (RingHom.Etale.iff_flat_and_formallyUnramified.mp h).2.2
    exact @Algebra.FiniteType.of_finitePresentation _ _ _ _ _ hf
  exact essentiallySmall_of_fully_faithful
    (ObjectProperty.lift (fun A : CommAlgCat B ↦ Algebra.FiniteType B A) F hF)

end RingTheory
