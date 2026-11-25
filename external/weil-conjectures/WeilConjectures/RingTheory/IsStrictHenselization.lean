/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IsSepClosed

/-!
# Ring strict henselization

Source: Stacks Project, Algebra, Lemma Tag 04GW, with the pointed-algebra description in
its proof (blueprint: def-sc-ring-strict-henselization).

The predicate specifies the colimit by an actual universal cocone, rather than choosing
its underlying ring. The large category of pointed etale algebras is essentially small:
finite presentation gives a set of representatives. No large-colimit instance is assumed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-- The `A`-algebra `C` is the strict henselization of the local ring `A` relative to the
chosen separable closure `K` of its residue field if it is a colimit of etale `A`-algebras
pointed in `K`. Source: Stacks Project, Tag 04GW (blueprint: def-sc-ring-strict-henselization).
An algebra map `S → K` is equivalent to a prime `q = ker(S → K)` and an embedding of
its residue field into `K` over the residue field of `A`. Morphisms commute with these
maps to `K`. The forgetful diagram retains `S` and its `A`-algebra transition maps.
`Nonempty (IsColimit c)` is the usual universal property, and the final algebra isomorphism
identifies the cocone vertex with `C`, including its structural map from `A`. -/
def IsStrictHenselization (A K C : Type u) [CommRing A] [IsLocalRing A] [Field K]
    [Algebra (IsLocalRing.ResidueField A) K] [IsSepClosure (IsLocalRing.ResidueField A) K]
    [Algebra A K] [IsScalarTower A (IsLocalRing.ResidueField A) K]
    [CommRing C] [Algebra A C] : Prop :=
  let P : ObjectProperty (Over (CommAlgCat.of A K)) := fun X => Etale A X.left
  let D := P.ι ⋙ Over.forget (CommAlgCat.of A K)
  ∃ c : Cocone D, Nonempty (IsColimit c) ∧ Nonempty (c.pt ≅ CommAlgCat.of A C)

end Algebra
