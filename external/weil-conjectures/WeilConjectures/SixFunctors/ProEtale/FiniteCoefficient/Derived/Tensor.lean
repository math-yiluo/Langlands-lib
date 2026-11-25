/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory

/-!

# The derived tensor product of pro-étale sheaves

Let `A` be a monoidal Grothendieck abelian coefficient category and let `X` be a scheme.
The category `Sheaf (Scheme.ProEt.topology X) A` of `A`-valued pro-étale sheaves on `X` is then a
monoidal Grothendieck abelian category, so it has a derived category `D(X_proét)`, and the
K-flat machinery migrated from mathlib PR #25848 equips `D(X_proét)` with the *derived tensor
product* `- ⊗ᴸ -`, the total left derived functor of `- ⊗ -` in two variables.

## Main definitions

- `AlgebraicGeometry.ProEtale.derivedTensor` : the derived tensor product
  `- ⊗ᴸ - : D(X_proét) ⥤ D(X_proét) ⥤ D(X_proét)`, with scoped
  notation `-⊗ᴸ-(X)[A]`.

## Main results

- `AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor` : the derived tensor product
  really is the total left derived functor of the tensor product of pro-étale sheaves, in two
  variables.

- `AlgebraicGeometry.ProEtale.laxMonoidal_Q` : the localization functor
  `Q : C(X_proét) ⥤ D(X_proét)` is lax monoidal.

## Implementation notes

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.

The monoidal structure on `Sheaf (Scheme.ProEt.topology X) A` is the global instance
`AlgebraicGeometry.ProEtale.sheafMonoidalCategory` of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`, the pro-étale site being
essentially small. Note that the *type* of `derivedTensor` does not mention the monoidal
structure.

That `D(X_proét)` is monoidal at all comes from
`DerivedCategory.hasDerivedMonoidalCategory` in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`, which is why
the hypotheses below are exactly the ones that instance asks of the category of pro-étale
sheaves: monoidal closed (so that tensoring preserves colimits) and admitting functorial
flat resolutions.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A]

variable (X : Scheme.{u})

variable [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]

namespace ProEtale

/-- Blueprint `prose-03-02`: Derived pullback, tensor product, and
internal Hom; the derived tensor product.

The derived tensor product `- ⊗ᴸ - : D(X_proét) ⥤ D(X_proét) ⥤ D(X_proét)` on the unbounded
derived category of `A`-valued pro-étale sheaves on `X`: the tensor product of the monoidal
structure on `D(X_proét)` obtained from the K-flat left derivability structure. For
`A = ModuleCat R` it is `K₁ ⊗ᴸ_R K₂ = P ⊗_R K₂` for a K-flat resolution `P → K₁`
(`AlgebraicGeometry.ProEtale.isLeftDerivedFunctor₂_derivedTensor`).

(blueprint: `prose-03-02`) -/
@[implicit_reducible]
noncomputable def derivedTensor :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) ⥤
        DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  curriedTensor _

@[inherit_doc derivedTensor]
scoped notation "-⊗ᴸ-(" X ")[" A "]" => derivedTensor A X

noncomputable instance laxMonoidal_Q :
    (DerivedCategory.Q (C := Sheaf (Scheme.ProEt.topology X) A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQ (Sheaf (Scheme.ProEt.topology X) A)

noncomputable instance laxMonoidal_Qh :
    (DerivedCategory.Qh (C := Sheaf (Scheme.ProEt.topology X) A)).LaxMonoidal :=
  DerivedCategory.laxMonoidalQh (Sheaf (Scheme.ProEt.topology X) A)

instance isLeftDerivedFunctor₂_derivedTensor :
    -⊗ᴸ-(X)[A].IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Sheaf (Scheme.ProEt.topology X) A) (ComplexShape.up ℤ)) :=
  DerivedCategory.isLeftDerivedFunctor₂CurriedTensor (Sheaf (Scheme.ProEt.topology X) A)

end ProEtale

end AlgebraicGeometry
