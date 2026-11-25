/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift
public import WeilConjectures.SixFunctors.Etale.Derived.Composition
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekTransport
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!

# External products on the étale site

Let `A` be a monoidal Grothendieck abelian coefficient category. For two schemes `X`, `Y` over
a base `B`, with projections `p : X ×_B Y ⟶ X` and `q : X ×_B Y ⟶ Y`, the *external product*
of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)` is

`K ⊠ M = Lp^* K ⊗ᴸ Lq^* M ∈ D((X ×_B Y)_ét)`.

The Künneth formulas for the external product are in the other modules of
`WeilConjectures.SixFunctors.Etale.Derived.Kunneth`.

## Main definitions

- `AlgebraicGeometry.Etale.externalProduct`: `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

namespace Etale

variable {B X Y : Scheme.{u}}

/-- The external product of `K ∈ D(X_ét)` and `M ∈ D(Y_ét)` along the fibre-product square

```
  X ×_B Y --q--> Y
     |           |
     p           g
     v           v
     X ---f----> B
```

namely `K ⊠ M = Lp^* K ⊗ᴸ Lq^* M`, an object of `D((X ×_B Y)_ét)`.

The absolute external product over a base scheme `S` is the case where `f` and `g` are the
structure morphisms of `X` and `Y`. -/
noncomputable def externalProduct (f : X ⟶ B) (g : Y ⟶ B)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)) :
    _root_.DerivedCategory (Sheaf (pullback f g).smallEtaleTopology A) :=
  -- Written with `derivedTensor A (pullback f g)` rather than `⊗`: the instance proofs of the
  -- monoidal structure then mention the scheme only through a variable, so they are not
  -- abstracted into auxiliary lemmas, and unfolding `externalProduct` against `⊗` stays cheap
  -- in the kernel (about 1s instead of about 2 minutes per unfolding).
  ((derivedTensor A (pullback f g)).obj ((L((pullback.fst f g)^*[A])).obj K)).obj
    ((L((pullback.snd f g)^*[A])).obj M)

end Etale

end AlgebraicGeometry
