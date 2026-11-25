/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# The external product of pro-étale complexes

For two schemes `a_X : X ⟶ s` and `a_Y : Y ⟶ s` over a base `s`, the *external product* of
`M ∈ D(X_proét)` and `N ∈ D(Y_proét)` is the complex

`M ⊠ N = Lp_X^* M ⊗ᴸ Lp_Y^* N`

on the fibre product `X ×_s Y`, where `p_X` and `p_Y` are the two projections. It is the
bifunctor out of which the Künneth-Verdier comparison and the Lefschetz-Verdier pairing are
built.

## Main definitions

- `AlgebraicGeometry.ProEtale.externalProduct`: the external product `M ⊠ N`.
-/

@[expose] public section

universe u' u

open CategoryTheory Abelian Limits MonoidalCategory

namespace AlgebraicGeometry.ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The external product `M ⊠ N = Lp_X^* M ⊗ᴸ Lp_Y^* N` on the fibre product `X ×_s Y`:

```
          X ×_s Y
         ↙       ↘
      p_X         p_Y
      ↙             ↘
     X               Y
      ↘             ↙
       a_X       a_Y
         ↘       ↙
             s
```

(blueprint: `sk-d-six`, `prose-11-08`). -/
noncomputable def externalProduct {s X Y : Scheme.{u}} (aX : X ⟶ s) (aY : Y ⟶ s)
    (M : DerivedCategory (Sheaf (Scheme.ProEt.topology X) A))
    (N : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) A)) :
    DerivedCategory (Sheaf (Scheme.ProEt.topology (pullback aX aY)) A) :=
  ((upperStar A (pullback.fst aX aY)).leftDerivedFunctor).obj M ⊗
    ((upperStar A (pullback.snd aX aY)).leftDerivedFunctor).obj N

end AlgebraicGeometry.ProEtale
