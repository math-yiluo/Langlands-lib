/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.AbsoluteFrobenius
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal

/-!
# The trivializations of the absolute Frobenius are monoidal

Let `X` be a scheme in which the prime `p` vanishes and `F_X` its `p ^ n`-power absolute
Frobenius. The trivializations `F_{X*} ≅ 𝟭` and `F_X^* ≅ 𝟭` of
`AlgebraicGeometry.ProEtale.lowerStarIterateFrobeniusIso` and
`AlgebraicGeometry.ProEtale.upperStarIterateFrobeniusIso` are monoidal natural isomorphisms,
for the lax monoidal structure of the pushforward, the strong monoidal structure of the pullback
and the identity monoidal structure of `𝟭`. The first one is the identification of the
pushforward along a functor isomorphic to the identity
(`CategoryTheory.Functor.isMonoidal_sheafPushforwardContinuousId'`); the second one follows by
conjugation along the monoidal adjunctions `𝟭 ⊣ 𝟭` and `F_X^* ⊣ F_{X*}`.

## Main results

- `AlgebraicGeometry.ProEtale.isMonoidal_lowerStarIterateFrobeniusIso_hom`: `F_{X*} ≅ 𝟭` is
  monoidal.
- `AlgebraicGeometry.ProEtale.isMonoidal_upperStarIterateFrobeniusIso_hom`: `F_X^* ≅ 𝟭` is
  monoidal.

The inverses are then monoidal by the general instance on `CategoryTheory.Iso.inv`.
-/

@[expose] public section

universe u' u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

variable {X : Scheme.{u}} {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0) (n : ℕ)

/-- The trivialization `F_{X*} ≅ 𝟭` of the pushforward along the absolute Frobenius is
monoidal. -/
instance isMonoidal_lowerStarIterateFrobeniusIso_hom :
    NatTrans.IsMonoidal (lowerStarIterateFrobeniusIso A hp hX n).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.sheafPushforwardContinuousId'
    (Scheme.ProEt.overPullbackIterateFrobeniusIso hp hX n) A (Scheme.ProEt.topology X)).hom)

/-- The trivialization `F_X^* ≅ 𝟭` of the pullback along the absolute Frobenius is monoidal:
it is conjugate to the monoidal isomorphism `𝟭 ≅ F_{X*}`. -/
instance isMonoidal_upperStarIterateFrobeniusIso_hom :
    NatTrans.IsMonoidal (upperStarIterateFrobeniusIso A hp hX n).hom :=
  isMonoidal_conjugateEquiv_symm Adjunction.id
    (upperStarLowerStarAdjunction A (X.iterateFrobenius hp hX n))
    (lowerStarIterateFrobeniusIso A hp hX n).inv

end AlgebraicGeometry.ProEtale
