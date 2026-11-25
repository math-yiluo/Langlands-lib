/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.UpperLowerStar.Defs

/-!

# The pushforward `g_*` is lax symmetric monoidal

For a morphism of schemes `g : W ⟶ U` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued sheaves for the small `Q`-topologies is lax braided. This is
the general statement for the pushforward along a continuous functor of sites, applied to the
base change functor; when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

## Main results

- `CategoryTheory.GrothendieckTopology.laxBraided_lowerStar`: the pushforward `g_*` is lax
  braided.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.GrothendieckTopology

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]
  [MonoidalCategory A] [BraidedCategory A]

variable (P Q : MorphismProperty Scheme.{u})
variable [P.IsMultiplicative] [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  [Q.IsMultiplicative] [Q.IsStableUnderBaseChange]
variable (hQP : Q ≤ P)

variable {W U : Scheme.{u}} (g : W ⟶ U)
  [((U.smallGrothendieckTopology Q (Q := P)).W (A := A)).IsMonoidal]
  [((W.smallGrothendieckTopology Q (Q := P)).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` is lax monoidal. -/
noncomputable instance laxMonoidal_lowerStar : (lowerStar A P Q hQP g).LaxMonoidal :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (Functor.LaxMonoidal
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

/-- The pushforward `g_*` is lax braided. When `A` is symmetric, this says that `g_*` is lax
symmetric monoidal. -/
noncomputable instance laxBraided_lowerStar : (lowerStar A P Q hQP g).LaxBraided :=
  have := isContinuous_overPullback P Q hQP g
  inferInstanceAs (Functor.LaxBraided
    ((MorphismProperty.Over.pullback P ⊤ g).sheafPushforwardContinuous A
      (U.smallGrothendieckTopology Q (Q := P)) (W.smallGrothendieckTopology Q (Q := P))))

end CategoryTheory.GrothendieckTopology
