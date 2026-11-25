/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-!

# Lower shriek along a morphism admitting a compactification

For a morphism `f : X ⟶ Y` together with a compactification `X ⟶[i] Z ⟶[g] Y` (`i` an
open immersion, `g` proper), the lower shriek on small étale sites is the composition
`f_! := i_! ⋙ g_*` of the extension by zero along `i` with the pushforward
`AlgebraicGeometry.Etale.lowerStar` along `g`.

## Main definitions

- `AlgebraicGeometry.Etale.Compactification.lowerShriek`: the lower shriek `i_! ⋙ g_*`
  associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`.
- `AlgebraicGeometry.Etale.lowerShriek`: the lower shriek `f_!` of a morphism `f` satisfying
  `HasCompactification f`, *definitionally* equal to the composition associated with the
  chosen compactification `HasCompactification.compactification f`, see
  `Etale.lowerShriek_eq`.

## Main results

- `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerShriek`: the lower shriek `f_!` with
  values in an abelian category is left exact. This one needs sheafification to be *exact*,
  not merely to exist.

## Implementation notes

- The pushforward `g_*` of `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` is
  defined along the base change functor, which exists for an *arbitrary* morphism `g` — in
  contrast to the localization functor `MorphismProperty.Over.map ⊤ h` of
  `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, which requires
  `Etale g`. This is essential for compactifications, whose structure morphism is proper and
  in general is not étale.
- The open immersion of a compactification is étale by
  `AlgebraicGeometry.Etale.of_isOpenImmersion`, so the extension by zero along it is
  available; the Kan extension it needs exists because an open immersion is a monomorphism.
  Hence `f_!` carries no hypotheses beyond the standing assumptions on `A`.

-/

@[expose] public section

universe u' u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
variable {X Y : Scheme.{u}}

namespace Etale

namespace Compactification

variable {f : X ⟶ Y} (c : Compactification f)

/-- The lower shriek associated with a compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
extension by zero `i_!` followed by the pushforward `g_*`. -/
noncomputable def lowerShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  (c.i)_!open[A] ⋙ (c.g)_*[A]

end Compactification

variable (f : X ⟶ Y) [HasCompactification f]

/-- The lower shriek `f_!` along a morphism `f : X ⟶ Y` admitting a compactification, on
sheaves for the small étale sites: the composition `i_! ⋙ g_*` associated with the chosen
compactification `HasCompactification.compactification f`. -/
noncomputable def lowerShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  Compactification.lowerShriek A (HasCompactification.compactification f)

/-- The lower shriek `f_!` on étale sheaves is the extension by zero along the open
immersion of the chosen compactification followed by the pushforward `Etale.lowerStar`
along its proper structure morphism. -/
lemma lowerShriek_eq :
    lowerShriek A f =
      ((HasCompactification.compactification f).i)_!open[A] ⋙
        ((HasCompactification.compactification f).g)_*[A] :=
  rfl

/-- The lower shriek `f_!` on étale sheaves with values in a preadditive category is
additive, being the composition of the extension by zero along the open immersion of the
chosen compactification with the pushforward along its proper structure morphism. -/
instance lowerShriek_additive : (lowerShriek A f).Additive := by
  rw [lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on étale sheaves with values in an abelian category is left
exact, being the composition of the exact extension by zero along the open immersion of
the chosen compactification with the left exact pushforward along its proper structure
morphism.

The extension by zero is sheafification composed with a left Kan extension, so left
exactness of sheafification is needed here; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`. This is why
`HasSheafify` appears in addition to the `HasWeakSheafify` that defines `f_!`. -/
instance preservesFiniteLimits_lowerShriek :
    PreservesFiniteLimits (lowerShriek A f) := by
  rw [lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end Etale

--TODO: the composition isomorphism : `(fg)_! ≅ f_! g_!`

--TODO: invarience with choice of compcatification

end AlgebraicGeometry
