/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs

/-!

# The base change theorem for the lower shriek

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

recorded as `sq : IsPullback g' f' f g`, and a compactification `c : X ⟶[i] Z ⟶[p] Y`
of `f`. This file deduces from the proper base change theorem
(`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`) that the compact-support
base-change morphism

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LowerShriek.MorphismDefs` is an
isomorphism, where `c' = c.ofIsPullback sq` and `Rf_!^c = Rf_!(c)[A]+` is the derived lower
shriek `Etale.rightDerivedLowerShriekOfCompactificationPlus` associated with `c`. No
properness is assumed on `f` itself: the properness enters only through the structure
morphism `p` of the compactification, which is proper by definition. This is the base
change theorem for the lower shriek `Compactification.lowerShriek`.

Indeed, in the composite defining `Ex_!^c` the extension-by-zero exchange is an
isomorphism by construction, and the direct-image exchange `Ex_*` of the proper square
of the base-changed compactification is an isomorphism by proper base change applied to
the proper morphism `p`, on complexes with torsion cohomology. For the pointwise
statement the extension by zero `i_!` must preserve torsion cohomology, which is a
stalkwise statement recorded separately
(`Etale.DerivedCategory.Plus.torsionHomology_openImmersionLowerShriek`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_lowerShriekBaseChange_of_isAddTorsion_ring`: for a
  torsion coefficient ring, the compact-support base-change transformation is an
  isomorphism of functors.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The base change theorem for the lower shriek as an isomorphism of functors**: if
the coefficient ring `Λ` is torsion as an additive group — in particular if `Λ` is
finite, e.g. `Λ = ℤ/ℓⁿℤ` — then for a cartesian square and a compactification `c` of
`f` the compact-support base-change transformation

`Ex_!^c : Rf_!^c ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_!^{c'}`

on the bounded below derived categories is an isomorphism: every complex automatically
has torsion cohomology. -/
theorem Etale.isIso_lowerShriekBaseChange_of_isAddTorsion_ring (Λ : Type (u + 1)) [CommRing Λ]
    (hΛ : IsAddTorsion Λ) (c : Compactification f) (sq : IsPullback g' f' f g) :
    IsIso (Etale.lowerShriekBaseChange (ModuleCat.{u + 1} Λ) c sq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro K
  rw [Etale.lowerShriekBaseChange_app]
  apply CategoryTheory.IsIso.comp_isIso' _ (Functor.map_isIso _ _)
  apply (NatTrans.isIso_iff_isIso_app _).mp
  exact Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring Λ hΛ
    (c.isPullback_g_ofIsPullback sq).flip

end AlgebraicGeometry
