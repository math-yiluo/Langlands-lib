/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare

/-!
# Open-immersion squares

An *open-immersion square* (blueprint `proposition-extension-zero-restriction-closed-subscheme--11`)
is a cartesian square
```
U' --g_U--> U
|           |
j'          j
v           v
X' --g-->   X
```
of schemes in which `j` and `j'` are open immersions, so that `U' = U ×_X X'`; no hypothesis is
made on `g`. Since open immersions are stable under base change, a cartesian square whose right
vertical map is an open immersion is an open-immersion square
(`AlgebraicGeometry.IsOpenImmersionSquare.of_isPullback`). For such a square the base change map
`j'_! g_U^* ⟶ g^* j_!` of the extension by zero is an isomorphism
(`AlgebraicGeometry.IsOpenImmersionSquare.isIso_openImmersionLowerShriekBaseChangeMap`).
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `proposition-extension-zero-restriction-closed-subscheme--11`: Open-immersion square.

A cartesian square `g_U ≫ j = j' ≫ g`
```
U' --g_U--> U
|           |
j'          j
v           v
X' --g-->   X
```
of schemes in which `j : U ⟶ X` and `j' : U' ⟶ X'` are open immersions, so that
`U' = U ×_X X'`. No hypothesis is made on `g`. -/
structure IsOpenImmersionSquare {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) : Prop extends IsPullback gU j' j g where
  isOpenImmersion_right : IsOpenImmersion j
  isOpenImmersion_left : IsOpenImmersion j'

namespace IsOpenImmersionSquare

variable {U' U X' X : Scheme.{u}} {gU : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {g : X' ⟶ X}

/-- A cartesian square whose right vertical map is an open immersion is an open-immersion
square: the left vertical map is an open immersion as a base change of one. -/
lemma of_isPullback (h : IsPullback gU j' j g) [IsOpenImmersion j] :
    IsOpenImmersionSquare gU j' j g where
  toIsPullback := h
  isOpenImmersion_right := inferInstance
  isOpenImmersion_left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h inferInstance

/-- **Base change for the extension by zero along an open-immersion square**: the base change
map `j'_! g_U^* ⟶ g^* j_!` is an isomorphism. -/
lemma isIso_openImmersionLowerShriekBaseChangeMap (h : IsOpenImmersionSquare gU j' j g)
    (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [HasSmallSiteSheafify A] :
    letI := h.isOpenImmersion_right
    letI := h.isOpenImmersion_left
    IsIso (Etale.openImmersionLowerShriekBaseChangeMap A h.toIsPullback.toCommSq) :=
  letI := h.isOpenImmersion_right
  letI := h.isOpenImmersion_left
  Etale.isIso_openImmersionLowerShriekBaseChangeMap A h.toIsPullback

end IsOpenImmersionSquare

end AlgebraicGeometry
