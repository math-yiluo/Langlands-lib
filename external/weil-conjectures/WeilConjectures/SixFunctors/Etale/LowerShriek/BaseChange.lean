/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap

/-!
# Base change for extensions by zero along étale morphisms

For a cartesian square with `v` étale, `g^* v_! ≅ v'_! g'^*`
(`AlgebraicGeometry.Etale.etaleLowerShriekBaseChangeIso`): the two sides are left adjoint to the
two sides of the degree-zero base change `v^* g_* ≅ g'_* v'^*` along the étale `v`. This is an
input to the constructibility of extensions by zero along étale maps [Stacks 03SA], where it
identifies the restriction of `v_! Λ` to a stratum with the extension by zero along the base
change of `v`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] {W' W X Y : Scheme.{u}} {v : W ⟶ X} {g : Y ⟶ X}
  {v' : W' ⟶ Y} {g' : W' ⟶ W} [Etale v] [Etale v']

/-- **Base change for extensions by zero along étale morphisms**: for a cartesian square
```
W' --v'--> Y
|          |
g'         g
v          v
W  --v---> X
```
with `v` étale, `g^* v_! ≅ v'_! g'^*` on étale sheaves of `Λ`-modules. Both are left adjoint to
the two sides of the degree-zero base change `v^* g_* ≅ g'_* v'^*`, an isomorphism as `v` is
étale (`AlgebraicGeometry.Etale.isIso_baseChangeMap_flip_of_isPullback`). -/
noncomputable def Etale.etaleLowerShriekBaseChangeIso (sq : IsPullback v' g' g v) :
    Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v inferInstance ⋙
        (g)^*[ModuleCat.{u + 1} Λ] ≅
      (g')^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v' inferInstance :=
  have : IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
    Etale.isIso_baseChangeMap_flip_of_isPullback _ sq.flip
  (((Etale.etaleLowerShriekUpperStarAdjunction _ v inferInstance).comp
      (Etale.upperStarLowerStarAdjunction _ g)).ofNatIsoRight
      (asIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq))).leftAdjointUniq
    ((Etale.upperStarLowerStarAdjunction _ g').comp
      (Etale.etaleLowerShriekUpperStarAdjunction _ v' inferInstance))

end AlgebraicGeometry
