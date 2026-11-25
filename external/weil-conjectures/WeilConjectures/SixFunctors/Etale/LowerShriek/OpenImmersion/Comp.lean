/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!

# Composition of extensions by zero

For open immersions `j' : V ⟶ U` and `j : U ⟶ X` the extension by zero along the composite
is the composite of the extensions by zero, `(j' ≫ j)_! ≅ j'_! ⋙ j_!`. For an isomorphism
`e : U ≅ U'` of schemes the pullback along `e` is the extension by zero along its inverse,
`e^* ≅ (e⁻¹)_!`.

## Main definitions

- `AlgebraicGeometry.Etale.openImmersionLowerShriekComp`: `(j' ≫ j)_! ≅ j'_! ⋙ j_!`.
- `AlgebraicGeometry.Etale.upperStarIsoOpenImmersionLowerShriekInv`: `e^* ≅ (e⁻¹)_!` for an
  isomorphism `e`.

-/

@[expose] public section

universe u' u

open CategoryTheory

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [HasSmallSiteSheafify A]

/-- The composition isomorphism of extensions by zero along open immersions `j' : V ⟶ U` and
`j : U ⟶ X`:
```
Sh(V) --j'_!--> Sh(U)
     \            |
 (j' ≫ j)_!       | j_!
       \          v
        -----> Sh(X)
```
-/
noncomputable def Etale.openImmersionLowerShriekComp {V U X : Scheme.{u}} (j' : V ⟶ U)
    (j : U ⟶ X) [IsOpenImmersion j'] [IsOpenImmersion j] :
    (j' ≫ j)_!open[A] ≅ (j')_!open[A] ⋙ (j)_!open[A] :=
  -- both are left adjoint to `(j' ≫ j)^* ≅ j^* ⋙ j'^*`
  (Etale.openImmersionLowerShriekUpperStarAdjunction A (j' ≫ j)).leftAdjointUniq
    (((Etale.openImmersionLowerShriekUpperStarAdjunction A j').comp
        (Etale.openImmersionLowerShriekUpperStarAdjunction A j)).ofNatIsoRight
      (Etale.upperStarComp A j' j).symm)

/-- The pullback along an isomorphism `e : U ≅ U'` of schemes is the extension by zero along
its inverse: `e^* ≅ (e⁻¹)_!` as functors `Sh(U') ⥤ Sh(U)`. -/
noncomputable def Etale.upperStarIsoOpenImmersionLowerShriekInv {U U' : Scheme.{u}}
    (e : U ≅ U') : (e.hom)^*[A] ≅ (e.inv)_!open[A] :=
  -- both are left adjoint to `(e⁻¹)^* ≅ e_*`
  (Etale.upperStarLowerStarAdjunction A e.hom).leftAdjointUniq
    ((Etale.openImmersionLowerShriekUpperStarAdjunction A e.inv).ofNatIsoRight
      (Etale.upperStarInvIsoLowerStarHom A e))

end AlgebraicGeometry
