/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek

/-!
# Compatibility of the derived six functors with shifts

The derived pullback, pushforward, lower shriek and exceptional inverse image on the
unbounded derived categories of étale sheaves commute with the shift functors. This file
equips each of them with its `CategoryTheory.Functor.CommShift` structure:

* `D(g^*)` is the functor induced by an exact functor, so it commutes with shifts by
  Mathlib's `Functor.mapDerivedCategory` instance;
* `Rg_*` is right adjoint to `D(g^*)` (`Etale.mapDerivedUpperStarLowerStarAdjunction`), so it
  inherits the structure by `Adjunction.rightAdjointCommShift`;
* `Lg^*` is isomorphic to `D(g^*)` (`Etale.leftDerivedUpperStarIsoMapDerivedCategory`);
* `Rf_! = D(i_!) ⋙ R(g_*)` for the chosen compactification `(i, g)` is a composite of two
  functors commuting with shifts;
* `Rf^!` is right adjoint to `Rf_!` (`Etale.rightDerivedUpperShriekAdjunction`);
* the derived tensor product `K ⊗ᴸ -` and `- ⊗ᴸ K` is the tensor product of the monoidal
  derived category, which commutes with shifts in each variable
  (`DerivedCategory.commShiftTensorLeft`).

These are what make the boundary of the supported localization triangle and the cup
product with supports compatible with the degree shifts in which cohomology classes live.

## Main definitions

- `AlgebraicGeometry.Etale.commShiftRightDerivedLowerStar`
- `AlgebraicGeometry.Etale.commShiftLeftDerivedUpperStar`
- `AlgebraicGeometry.Etale.commShiftRightDerivedLowerShriek`
- `AlgebraicGeometry.Etale.commShiftRightDerivedUpperShriek`
- `AlgebraicGeometry.Etale.commShiftDerivedTensorObj`,
  `AlgebraicGeometry.Etale.commShiftDerivedTensorFlipObj`
- `AlgebraicGeometry.Etale.derivedTensorShiftIso`: `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧`.
- `AlgebraicGeometry.Etale.derivedTensorRightShiftIso`: `M ⊗ᴸ K⟦a⟧ ≅ (M ⊗ᴸ K)⟦a⟧`, naturally
  in `M`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The total right derived pushforward `Rg_*` commutes with shifts: it is right adjoint to the
functor `D(g^*)` induced by the exact pullback, which does. -/
noncomputable instance commShiftRightDerivedLowerStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (R((g)_*[A])).CommShift ℤ :=
  (mapDerivedUpperStarLowerStarAdjunction A g).rightAdjointCommShift ℤ

/-- The derived lower shriek `Rf_!` commutes with shifts: for the chosen compactification
`(i, g)` of `f` it is the composite of the functor `D(i_!)` induced by the exact extension by
zero and of the right derived pushforward `Rg_*`. -/
noncomputable instance commShiftRightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)_![A]).CommShift ℤ :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).CommShift ℤ)

/-- The exceptional inverse image `Rf^!` commutes with shifts, being right adjoint to `Rf_!`. -/
noncomputable instance commShiftRightDerivedUpperShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)^![Λ]).CommShift ℤ :=
  (rightDerivedUpperShriekAdjunction Λ f).rightAdjointCommShift ℤ

/-- A right adjoint of `Rf_!` (for instance `Rf^!` at integral coefficients, where it is only
assumed to exist) commutes with shifts, being right adjoint to `Rf_!`. -/
noncomputable instance commShiftRightAdjointRightDerivedLowerShriek {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint] :
    (R(f)_![A]).rightAdjoint.CommShift ℤ :=
  (Adjunction.ofIsLeftAdjoint (R(f)_![A])).rightAdjointCommShift ℤ

section Monoidal

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` commutes with shifts, being isomorphic to the functor `D(g^*)`
induced by the exact pullback (`Etale.leftDerivedUpperStarIsoMapDerivedCategory`). -/
noncomputable instance commShiftLeftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).CommShift ℤ :=
  Functor.CommShift.ofIso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ

variable {X : Scheme.{u}}

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring on the left with a fixed complex, `M ↦ K ⊗ᴸ M`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorObj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).obj K).CommShift ℤ)

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring on the right with a fixed complex, `M ↦ M ⊗ᴸ K`, commutes with shifts. -/
noncomputable instance commShiftDerivedTensorFlipObj
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    ((derivedTensor A X).flip.obj K).CommShift ℤ :=
  inferInstanceAs
    (((curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))).flip.obj K).CommShift ℤ)

/-- The derived tensor product of shifted complexes, `K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧`: the shift
is first moved out of the left factor, then out of the right one.

```
K⟦a⟧ ⊗ᴸ M⟦b⟧ ≅ (K ⊗ᴸ M⟦b⟧)⟦a⟧ ≅ ((K ⊗ᴸ M)⟦b⟧)⟦a⟧ ≅ (K ⊗ᴸ M)⟦a + b⟧
```

No sign convention is involved in the construction; the two orders of moving the shifts out
differ by the sign `(-1)^{ab}`. -/
noncomputable def derivedTensorShiftIso (K M : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (a b : ℤ) :
    ((derivedTensor A X).obj (K⟦a⟧)).obj (M⟦b⟧) ≅ (((derivedTensor A X).obj K).obj M)⟦a + b⟧ :=
  (((derivedTensor A X).flip.obj (M⟦b⟧)).commShiftIso a).app K ≪≫
    (shiftFunctor _ a).mapIso ((((derivedTensor A X).obj K).commShiftIso b).app M) ≪≫
      ((shiftFunctorAdd' _ b a (a + b) (add_comm b a)).app _).symm

attribute [local instance] Sheaf.monoidalCategory in
/-- Tensoring with a shifted complex shifts the tensor product, `M ⊗ᴸ K⟦a⟧ ≅ (M ⊗ᴸ K)⟦a⟧`,
naturally in `M`. The components are the commutation of `M ⊗ᴸ -` with the shift
(`AlgebraicGeometry.Etale.commShiftDerivedTensorObj`); they are natural in `M` because the
derived tensor product commutes with shifts as a bifunctor
(`DerivedCategory.commShift₂CurriedTensor`). -/
noncomputable def derivedTensorRightShiftIso
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) (a : ℤ) :
    derivedTensorRight A X (K⟦a⟧) ≅ derivedTensorRight A X K ⋙ shiftFunctor _ a :=
  NatIso.ofComponents (fun M ↦ (((derivedTensor A X).obj M).commShiftIso a).app K)
    (fun f ↦
      have : NatTrans.CommShift ((derivedTensor A X).map f) ℤ :=
        Functor.CommShift₂.commShift_map (h := .int)
          (G := curriedTensor (DerivedCategory (Sheaf X.smallEtaleTopology A))) f
      (NatTrans.shift_app_comm ((derivedTensor A X).map f) a K).symm)

end Monoidal

end Etale

end AlgebraicGeometry
