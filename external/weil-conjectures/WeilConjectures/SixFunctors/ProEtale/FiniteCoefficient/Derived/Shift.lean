/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-!
# Compatibility of the pro-étale derived functors with shifts, and their additivity

The derived pullback, pushforward and lower shriek on the unbounded derived categories of
pro-étale sheaves commute with the shift functors, and `Dᵇctf(X, A)` is stable under shifts:

* `Rg_*` commutes with shifts as every right derived functor does;
* `Lg^*` is left adjoint to `Rg_*` (`ProEtale.derivedUpperStarLowerStarAdjunction`), so it
  inherits the structure by `Adjunction.leftAdjointCommShift`, compatibly with the adjunction;
* `Rf_! = D(i_!) ⋙ R(g_*)` for the chosen compactification `(i, g)` is a composite of two
  functors commuting with shifts.

The three functors are additive: `Lg^*` is isomorphic to the functor `D(g^*)` induced by the
exact pullback, and `Rf_!` is a composite of additive functors.

## Main definitions

- `AlgebraicGeometry.ProEtale.commShiftLeftDerivedUpperStar`
- `AlgebraicGeometry.ProEtale.commShiftRightDerivedLowerShriek`

## Main results

- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor.shift`: `Dᵇctf(X, A)` is
  stable under shifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived pullback `Lg^*` commutes with shifts: it is left adjoint to the total right
derived pushforward `Rg_*` (`ProEtale.derivedUpperStarLowerStarAdjunction`), which does, as
every right derived functor does. -/
noncomputable instance commShiftLeftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).CommShift ℤ :=
  (derivedUpperStarLowerStarAdjunction A g).leftAdjointCommShift ℤ

/-- The adjunction `Lg^* ⊣ Rg_*` is compatible with the commutation of both functors with the
shifts. -/
instance commShift_derivedUpperStarLowerStarAdjunction {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
  (derivedUpperStarLowerStarAdjunction A g).commShift_of_rightAdjoint ℤ

/-- The derived lower shriek `Rf_!` commutes with shifts: for the chosen compactification
`(i, g)` of `f` it is the composite of the functor `D(i_!)` induced by the exact extension by
zero and of the right derived pushforward `Rg_*`. -/
noncomputable instance commShiftRightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)_![A]).CommShift ℤ :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).CommShift ℤ)

/-- The derived pullback `Lg^*` is additive, being isomorphic to the functor `D(g^*)` induced by
the exact pullback. -/
instance additive_leftDerivedUpperStar {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (L((g)^*[A])).Additive :=
  Functor.additive_of_iso (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

/-- The derived lower shriek `Rf_! = D(i_!) ⋙ R(g_*)` is additive. -/
instance additive_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] : (R(f)_![A]).Additive :=
  inferInstanceAs ((D(((HasCompactification.compactification f).i)_!open[A]) ⋙
    R(((HasCompactification.compactification f).g)_*[A])).Additive)

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

variable {A} {X : Scheme.{u}}

/-- Shifting moves the Tor amplitude: if `K` has Tor amplitude in `[a, b]`, then `K⟦n⟧` has
Tor amplitude in `[a - n, b - n]`. -/
lemma DerivedCategory.torAmplitudeIn.shift
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)} {a b : ℤ}
    (hK : DerivedCategory.torAmplitudeIn A X a b K) (n : ℤ) :
    DerivedCategory.torAmplitudeIn A X (a - n) (b - n) (K⟦n⟧) := by
  intro F
  obtain ⟨h₁, h₂⟩ := hK F
  set F' := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let e : K⟦n⟧ ⊗ F' ≅ (K ⊗ F')⟦n⟧ :=
    (((curriedTensor _).flip.obj F').commShiftIso n).app K
  have := _root_.DerivedCategory.TStructure.t.isGE_shift (K ⊗ F') a n (a - n)
  have := _root_.DerivedCategory.TStructure.t.isLE_shift (K ⊗ F') b n (b - n)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm _,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm _⟩

omit [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] in
/-- Being bounded constructible is stable under shifts. -/
lemma DerivedCategory.boundedConstructible.shift
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.boundedConstructible A X K) (n : ℤ) :
    DerivedCategory.boundedConstructible A X (K⟦n⟧) := by
  obtain ⟨K', hK', ⟨e⟩⟩ := (DerivedCategory.boundedConstructible_iff A X K).1 hK
  exact (DerivedCategory.boundedConstructible_iff A X _).2 ⟨K'⟦n⟧,
    (Etale.DerivedCategory.boundedConstructible _ X).le_shift n _ hK',
    ⟨((D(ν^*(X)[A])).commShiftIso n).app K' ≪≫ (shiftFunctor _ n).mapIso e⟩⟩

/-- `Dᵇctf(X, A)` is stable under shifts. -/
lemma DerivedCategory.constructibleFiniteTor.shift
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) (n : ℤ) :
    DerivedCategory.constructibleFiniteTor A X (K⟦n⟧) := by
  obtain ⟨hb, a, b, hab⟩ := hK
  exact ⟨DerivedCategory.boundedConstructible.shift hb n, a - n, b - n,
    DerivedCategory.torAmplitudeIn.shift hab n⟩

end ProEtale

end AlgebraicGeometry
