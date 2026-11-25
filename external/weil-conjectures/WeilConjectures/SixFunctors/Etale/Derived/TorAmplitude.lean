/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

/-!

# Finite Tor amplitude and the small category `Dctf(X, A)`

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_ét)` of `A`-valued étale sheaves on `X` carries the derived tensor product
`- ⊗ᴸ -` of `WeilConjectures.SixFunctors.Etale.Derived.Tensor` and the bounded constructible
subcategory `Dᵇc(X, A)` of `WeilConjectures.CategoryTheory.DerivedCategory.Constructible`.

This file cuts out the *small* category on which the six operations of the `ℓ`-adic formalism
are typed: the bounded constructible complexes of finite Tor amplitude.

## Main definitions

- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`, tested by
  tensoring with an arbitrary étale sheaf.
- `AlgebraicGeometry.Etale.DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleFiniteTor`: membership in `Dctf(X, A)`,
  as an object property.
- `AlgebraicGeometry.Etale.DerivedCategory.constructibleTorAmplitudeIn`: membership in
  `D_c^[a, b](X, A)` together with Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor`: the category `Dctf(X, A)` of bounded
  constructible complexes of finite Tor amplitude.

## Implementation notes

Neither homology concentration in an interval nor Tor amplitude is an étale notion, and neither
is defined here: they are `DerivedCategory.homologyConcentratedIn` of
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure`, phrased through the
canonical t-structure so that the t-structure API applies to it, and
`DerivedCategory.torAmplitudeIn` of `WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`,
for the derived tensor product. The definitions below specialise them to `D(X_ét)`.

The blueprint's second small category `D_c^[a, b](X, A)` is
`AlgebraicGeometry.Etale.DerivedCategoryConstructibleIn` of
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible`. The statements that speak about
it — those of `WeilConjectures.SixFunctors.Etale.Derived.Stability` — always pair it with a Tor
amplitude bound, and use the object property
`AlgebraicGeometry.Etale.DerivedCategory.constructibleTorAmplitudeIn`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable (X : Scheme.{u})

namespace Etale.DerivedCategory

/-- An object `M` of `D(X_ét)` has *Tor amplitude in `[a, b]`* if for every étale sheaf `F` the
derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]`. -/
abbrev torAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.torAmplitudeIn _ a b

variable {A X}

/-- Widening the interval preserves Tor amplitude. -/
lemma torAmplitudeIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (hM : torAmplitudeIn A X a b M) : torAmplitudeIn A X a' b' M :=
  _root_.DerivedCategory.torAmplitudeIn.mono ha hb hM

variable (A X)

/-- An object of `D(X_ét)` has *finite Tor amplitude* if it has Tor amplitude in some
interval `[a, b]`. -/
abbrev finiteTorAmplitude :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  _root_.DerivedCategory.finiteTorAmplitude _

end Etale.DerivedCategory

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

namespace Etale

/-- Membership in `Dctf(X, A)` as an object property of `D(X_ét)`: bounded constructible and of
finite Tor amplitude. -/
noncomputable def DerivedCategory.constructibleFiniteTor :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Etale.DerivedCategory.boundedConstructible A X ⊓ Etale.DerivedCategory.finiteTorAmplitude A X

lemma DerivedCategory.constructibleFiniteTor_iff
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.constructibleFiniteTor A X K ↔
      Etale.DerivedCategory.boundedConstructible A X K ∧
        Etale.DerivedCategory.finiteTorAmplitude A X K :=
  Iff.rfl

/-- Membership in the blueprint's `D_c^[a, b](X, A)` together with Tor amplitude in the same
interval, as an object property of `D(X_ét)`: bounded constructible, homology concentrated in
`[a, b]`, and Tor amplitude in `[a, b]`. -/
noncomputable def DerivedCategory.constructibleTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :=
  Etale.DerivedCategory.boundedConstructible A X ⊓
    _root_.DerivedCategory.homologyConcentratedIn a b ⊓
    Etale.DerivedCategory.torAmplitudeIn A X a b

lemma DerivedCategory.constructibleTorAmplitudeIn_iff (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    DerivedCategory.constructibleTorAmplitudeIn A X a b K ↔
      (Etale.DerivedCategory.boundedConstructible A X K ∧
          _root_.DerivedCategory.homologyConcentratedIn a b K) ∧
        Etale.DerivedCategory.torAmplitudeIn A X a b K :=
  Iff.rfl

/-- `D_c^[a, b](X, A)` with Tor amplitude in `[a, b]` is the intersection of
`Etale.DerivedCategory.constructibleIn` and `Etale.DerivedCategory.torAmplitudeIn`. -/
lemma DerivedCategory.constructibleTorAmplitudeIn_eq (a b : ℤ) :
    DerivedCategory.constructibleTorAmplitudeIn A X a b =
      DerivedCategory.constructibleIn A X a b ⊓ DerivedCategory.torAmplitudeIn A X a b :=
  rfl

variable {A X}

/-- An object of `D(X_ét)` lies in `Dctf(X, A)` exactly when, for some interval `[a, b]`, it
is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`. -/
lemma DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (∃ a b : ℤ, DerivedCategory.constructibleTorAmplitudeIn A X a b K) ↔
      DerivedCategory.constructibleFiniteTor A X K :=
  _root_.DerivedCategory.exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff
    (fun _ hK ↦ hK.1) K

variable (A X)

/-- Blueprint `definition-constructible-sheaves`: Ambient categories and small subcategories.

The small category `Dctf(X, A)` of bounded constructible complexes of finite Tor amplitude, as
a full subcategory of `D(X_ét)`. It is the category on which the six operations of the
`ℓ`-adic formalism are typed. -/
noncomputable def DerivedCategoryFiniteTor : Type _ :=
  (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

noncomputable instance : Category (DerivedCategoryFiniteTor A X) :=
  inferInstanceAs <| Category (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

/-- The inclusion of `Dctf(X, A)` into the derived category of étale sheaves. -/
noncomputable def DerivedCategoryFiniteTor.ι :
    DerivedCategoryFiniteTor A X ⥤ _root_.DerivedCategory (Sheaf X.smallEtaleTopology A) :=
  (DerivedCategory.constructibleFiniteTor A X).ι

/-- The inclusion `Dctf(X, A) ⊆ Dᵇc(X, A)` of blueprint `definition-constructible-sheaves`. -/
noncomputable def DerivedCategoryFiniteTor.toBoundedConstructible :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryBoundedConstructible A X :=
  ObjectProperty.ιOfLE inf_le_left

@[inherit_doc DerivedCategoryFiniteTor]
scoped notation "Dctf(" X ", " A ")" => Etale.DerivedCategoryFiniteTor A X

end Etale

end AlgebraicGeometry
