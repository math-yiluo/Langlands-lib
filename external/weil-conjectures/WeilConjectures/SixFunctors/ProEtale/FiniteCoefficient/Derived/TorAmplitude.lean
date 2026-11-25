/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!

# Finite Tor amplitude and the small category `Dctf(X, A)` on the pro-étale site

Let `A` be a monoidal Grothendieck abelian coefficient category and `X` a scheme, so that the
derived category `D(X_proét)` of `A`-valued pro-étale sheaves on `X` carries the derived tensor
product `- ⊗ᴸ -` of `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor` and the
bounded constructible objects of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible`.

This file is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`: it cuts out the small category of
bounded constructible complexes of finite Tor amplitude.

## Main definitions

- `AlgebraicGeometry.ProEtale.DerivedCategory.torAmplitudeIn`: Tor amplitude in `[a, b]`,
  tested by tensoring with an arbitrary pro-étale sheaf.
- `AlgebraicGeometry.ProEtale.DerivedCategory.finiteTorAmplitude`: finite Tor amplitude.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleFiniteTor`: membership in
  `Dctf(X, A)`, as an object property.
- `AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTorAmplitudeIn`: membership in
  `D_c^[a, b](X, A)` together with Tor amplitude in `[a, b]`.
- `AlgebraicGeometry.ProEtale.DerivedCategoryFiniteTor`: the category `Dctf(X, A)` of bounded
  constructible pro-étale complexes of finite Tor amplitude.

## Implementation notes

As on the étale side, Tor amplitude is the site-independent `DerivedCategory.torAmplitudeIn` of
`WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude`, specialised to `D(X_proét)`.

The blueprint's second small category `D_c^[a, b](X, A)` is
`AlgebraicGeometry.ProEtale.DerivedCategoryConstructibleIn` of
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Constructible`. The statements that
speak about it always pair it with a Tor amplitude bound, and use the object property
`AlgebraicGeometry.ProEtale.DerivedCategory.constructibleTorAmplitudeIn` (see the note in
`WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude`).

Bounded constructibility is étale origin
(`AlgebraicGeometry.ProEtale.DerivedCategory.boundedConstructible`), which is the right notion
only at the finite coefficient stages; so is `Dctf(X, A)`.

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

namespace ProEtale.DerivedCategory

/-- Blueprint `definition-constructible-sheaves`: Finite Tor amplitude, the amplitude condition.

An object `M` of `D(X_proét)` has *Tor amplitude in `[a, b]`* if for every pro-étale sheaf
`F` the derived tensor product `M ⊗ᴸ F` has homology concentrated in `[a, b]`. -/
abbrev torAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  _root_.DerivedCategory.torAmplitudeIn _ a b

variable {A X}

/-- Widening the interval preserves Tor amplitude. -/
lemma torAmplitudeIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {M : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hM : torAmplitudeIn A X a b M) : torAmplitudeIn A X a' b' M :=
  _root_.DerivedCategory.torAmplitudeIn.mono ha hb hM

variable (A X)

/-- An object of `D(X_proét)` has *finite Tor amplitude* if it has Tor amplitude in some
interval `[a, b]`. -/
abbrev finiteTorAmplitude :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  _root_.DerivedCategory.finiteTorAmplitude _

end ProEtale.DerivedCategory

variable {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA]

namespace ProEtale

/-- Blueprint `definition-constructible-sheaves`: Finite Tor amplitude, the category
`Dᵇctf(Y, A)` at the finite stages.

Membership in `Dctf(X, A)` as an object property of `D(X_proét)`: bounded constructible and
of finite Tor amplitude. Since bounded constructibility is étale origin, this is the blueprint's
`Dctf(X, A)` only at the finite coefficient stages. -/
noncomputable def DerivedCategory.constructibleFiniteTor :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.boundedConstructible A X ⊓ DerivedCategory.finiteTorAmplitude A X

/-- Being bounded constructible of finite Tor amplitude is invariant under isomorphism. -/
instance : (DerivedCategory.constructibleFiniteTor A X).IsClosedUnderIsomorphisms :=
  have : (DerivedCategory.finiteTorAmplitude A X).IsClosedUnderIsomorphisms :=
    ⟨fun e ⟨a, b, h⟩ ↦ ⟨a, b, (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso e h⟩⟩
  inferInstanceAs (DerivedCategory.boundedConstructible A X ⊓
    DerivedCategory.finiteTorAmplitude A X).IsClosedUnderIsomorphisms

variable {A X} in
/-- A bounded constructible complex of finite Tor amplitude is bounded below of étale
origin. -/
lemma DerivedCategory.constructibleFiniteTor.plusEtaleOrigin
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    DerivedCategory.plusEtaleOrigin A X K :=
  hK.1.plusEtaleOrigin

variable {A X} in
/-- A bounded constructible complex of finite Tor amplitude is bounded below. -/
lemma DerivedCategory.constructibleFiniteTor.plus
    {K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K) :
    _root_.DerivedCategory.TStructure.t.plus K :=
  hK.plusEtaleOrigin.plus

/-- Unfolding of `DerivedCategory.constructibleFiniteTor`. -/
lemma DerivedCategory.constructibleFiniteTor_iff
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory.constructibleFiniteTor A X K ↔
      DerivedCategory.boundedConstructible A X K ∧ DerivedCategory.finiteTorAmplitude A X K :=
  Iff.rfl

/-- Membership in the blueprint's `D_c^[a, b](X, A)` together with Tor amplitude in the same
interval, as an object property of `D(X_proét)`: bounded constructible, homology concentrated
in `[a, b]`, and Tor amplitude in `[a, b]`. -/
noncomputable def DerivedCategory.constructibleTorAmplitudeIn (a b : ℤ) :
    ObjectProperty (_root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :=
  DerivedCategory.boundedConstructible A X ⊓
    _root_.DerivedCategory.homologyConcentratedIn a b ⊓
    DerivedCategory.torAmplitudeIn A X a b

/-- Unfolding of `DerivedCategory.constructibleTorAmplitudeIn`. -/
lemma DerivedCategory.constructibleTorAmplitudeIn_iff (a b : ℤ)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    DerivedCategory.constructibleTorAmplitudeIn A X a b K ↔
      (DerivedCategory.boundedConstructible A X K ∧
          _root_.DerivedCategory.homologyConcentratedIn a b K) ∧
        DerivedCategory.torAmplitudeIn A X a b K :=
  Iff.rfl

/-- `D_c^[a, b](X, A)` with Tor amplitude in `[a, b]` is the intersection of
`ProEtale.DerivedCategory.constructibleIn` and `ProEtale.DerivedCategory.torAmplitudeIn`. -/
lemma DerivedCategory.constructibleTorAmplitudeIn_eq (a b : ℤ) :
    DerivedCategory.constructibleTorAmplitudeIn A X a b =
      DerivedCategory.constructibleIn A X a b ⊓ DerivedCategory.torAmplitudeIn A X a b :=
  rfl

variable {A X}

/-- An object of `D(X_proét)` lies in `Dctf(X, A)` exactly when, for some interval `[a, b]`,
it is bounded constructible with homology concentrated in `[a, b]` and Tor amplitude in
`[a, b]`. -/
lemma DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A)) :
    (∃ a b : ℤ, DerivedCategory.constructibleTorAmplitudeIn A X a b K) ↔
      DerivedCategory.constructibleFiniteTor A X K :=
  _root_.DerivedCategory.exists_inf_homologyConcentratedIn_inf_torAmplitudeIn_iff
    (fun _ hK ↦ hK.bounded) K

variable (A X)

/-- Blueprint `definition-constructible-sheaves`: Ambient categories and small subcategories.

The small category `Dctf(X, A)` of bounded constructible pro-étale complexes of finite Tor
amplitude, as a full subcategory of `D(X_proét)`. -/
noncomputable def DerivedCategoryFiniteTor : Type _ :=
  (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

/-- The category structure on `Dctf(X, A)`, inherited from `D(X_proét)`. -/
noncomputable instance : Category (DerivedCategoryFiniteTor A X) :=
  inferInstanceAs <| Category (DerivedCategory.constructibleFiniteTor A X).FullSubcategory

/-- The inclusion of `Dctf(X, A)` into the derived category of pro-étale sheaves. -/
noncomputable def DerivedCategoryFiniteTor.ι :
    DerivedCategoryFiniteTor A X ⥤ _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) A) :=
  (DerivedCategory.constructibleFiniteTor A X).ι

/-- The inclusion `Dctf(X, A) ⊆ Dᵇc(X, A)` of blueprint `definition-constructible-sheaves`. -/
noncomputable def DerivedCategoryFiniteTor.toBoundedConstructible :
    DerivedCategoryFiniteTor A X ⥤ DerivedCategoryBoundedConstructible A X :=
  ObjectProperty.ιOfLE inf_le_left

@[inherit_doc DerivedCategoryFiniteTor]
scoped notation "Dctf(" X ", " A ")" => ProEtale.DerivedCategoryFiniteTor A X

end ProEtale

end AlgebraicGeometry
