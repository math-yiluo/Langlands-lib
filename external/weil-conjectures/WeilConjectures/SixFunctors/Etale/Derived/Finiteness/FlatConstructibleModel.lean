/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel

/-!
# Flat constructible models of objects of `D^b_{ctf}`

Every object of `D^b_{ctf}(X, Λ)` (bounded, constructible cohomology, finite Tor amplitude), for
`X` Noetherian and `Λ` finite, is represented by a bounded complex of flat constructible sheaves
(blueprint `lemma-flat-models-generators`).

## Main statements (in `AlgebraicGeometry.Etale.DerivedCategory`)

- `exists_flatConstructibleModel_of_boundedConstructibleFiniteTor`
- `exists_flatConstructibleModel_of_locallyOfFiniteType`
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale.DerivedCategory

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- An object of finite Tor amplitude has Tor amplitude in some interval `[a, b]` with
`a ≤ b`, in the sense of `AlgebraicGeometry.Etale.DerivedCategory.hasTorAmplitudeIn`. -/
lemma exists_le_hasTorAmplitudeIn_of_finiteTorAmplitude {X : Scheme.{u}}
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : finiteTorAmplitude (ModuleCat.{u + 1} Λ) X K) :
    ∃ a b : ℤ, a ≤ b ∧ hasTorAmplitudeIn Λ X a b K := by
  obtain ⟨a, b, h⟩ := hK
  exact ⟨min a b, b, min_le_right a b, hasTorAmplitudeIn_iff_torAmplitudeIn.2
    (torAmplitudeIn.mono (min_le_left a b) le_rfl h)⟩

/-- **Flat constructible models** (blueprint `lemma-flat-models-generators`): on a Noetherian
scheme, with finite coefficients, an object of `D^b_{ctf}(X, Λ)` is represented by a bounded complex
of flat constructible sheaves. -/
theorem exists_flatConstructibleModel_of_boundedConstructibleFiniteTor {X : Scheme.{u}}
    [Finite Λ] [IsNoetherian X]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : boundedConstructibleFiniteTor Λ X K) :
    ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
      (∃ a b, IsBoundedFlatComplex Λ a b P) ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ _root_.DerivedCategory.Q.obj P) := by
  obtain ⟨a, b, hab, h⟩ := exists_le_hasTorAmplitudeIn_of_finiteTorAmplitude hK.2
  obtain ⟨P, hP, hPc, he⟩ :=
    (hasTorAmplitudeIn_iff_exists_flatConstructibleModel Λ a b hab K hK.1).1 h
  exact ⟨P, ⟨a, b, hP⟩, hPc, he⟩

/-- **Flat constructible models** over a quasi-compact scheme locally of finite type over a
field: such a scheme is Noetherian, so
`exists_flatConstructibleModel_of_boundedConstructibleFiniteTor` applies. -/
theorem exists_flatConstructibleModel_of_locallyOfFiniteType {k : Type u} [Field k]
    [Finite Λ] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [CompactSpace X]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : boundedConstructibleFiniteTor Λ X K) :
    ∃ P : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ,
      (∃ a b, IsBoundedFlatComplex Λ a b P) ∧ (∀ q : ℤ, IsConstructibleSheaf (P.X q)) ∧
        Nonempty (K ≅ _root_.DerivedCategory.Q.obj P) := by
  have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian f }
  exact exists_flatConstructibleModel_of_boundedConstructibleFiniteTor K hK

end AlgebraicGeometry.Etale.DerivedCategory
