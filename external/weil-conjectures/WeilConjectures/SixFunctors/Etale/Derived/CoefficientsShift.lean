/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# Shifts of coefficient objects

The coefficient-side properties of `D(X_ét, Λ)` are stable under shifts: a shift of an
invertible object is invertible, a shift moves the Tor amplitude by the same amount, and
`D^b_{ctf}(X, Λ)` is stable under shifts. Invertibility is also invariant under isomorphism.
This is what lets twisted and shifted objects such as `Λ_X(m)[2m]` be fed to the statements of
the purity chapter.

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.of_iso`
- `AlgebraicGeometry.Etale.DerivedCategory.isInvertible.shift`
- `AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn.shift`
- `AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleFiniteTor.shift`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}}

/-- Invertibility is invariant under isomorphism. -/
theorem DerivedCategory.isInvertible.of_iso
    {L L' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (e : L ≅ L') (hL : DerivedCategory.isInvertible Λ X L) :
    DerivedCategory.isInvertible Λ X L' := by
  obtain ⟨M, ⟨h⟩, ⟨h'⟩⟩ := hL
  exact ⟨M, ⟨((derivedTensor (ModuleCat.{u + 1} Λ) X).mapIso e.symm).app M ≪≫ h⟩,
    ⟨((derivedTensor (ModuleCat.{u + 1} Λ) X).obj M).mapIso e.symm ≪≫ h'⟩⟩

/-- A shift of an invertible object is invertible: `L⟦n⟧ ⊗ᴸ M⟦-n⟧ ≅ (L ⊗ᴸ M)⟦0⟧`, and
symmetrically. -/
theorem DerivedCategory.isInvertible.shift
    {L : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : DerivedCategory.isInvertible Λ X L) (n : ℤ) :
    DerivedCategory.isInvertible Λ X (L⟦n⟧) := by
  obtain ⟨M, ⟨h⟩, ⟨h'⟩⟩ := hL
  exact ⟨M⟦-n⟧, ⟨derivedTensorShiftIso _ L M n (-n) ≪≫ (shiftFunctor _ _).mapIso h ≪≫
    (shiftFunctorZero' _ (n + -n) (by lia)).app _⟩,
    ⟨derivedTensorShiftIso _ M L (-n) n ≪≫ (shiftFunctor _ _).mapIso h' ≪≫
    (shiftFunctorZero' _ (-n + n) (by lia)).app _⟩⟩

/-- Shifting moves the Tor amplitude: if `K` has Tor amplitude in `[a, b]`, then `K⟦n⟧` has
Tor amplitude in `[a - n, b - n]`. -/
theorem DerivedCategory.torAmplitudeIn.shift
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} {a b : ℤ}
    (hK : DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X a b K) (n : ℤ) :
    DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) X (a - n) (b - n) (K⟦n⟧) := by
  intro F
  obtain ⟨h₁, h₂⟩ := hK F
  set F' := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  let e : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (K⟦n⟧)).obj F' ≅
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj F')⟦n⟧ :=
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj F').commShiftIso n).app K
  have : _root_.DerivedCategory.TStructure.t.IsGE
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj F') a := h₁
  have : _root_.DerivedCategory.TStructure.t.IsLE
      (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj F') b := h₂
  have := _root_.DerivedCategory.TStructure.t.isGE_shift
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj F') a n (a - n)
  have := _root_.DerivedCategory.TStructure.t.isLE_shift
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj F') b n (b - n)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso e.symm _,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso e.symm _⟩

/-- `D^b_{ctf}(X, Λ)` is stable under shifts. -/
theorem DerivedCategory.boundedConstructibleFiniteTor.shift
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (n : ℤ) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X (K⟦n⟧) := by
  obtain ⟨hb, a, b, hab⟩ := hK
  exact ⟨(Etale.DerivedCategory.boundedConstructible _ X).le_shift n K hb, a - n, b - n,
    DerivedCategory.torAmplitudeIn.shift hab n⟩

end Etale

end AlgebraicGeometry
