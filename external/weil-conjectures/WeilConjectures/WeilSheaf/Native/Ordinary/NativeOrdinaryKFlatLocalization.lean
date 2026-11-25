/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Weil.NativeWeilClosedModels
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement

/-! # Ordinary K-flat complexes and the localization tensorator

Source: Stacks 06YN, 06YU.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option linter.style.haveILetI false

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] DerivedCategory DerivedCategory.Q
  instCategoryDerivedCategory NativeOrdinaryKFlat

/-- Ordinary total-tensor K-flatness gives canonical homotopy K-flatness.
Source: Stacks 06YN, 06YU
(blueprint: lem-sf-native-ordinary-kflat-localization).
Proof: transport acyclicity along the specified total comparison and apply the
acyclic-complex criterion for homotopy K-flatness. -/
theorem nativeOrdinaryKFlat_homotopy (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P)
    (P : CochainComplex (ProEtale.AdicSheaf l Y) ℤ) (hP : NativeOrdinaryKFlat l Y P) :
    (HomotopyCategory.quasiIso _ (.up ℤ)).kFlat
      ((HomotopyCategory.quotient _ _).obj P) := by
  apply RingedDerivedNative.kFlat_of_acyclic P
  unfold NativeOrdinaryKFlat at hP
  intro N hN n
  exact (hP N hN n).of_iso (κ P N)

/-- The canonical localization tensorator is invertible on ordinary K-flat pairs.
Source: Stacks 06YU
(blueprint: lem-sf-native-ordinary-kflat-localization).
Proof: apply the localization tensorator theorem to the preceding conversion
of either K-flat factor. -/
theorem nativeOrdinaryKFlat_isIso_mu (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    (κ : ∀ P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ,
      ordinaryTensorTotal l Y P Q ≅ Q ⊗ P)
    (P Q : CochainComplex (ProEtale.AdicSheaf l Y) ℤ)
    (h : NativeOrdinaryKFlat l Y P ∨ NativeOrdinaryKFlat l Y Q) :
    IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) :=
  RingedDerivedNative.localization_isIso_mu P Q
    (h.imp (nativeOrdinaryKFlat_homotopy l Y κ P)
      (nativeOrdinaryKFlat_homotopy l Y κ Q))

end AlgebraicGeometry.ProEtaleWeilSheaf
