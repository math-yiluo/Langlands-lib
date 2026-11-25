/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingCoherenceData
import WeilConjectures.PoincareDuality.PodReindexingCoherence.PodReindexingShiftDerivedDescent

/-! # Derived part of signed shift laws for reindexing comparisons

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

The localization square is isolated from the representative chain square.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodReindexingCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The derived localization square required by `ShiftLaws`. -/
def DerivedShiftPart {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) : Prop :=
  ∀ (M N : podReindexingDerived l E Y s) (a b : ℤ),
    c.derived.hom.app (op (M⟦a⟧), N⟦b⟧) ≫
      (podReindexingDerivedHom l E X s).map
        (Prod.mkHom (((podReindexingDerivedFunctor l E g s).commShiftIso a).inv.app M).op
          (((podReindexingDerivedFunctor l E g s).commShiftIso b).hom.app N)) ≫
      (signedShift l E X s ((podReindexingDerivedFunctor l E g s).obj M)
        ((podReindexingDerivedFunctor l E g s).obj N) a b).hom =
      (podReindexingDerivedFunctor l E g s).map (signedShift l E Y s M N a b).hom ≫
        ((podReindexingDerivedFunctor l E g s).commShiftIso (b-a)).hom.app
          ((podReindexingDerivedHom l E Y s).obj (op M, N)) ≫
        (c.derived.hom.app (op M, N))⟦b-a⟧'

/-- Prove the normalized derived square for supplied chain shift presentations.

Source: blueprint dual-Tate compatibility, Step 4; Stacks 0A8X, 08JA
(blueprint: lem-pod-reindexing-signed-shifts).

Proof: shifted K-injective complexes remain K-injective by transporting a
null-homotopy through the shift. Apply the comparison's `derived_model` to
these representatives. The projection characterization of the normalized
source and target shifts identifies the localized chain square with the
specified `signedShift`; naturality along resolutions extends the identity to
arbitrary derived objects. -/
theorem derived_shift_part {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [EssentiallySmall.{u + 1} X.ProEt] [EssentiallySmall.{u + 1} Y.ProEt] (s : Option ℕ)
    (SX : Closed l E X s) (SY : Closed l E Y s)
    (TX : Models l E X s SX) (TY : Models l E Y s SY)
    (c : Comparison l E g s SX SY TX TY) :
    DerivedShiftPart l E g s SX SY TX TY c := by
  change ∀ (M N : podReindexingDerived l E Y s) (a b : ℤ),
    derivedShiftEquation l E g s SX SY TX TY c M N a b
  exact derived_shift_descent l E g s SX SY TX TY c
    (derived_shift_model l E g s SX SY TX TY c)

end WeilConjectures.PodReindexingCoherence
