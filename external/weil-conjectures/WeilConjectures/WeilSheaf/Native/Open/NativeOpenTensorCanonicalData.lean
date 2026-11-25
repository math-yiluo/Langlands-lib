/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorOperations

/-! # Canonical expressions for the native open tensor data

Source: the native tensor, total tensor, and actual summand insertion definitions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtaleWeilSheaf

attribute [local irreducible] nativeDerivedClosedComparison nativeTensorMap tensor

/-- The native tensor data agree with the curried totalization expressions.
Source: Stacks 012Z and the definitions of nativeTensorBifunctor, nativeTensorTotal,
and nativeOpenTensorInsertion (blueprint: lem-sf-native-open-tensor-canonical-data).
Proof: unfold the object and map projections of the flipped tensor bifunctor.
The total tensor is defined to be its cochain total, and the recorded insertion
is defined to be the actual homogeneous coproduct insertion for that total.
All four equalities are therefore reflexive, on arbitrary objects and complexes. -/
theorem native_open_tensor_canonical_data
    (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))] :
    ((fun M N ↦ tensor k₀ l X N M) =
      fun M N ↦ (((nativeTensorBifunctor k₀ l X).flip.obj M).obj N)) ∧
    HEq (fun {M M' : ProEtaleWeilSheaf k₀ l X} (f : M ⟶ M') N ↦
      (tensorFunctor k₀ l X N).map f)
      (fun {M M' : ProEtaleWeilSheaf k₀ l X} (f : M ⟶ M') N ↦
        ((nativeTensorBifunctor k₀ l X).flip.map f).app N) ∧
    nativeTensorTotal k₀ l X = (nativeTensorBifunctor k₀ l X).flip.map₂CochainComplex ∧
    HEq (nativeOpenTensorInsertion k₀ l X)
      (fun (P T : CochainComplex (ProEtaleWeilSheaf k₀ l X) ℤ) p q n h ↦
        HomologicalComplex.ιMapBifunctor P T (nativeTensorBifunctor k₀ l X).flip
          (.up ℤ) p q n h) := by
  exact ⟨rfl, HEq.rfl, rfl, HEq.rfl⟩

end AlgebraicGeometry.ProEtaleWeilSheaf
