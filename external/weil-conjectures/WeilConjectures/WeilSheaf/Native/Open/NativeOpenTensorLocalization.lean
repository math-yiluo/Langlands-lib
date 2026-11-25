/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorPresentationExistence

/-! # Localizing the native open tensor comparison

Source: Stacks 0GL1, 06YN; steps 3--6 of the native open tensor proof.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

-- The dependent presentation fields require a larger elaboration budget.
/-- Totalize the fixed sheaf maps and descend them, with the prescribed models,
to the unbounded ambient derived categories.

Source: Stacks 0GL1 and 06YN; native open tensor proof steps 3--6
(blueprint: lem-sf-native-open-tensor-localization).

Proof: Apply the fixed sheaf comparison and its inverse in every bidegree. The
coproducts are created by forgetting Weil structures. The signed differential
calculation dx tensor y + (-1)^p x tensor dy makes these maps natural chain
isomorphisms and pins every summand to s.sheafGamma. Totalize s.sheafRestriction
in the same way, pinning every restriction summand. Use the twisted action-site
presentation and its flat-term equivariant K-flat resolutions. Its coefficients
agree with the native locally finite coefficient functions: finitely many
spanning values lie in a finite subextension, and a quasi-compact test object
needs only finitely many such neighborhoods. The finite compositum gives the
same coefficient sheaf. Check flat terms in the two functors as well as the
K-flatness already recorded in s. For extension, restrict a short exact sequence,
tensor with a flat sheaf, and extend. For restriction, extend a short exact
sequence, tensor with a flat ambient sheaf, and restrict back using the open
unit. The sheaf tensor comparisons identify these sequences, proving flatness.
Thus both exact functors preserve the resolving subcategories. Localize the
natural chain comparisons and their inverses in each variable. The native
K-flat tensor models and exact-functor factorization isomorphisms give precisely
the two representative normalization squares in OpenTensorPresentation. The
localization universal property supplies naturality on all derived objects,
independence of resolutions, and the inverse identities. Record the actual
native functors, K-flat predicates, models and insertions as the remaining
fields; their compatibility equalities are reflexive. -/
theorem native_open_tensor_localization (s : NativeOpenTensorData k₀ l j) :
    ∃ (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
        (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
      (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U) (ProEtaleWeilSheaf k₀ l Z)),
      HEq c.E (extensionByZero k₀ l j) ∧ HEq c.R (upperStar k₀ l j) ∧
      HEq c.SA (nativeOpenSheafTensor k₀ l U) ∧ HEq c.SB (nativeOpenSheafTensor k₀ l Z) ∧
      HEq c.TA (nativeTensorTotal k₀ l U) ∧ HEq c.TB (nativeTensorTotal k₀ l Z) ∧
      HEq c.DA (nativeDerivedTensor k₀ l U) ∧ HEq c.DB (nativeDerivedTensor k₀ l Z) ∧
      HEq c.flatA (NativeIsKFlat k₀ l U) ∧ HEq c.flatB (NativeIsKFlat k₀ l Z) ∧
      HEq c.modelA (nativeOpenTensorModel k₀ l U) ∧
      HEq c.modelB (nativeOpenTensorModel k₀ l Z) ∧
      HEq c.iA (nativeOpenTensorInsertion k₀ l U) ∧
      HEq c.iB (nativeOpenTensorInsertion k₀ l Z) ∧
      HEq c.sheafGamma s.sheafGamma ∧ HEq c.gamma gamma ∧
      HEq c.sheafRestriction s.sheafRestriction ∧ HEq c.restriction rho := by
  exact native_open_tensor_presentation_exists k₀ l j s

end AlgebraicGeometry.ProEtaleWeilSheaf
