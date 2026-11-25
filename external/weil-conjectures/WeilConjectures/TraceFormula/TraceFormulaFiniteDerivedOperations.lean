/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicFiniteOperations
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal

/-! # Intrinsic finite operations for the trace formula

Source: Stacks 07A4, 08J9, and latest blueprint sk-d-six.
(blueprint: def-trf-finite-derived-operations).
Only one positive finite coefficient level is used. The closed adjunction and its
K-flat representative normalization determine the tensor up to its compatible
natural isomorphism; no integral or rational coefficient-system witness is chosen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

/-- Exact intrinsic pullback at a positive finite level.
Source: sk-d-six (blueprint: def-trf-finite-derived-operations). -/
abbrev traceFormulaFinitePullback {X Y : Scheme.{u}}
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (f : X ⟶ Y) :=
  letI : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
  sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E (n + 1)) f

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The intrinsic K-injective internal Hom for the finite constant ring.
Source: Stacks 08J9 (blueprint: def-trf-finite-derived-operations). -/
abbrev traceFormulaFiniteInternalHom (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{t}) (n : ℕ) :=
  @derivedInternalHomOfUniverses.{t+1, t, u, max (t+1) u + 1}
    _ _ (ProEt.topology W)
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (integralCoefficientCommRingSheaf l E W n)
    (HasDerivedCategory.standard (RingedTensorModules.{t+1, t, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)))

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The normalized closed tensor, uniquely characterized by its closed universal
property and K-flat comparison up to the compatible isomorphism used downstream.
Source: Stacks 07A4, 08J9 (blueprint: def-trf-finite-derived-operations). -/
def traceFormulaFiniteClosed (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{t}) (n : ℕ) :
    CoefficientClosedStructure (traceFormulaFiniteInternalHom l E W n) :=
  (@ringedDerived_closed_symmetric_monoidal.{t+1, t, u, max (t+1) u + 1}
    _ _ (ProEt.topology W)
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (integralCoefficientCommRingSheaf l E W n)
    (HasDerivedCategory.standard (RingedTensorModules.{t+1, t, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)))).choose

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The tensor of the normalized closed structure.
Source: Stacks 07A4 (blueprint: def-trf-finite-derived-operations). -/
def traceFormulaFiniteTensor (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{t}) (n : ℕ) :=
  (traceFormulaFiniteClosed l E W n).tensor

attribute [-instance] GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The fixed simultaneous K-flat representative comparison and evaluation formula.
Source: Stacks 08J9 (blueprint: def-trf-finite-derived-operations). -/
def traceFormulaFiniteTensorModels (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (W : Scheme.{t}) (n : ℕ) :
    @CoefficientTensorModels.{u, t+1, t, max (t+1) u + 1} _ _ (ProEt.topology W)
      (integralCoefficientAbSheafify.{t, u} W)
      (integralCoefficientAbLocallyBijective.{t, u} W)
      (integralCoefficientCommRingSheaf l E W n)
      (HasDerivedCategory.standard (RingedTensorModules.{t+1, t, u}
        (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)))
      (traceFormulaFiniteClosed l E W n) :=
  (@ringedDerived_closed_symmetric_monoidal.{t+1, t, u, max (t+1) u + 1}
    _ _ (ProEt.topology W)
    (integralCoefficientAbSheafify.{t, u} W)
    (integralCoefficientAbLocallyBijective.{t, u} W)
    (integralCoefficientCommRingSheaf l E W n)
    (HasDerivedCategory.standard (RingedTensorModules.{t+1, t, u}
      (ProEt.topology W) (integralCoefficientCommRingSheaf l E W n)))).choose_spec.choose

end WeilConjectures
