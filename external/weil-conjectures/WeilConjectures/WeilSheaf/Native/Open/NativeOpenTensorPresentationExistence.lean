/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorExtensionDescent
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent

/-! # Native open tensor presentation with normalized comparisons

Source: Stacks 0GL1 and 06YN; native open tensor proof steps 3--6.
(blueprint: new-sf-native-open-tensor-presentation)

The extension and restriction descents construct their derived comparisons together
with the required representative equations. Their fields assemble into a presentation
whose operations and models are the native ones.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.extensionByZero
  AlgebraicGeometry.ProEtaleWeilSheaf.upperStar
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeTensorTotal
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedTensor
  AlgebraicGeometry.ProEtaleWeilSheaf.NativeIsKFlat
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorModel
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeOpenTensorInsertion
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

universe u a b

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

section

attribute [local instance] OpenTensorDescentInput.e_add OpenTensorDescentInput.r_add
  OpenTensorDescentInput.e_lim OpenTensorDescentInput.e_colim
  OpenTensorDescentInput.r_lim OpenTensorDescentInput.r_colim
  OpenTensorDescentInput.e_zero OpenTensorDescentInput.r_zero

private def assembleOpenTensorPresentation
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (ext : OpenTensorExtensionDescentData c m) (res : OpenTensorRestrictionDescentData c m) :
    OpenTensorPresentation A B :=
  { E := c.E
    R := c.R
    e_add := c.e_add
    r_add := c.r_add
    e_lim := c.e_lim
    e_colim := c.e_colim
    r_lim := c.r_lim
    r_colim := c.r_colim
    SA := c.SA
    SB := c.SB
    TA := c.TA
    TB := c.TB
    DA := c.DA
    DB := c.DB
    flatA := c.flatA
    flatB := c.flatB
    hE := ext.hE
    hR := res.hR
    modelA := m.modelA
    modelB := m.modelB
    iA := m.iA
    iB := m.iB
    sheafGamma := m.sheafGamma
    totalGamma := ext.total
    summands := ext.summands
    sheafRestriction := m.sheafRestriction
    totalRestriction := res.total
    restriction_summands := res.summands
    restriction := res.rho
    restriction_model := res.model
    gamma := ext.gamma
    model := ext.model }

private theorem assembleOpenTensorPresentation_fields
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (ext : OpenTensorExtensionDescentData c m) (res : OpenTensorRestrictionDescentData c m) :
    HEq (assembleOpenTensorPresentation c m ext res).E (c.E) ∧
    HEq (assembleOpenTensorPresentation c m ext res).R (c.R) ∧
    HEq (assembleOpenTensorPresentation c m ext res).SA (c.SA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).SB (c.SB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).TA (c.TA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).TB (c.TB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).DA (c.DA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).DB (c.DB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).flatA (c.flatA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).flatB (c.flatB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).modelA (m.modelA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).modelB (m.modelB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).iA (m.iA) ∧
    HEq (assembleOpenTensorPresentation c m ext res).iB (m.iB) ∧
    HEq (assembleOpenTensorPresentation c m ext res).sheafGamma (m.sheafGamma) ∧
    HEq (assembleOpenTensorPresentation c m ext res).gamma (ext.gamma) ∧
    HEq (assembleOpenTensorPresentation c m ext res).sheafRestriction (m.sheafRestriction) ∧
    HEq (assembleOpenTensorPresentation c m ext res).restriction (res.rho) := by
  exact ⟨HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl,
    HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

private theorem assembleOpenTensorPresentation_compatible
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (ext : OpenTensorExtensionDescentData c m) (res : OpenTensorRestrictionDescentData c m)
    {V_E : Sort _} (v_E : V_E)
    {V_R : Sort _} (v_R : V_R)
    {V_SA : Sort _} (v_SA : V_SA)
    {V_SB : Sort _} (v_SB : V_SB)
    {V_TA : Sort _} (v_TA : V_TA)
    {V_TB : Sort _} (v_TB : V_TB)
    {V_DA : Sort _} (v_DA : V_DA)
    {V_DB : Sort _} (v_DB : V_DB)
    {V_flatA : Sort _} (v_flatA : V_flatA)
    {V_flatB : Sort _} (v_flatB : V_flatB)
    {V_modelA : Sort _} (v_modelA : V_modelA)
    {V_modelB : Sort _} (v_modelB : V_modelB)
    {V_iA : Sort _} (v_iA : V_iA)
    {V_iB : Sort _} (v_iB : V_iB)
    {V_sheafGamma : Sort _} (v_sheafGamma : V_sheafGamma)
    {V_gamma : Sort _} (v_gamma : V_gamma)
    {V_sheafRestriction : Sort _} (v_sheafRestriction : V_sheafRestriction)
    {V_restriction : Sort _} (v_restriction : V_restriction)
    (h_E : HEq c.E v_E)
    (h_R : HEq c.R v_R)
    (h_SA : HEq c.SA v_SA)
    (h_SB : HEq c.SB v_SB)
    (h_TA : HEq c.TA v_TA)
    (h_TB : HEq c.TB v_TB)
    (h_DA : HEq c.DA v_DA)
    (h_DB : HEq c.DB v_DB)
    (h_flatA : HEq c.flatA v_flatA)
    (h_flatB : HEq c.flatB v_flatB)
    (h_modelA : HEq m.modelA v_modelA)
    (h_modelB : HEq m.modelB v_modelB)
    (h_iA : HEq m.iA v_iA)
    (h_iB : HEq m.iB v_iB)
    (h_sheafGamma : HEq m.sheafGamma v_sheafGamma)
    (h_gamma : HEq ext.gamma v_gamma)
    (h_sheafRestriction : HEq m.sheafRestriction v_sheafRestriction)
    (h_restriction : HEq res.rho v_restriction) :
    HEq (assembleOpenTensorPresentation c m ext res).E v_E ∧
    HEq (assembleOpenTensorPresentation c m ext res).R v_R ∧
    HEq (assembleOpenTensorPresentation c m ext res).SA v_SA ∧
    HEq (assembleOpenTensorPresentation c m ext res).SB v_SB ∧
    HEq (assembleOpenTensorPresentation c m ext res).TA v_TA ∧
    HEq (assembleOpenTensorPresentation c m ext res).TB v_TB ∧
    HEq (assembleOpenTensorPresentation c m ext res).DA v_DA ∧
    HEq (assembleOpenTensorPresentation c m ext res).DB v_DB ∧
    HEq (assembleOpenTensorPresentation c m ext res).flatA v_flatA ∧
    HEq (assembleOpenTensorPresentation c m ext res).flatB v_flatB ∧
    HEq (assembleOpenTensorPresentation c m ext res).modelA v_modelA ∧
    HEq (assembleOpenTensorPresentation c m ext res).modelB v_modelB ∧
    HEq (assembleOpenTensorPresentation c m ext res).iA v_iA ∧
    HEq (assembleOpenTensorPresentation c m ext res).iB v_iB ∧
    HEq (assembleOpenTensorPresentation c m ext res).sheafGamma v_sheafGamma ∧
    HEq (assembleOpenTensorPresentation c m ext res).gamma v_gamma ∧
    HEq (assembleOpenTensorPresentation c m ext res).sheafRestriction v_sheafRestriction ∧
    HEq (assembleOpenTensorPresentation c m ext res).restriction v_restriction := by
  have hf := assembleOpenTensorPresentation_fields c m ext res
  exact ⟨
    hf.1.trans h_E,
    hf.2.1.trans h_R,
    hf.2.2.1.trans h_SA,
    hf.2.2.2.1.trans h_SB,
    hf.2.2.2.2.1.trans h_TA,
    hf.2.2.2.2.2.1.trans h_TB,
    hf.2.2.2.2.2.2.1.trans h_DA,
    hf.2.2.2.2.2.2.2.1.trans h_DB,
    hf.2.2.2.2.2.2.2.2.1.trans h_flatA,
    hf.2.2.2.2.2.2.2.2.2.1.trans h_flatB,
    hf.2.2.2.2.2.2.2.2.2.2.1.trans h_modelA,
    hf.2.2.2.2.2.2.2.2.2.2.2.1.trans h_modelB,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h_iA,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h_iB,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h_sheafGamma,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h_gamma,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.trans h_sheafRestriction,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.trans h_restriction⟩

private theorem assembleOpenTensorPresentation_exists
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (c : OpenTensorDescentInput A B) (m : OpenTensorDescentModels c)
    (ext : OpenTensorExtensionDescentData c m) (res : OpenTensorRestrictionDescentData c m)
    {V_E : Sort _} (v_E : V_E)
    {V_R : Sort _} (v_R : V_R)
    {V_SA : Sort _} (v_SA : V_SA)
    {V_SB : Sort _} (v_SB : V_SB)
    {V_TA : Sort _} (v_TA : V_TA)
    {V_TB : Sort _} (v_TB : V_TB)
    {V_DA : Sort _} (v_DA : V_DA)
    {V_DB : Sort _} (v_DB : V_DB)
    {V_flatA : Sort _} (v_flatA : V_flatA)
    {V_flatB : Sort _} (v_flatB : V_flatB)
    {V_modelA : Sort _} (v_modelA : V_modelA)
    {V_modelB : Sort _} (v_modelB : V_modelB)
    {V_iA : Sort _} (v_iA : V_iA)
    {V_iB : Sort _} (v_iB : V_iB)
    {V_sheafGamma : Sort _} (v_sheafGamma : V_sheafGamma)
    {V_gamma : Sort _} (v_gamma : V_gamma)
    {V_sheafRestriction : Sort _} (v_sheafRestriction : V_sheafRestriction)
    {V_restriction : Sort _} (v_restriction : V_restriction)
    (h_E : HEq c.E v_E)
    (h_R : HEq c.R v_R)
    (h_SA : HEq c.SA v_SA)
    (h_SB : HEq c.SB v_SB)
    (h_TA : HEq c.TA v_TA)
    (h_TB : HEq c.TB v_TB)
    (h_DA : HEq c.DA v_DA)
    (h_DB : HEq c.DB v_DB)
    (h_flatA : HEq c.flatA v_flatA)
    (h_flatB : HEq c.flatB v_flatB)
    (h_modelA : HEq m.modelA v_modelA)
    (h_modelB : HEq m.modelB v_modelB)
    (h_iA : HEq m.iA v_iA)
    (h_iB : HEq m.iB v_iB)
    (h_sheafGamma : HEq m.sheafGamma v_sheafGamma)
    (h_gamma : HEq ext.gamma v_gamma)
    (h_sheafRestriction : HEq m.sheafRestriction v_sheafRestriction)
    (h_restriction : HEq res.rho v_restriction) :
    ∃ (rho : V_restriction) (gamma : V_gamma) (p : OpenTensorPresentation A B),
    HEq p.E v_E ∧
    HEq p.R v_R ∧
    HEq p.SA v_SA ∧
    HEq p.SB v_SB ∧
    HEq p.TA v_TA ∧
    HEq p.TB v_TB ∧
    HEq p.DA v_DA ∧
    HEq p.DB v_DB ∧
    HEq p.flatA v_flatA ∧
    HEq p.flatB v_flatB ∧
    HEq p.modelA v_modelA ∧
    HEq p.modelB v_modelB ∧
    HEq p.iA v_iA ∧
    HEq p.iB v_iB ∧
    HEq p.sheafGamma v_sheafGamma ∧
    HEq p.gamma gamma ∧
    HEq p.sheafRestriction v_sheafRestriction ∧
    HEq p.restriction rho := by
  refine ⟨v_restriction, v_gamma, assembleOpenTensorPresentation c m ext res, ?_⟩
  exact assembleOpenTensorPresentation_compatible c m ext res
    v_E v_R v_SA v_SB v_TA v_TB v_DA v_DB v_flatA v_flatB
    v_modelA v_modelB v_iA v_iB v_sheafGamma v_gamma v_sheafRestriction v_restriction
    h_E h_R h_SA h_SB h_TA h_TB h_DA h_DB h_flatA h_flatB
    h_modelA h_modelB h_iA h_iB h_sheafGamma h_gamma h_sheafRestriction h_restriction

end

end CategoryTheory

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

private theorem native_input_E :
    HEq (nativeOpenTensorDescentInput k₀ l j).E (extensionByZero k₀ l j) := HEq.rfl

private theorem native_input_R :
    HEq (nativeOpenTensorDescentInput k₀ l j).R (upperStar k₀ l j) := HEq.rfl

private theorem native_input_SA :
    HEq (nativeOpenTensorDescentInput k₀ l j).SA (nativeOpenSheafTensor k₀ l U) := HEq.rfl

private theorem native_input_SB :
    HEq (nativeOpenTensorDescentInput k₀ l j).SB (nativeOpenSheafTensor k₀ l Z) := HEq.rfl

private theorem native_input_TA :
    HEq (nativeOpenTensorDescentInput k₀ l j).TA (nativeTensorTotal k₀ l U) := HEq.rfl

private theorem native_input_TB :
    HEq (nativeOpenTensorDescentInput k₀ l j).TB (nativeTensorTotal k₀ l Z) := HEq.rfl

private theorem native_input_DA :
    HEq (nativeOpenTensorDescentInput k₀ l j).DA (nativeDerivedTensor k₀ l U) := HEq.rfl

private theorem native_input_DB :
    HEq (nativeOpenTensorDescentInput k₀ l j).DB (nativeDerivedTensor k₀ l Z) := HEq.rfl

private theorem native_input_flatA :
    HEq (nativeOpenTensorDescentInput k₀ l j).flatA (NativeIsKFlat k₀ l U) := HEq.rfl

private theorem native_input_flatB :
    HEq (nativeOpenTensorDescentInput k₀ l j).flatB (NativeIsKFlat k₀ l Z) := HEq.rfl

attribute [local irreducible] nativeOpenTensorDescentInput

private theorem native_presentation_from_components
    (s : NativeOpenTensorData k₀ l j)
    (e : NativeOpenTensorExtensionDescentData k₀ l j s)
    (r : NativeOpenTensorRestrictionDescentData k₀ l j s e.models) :
    ∃ (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
        (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
      (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U)
        (ProEtaleWeilSheaf k₀ l Z)),
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
  have hea := e.compatible.modelA
  have heb := e.compatible.modelB
  have heia := e.compatible.iA
  have heib := e.compatible.iB
  have heg := e.compatible.sheafGamma
  have her := e.compatible.sheafRestriction
  exact assembleOpenTensorPresentation_exists
    (nativeOpenTensorDescentInput k₀ l j) e.models e.component r.component
    (extensionByZero k₀ l j)
    (upperStar k₀ l j)
    (nativeOpenSheafTensor k₀ l U)
    (nativeOpenSheafTensor k₀ l Z)
    (nativeTensorTotal k₀ l U)
    (nativeTensorTotal k₀ l Z)
    (nativeDerivedTensor k₀ l U)
    (nativeDerivedTensor k₀ l Z)
    (NativeIsKFlat k₀ l U)
    (NativeIsKFlat k₀ l Z)
    (nativeOpenTensorModel k₀ l U)
    (nativeOpenTensorModel k₀ l Z)
    (nativeOpenTensorInsertion k₀ l U)
    (nativeOpenTensorInsertion k₀ l Z)
    (s.sheafGamma)
    (e.gamma)
    (s.sheafRestriction)
    (r.rho)
    (native_input_E k₀ l j)
    (native_input_R k₀ l j)
    (native_input_SA k₀ l j)
    (native_input_SB k₀ l j)
    (native_input_TA k₀ l j)
    (native_input_TB k₀ l j)
    (native_input_DA k₀ l j)
    (native_input_DB k₀ l j)
    (native_input_flatA k₀ l j)
    (native_input_flatB k₀ l j)
    (hea)
    (heb)
    (heia)
    (heib)
    (heg)
    (e.gamma_compatible)
    (her)
    (r.rho_compatible)

/-- Construct the native open tensor presentation together with its normalized comparisons.

STATEMENT-DISPUTED (replaced statement): arbitrary derived rho and gamma cannot
satisfy the fixed summand and representative normalizations. The comparisons
are existential outputs here; the enclosing localization statement is unchanged.

Source: Stacks 0GL1 and 06YN, totalization, K-flat descent, and localization
normalization.  The native operations and representative insertions are
chosen first; degreewise tensor comparisons and exactness identify their
normalization maps, and the localization universal property proves the
required representative equalities.
(blueprint: new-sf-native-open-tensor-presentation)
-/
theorem native_open_tensor_presentation_exists (s : NativeOpenTensorData k₀ l j) :
    ∃ (rho : nativeDerivedTensor k₀ l Z ⋙ nativeOpenPull k₀ l j ≅
        (nativeOpenPull k₀ l j).prod (nativeOpenPull k₀ l j) ⋙ nativeDerivedTensor k₀ l U)
      (gamma : nativeOpenDerivedLeft k₀ l j ≅ nativeOpenDerivedRight k₀ l j)
      (c : OpenTensorPresentation (ProEtaleWeilSheaf k₀ l U)
        (ProEtaleWeilSheaf k₀ l Z)),
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
  classical
  let e := Classical.choice (native_open_tensor_extension_descent k₀ l j s)
  let r := Classical.choice
    (native_open_tensor_restriction_descent k₀ l j s e.models e.compatible)
  exact native_presentation_from_components k₀ l j s e r

end AlgebraicGeometry.ProEtaleWeilSheaf
