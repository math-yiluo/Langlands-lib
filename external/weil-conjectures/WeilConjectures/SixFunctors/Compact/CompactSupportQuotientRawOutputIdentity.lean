/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientNative
import WeilConjectures.SixFunctors.Compact.CompactSupportQuotientOutputIdentity

/-! # Original presentation of the output quotient identity

Source: the current blueprint finite-level coefficient comparison
(blueprint: lem-coef-compact-support-quotient-raw-output-identity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] Padic.coefficientExtensionIdeal
  HasDerivedCategory.standard SheafOfModules.monoidalCategory
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.scalarReductionDerivedExtension WeilConjectures.compactSupportReductionMap
attribute [local implicit_reducible] WeilConjectures.integralCoefficientSheaf
  WeilConjectures.scalarReductionTargetDerived
  AlgebraicGeometry.Scheme.sfIntrinsicCompactSupport
  AlgebraicGeometry.Scheme.sfAmbientCompactSupportCandidate
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem rawIdentity_map {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (n : ℕ) :
    (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
        (compactSupportReductionMap l E X n n le_rfl K) =
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).map
        (compactSupportQuotientNativeMap l E X n n le_rfl K) := by
  rfl

private theorem rawIdentity_comparison {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (n : ℕ) :
    (sfCompactSupportRestriction c (compactSupportLevelQuotient l E n n le_rfl)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K) =
      (compactSupportQuotientNativeComparison l E c n n le_rfl).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) := by
  rfl

private theorem rawIdentity_app_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (α : F ⟶ G) {H J : C} (e : H = J) :
    HEq (α.app H) (α.app J) := by
  cases e
  rfl

private theorem rawIdentity_resId {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (n : ℕ) :
    (compactSupportQuotientResId l E Y n).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) =
      (compactSupportQuotientNativeResId l E Y n).hom.app
        ((sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n + 1)) c).obj
          ((compactSupportQuotientNativeLevel l E X n).obj K)) := by
  have he := congrArg
    (fun F : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E (n + 1)) ⥤
        proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E (n + 1)) ↦
      F.obj ((compactSupportQuotientNativeLevel l E X n).obj K))
    (compactSupportQuotient_intrinsic_eq_ambient c
      (Padic.coefficientExtensionRing l E (n + 1)))
  exact eq_of_heq (rawIdentity_app_heq (compactSupportQuotientResId l E Y n).hom he)

/-- The transported identity with exactly the original compact-support expressions.
Source: identity coefficient normalization and functoriality
(blueprint: lem-coef-compact-support-quotient-raw-output-identity).
Proof: rewrite the intrinsic functor to its identical ambient presentation, and
apply the proved output identity. Every quotient wrapper retains its actual value. -/
theorem compactSupportQuotient_raw_output_identity
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategory (scalarReductionSource.{u, u} l E X))
    (hid :
    (∀ n : ℕ, compactSupportQuotientNativeMap l E X n n le_rfl K ≫
      (compactSupportQuotientNativeResId l E X n).hom.app
        ((compactSupportQuotientNativeLevel l E X n).obj K) = 𝟙 _)) :
    (∀ n : ℕ, ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).map
        (compactSupportReductionMap l E X n n le_rfl K) ≫
      (sfCompactSupportRestriction c (compactSupportLevelQuotient l E n n le_rfl)).hom.app
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) ≫
      (compactSupportQuotientResId l E Y n).hom.app
        ((sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))).obj
          ((scalarReductionDerivedExtension.{u, u} l E X n).obj K)) = 𝟙 _) := by
  intro n
  simp only [rawIdentity_map, rawIdentity_comparison, rawIdentity_resId]
  exact compactSupportQuotient_output_identity l E c K hid n

end WeilConjectures
