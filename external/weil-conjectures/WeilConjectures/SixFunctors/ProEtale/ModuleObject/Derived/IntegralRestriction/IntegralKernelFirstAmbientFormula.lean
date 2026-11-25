/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralKernelUnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralRestriction.IntegralNormalizedFamily
/-! # Ambient integral first contraction -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
open DiagonalCoefficients
open RationalP1
variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
/--
The ambient integral contraction formula for the fixed diagonal coefficient family.
This is the geometric trace/base-change calculation before restricting the unit and
counit to localizing subcategories.  It is strictly smaller than the contraction
with arbitrary restricted unit and counit: it only concerns ambient components whose
normalizations are the fixed formulas.  The proof transports the completed
trace/base-change equation through the integral coefficient reference, applies the
projection/section normalization, and identifies the resulting paste with the
literal support, diagonal-class, and trace composite.
Source: `sk-thm-int-restriction-line.proof.md`, paragraph (1), first contraction.
(blueprint: lem-integral-kernel-first-ambient-formula).
-/
theorem integralKernel_first_ambient_formula
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    (Y : Scheme.{u}) [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [∀ x : ProjectiveLine Y, Invertible (ℓ : (ProjectiveLine Y).residueField x)]
    [∀ x : diagonalSurface Y, Invertible (ℓ : (diagonalSurface Y).residueField x)]
    (family : Family ℓ Y) :
    (∀ (M : DerivedCategory
        (Modules (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)))
      (u : M ⟶ (twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
        (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
          ((moduleObjectDerivedPullback
            (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
            ((moduleObjectDerivedPushforward
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M)))
      (v : (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
        ((twist (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y)
          (spIntegralTwist (ProjectiveLine Y) ℓ E)).obj
            ((moduleObjectDerivedPullback
              (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj
              ((moduleObjectDerivedPushforward
                (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M))) ⟶
        (moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M)
      (_hu : RationalP1.UnitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        (by simpa only [traceTate] using
          (integralShiftedLinePullIso ℓ E (secondProjection Y))) M u)
      (_hv : RationalP1.CounitComponentNormalized
        (Profinite.padicIntegersRingObj ℓ E.val) Y (fun X ↦ spIntegralTwist X ℓ E)
        (family.integral E)
        ((moduleObjectDerivedPushforward
          (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).obj M) v),
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map u ≫ v =
      (moduleObjectDerivedPushforward
        (Profinite.padicIntegersRingObj ℓ E.val) (ProjectiveLine Y ↘ Y)).map
        ((ρ_ M).inv ≫ (M ◁
          ((singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
            (ProjectiveLine Y)).inv ≫ (family.integral E).support₁.hom ≫
            (family.integral E).R₁.R.map (family.integral E).delta ≫
            (family.integral E).trace₁ ≫
            (singleUnitIso (Profinite.padicIntegersRingObj ℓ E.val)
              (ProjectiveLine Y)).hom)) ≫ (ρ_ M).hom)) := by
  sorry
end AlgebraicGeometry.ProEtale.CondensedRing.IntegralRestriction
