/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.FreeParameterScalarMaps

/-! # Unit normalization of integral reduction and geometric pullback

Source: Stacks 06YY and 07A6; blueprint integral open direct image, Reduction paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.mapDerivedCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  {U X : Scheme.{u}} (j : U ⟶ X)

/-- The specified inverse scalar mate at exponent n+1.
Source: Stacks 06YY and 07A6
(auxiliary; not a blueprint node). -/
abbrev integralReductionPullbackMap (n : ℕ) :
    (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
        AdicCompletion.derivedReduction l E U n ⟶
      AdicCompletion.derivedReduction l E X n ⋙
        (CondensedRing.upperStar
          (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory :=
  ((mateEquiv
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))).symm
      (TwoSquare.mk _ _ _ _
        (CondensedRing.derivedComapUpperStarIso
          (DerivedNakayama.reductionRing l E (n + 1)) j).inv))

/-- A finite derived scalar/pullback comparison with the prescribed scalar-unit equation.
Source: Stacks 06YY, 07A6; blueprint integral open direct image, Reduction paragraph
(auxiliary; not a blueprint node).

Proof: the underived inverse image is exact and strong monoidal, and its coefficient
identification is an isomorphism. Relative tensor balancing gives the comparison sending
s tensor m to s tensor m, retaining the finite coefficient action. Pullback preserves
K-flat complexes: apply its exact strong monoidal functor to the acyclic tensor test.
Compute the two derived scalar extensions on a flat-term K-flat representative and
localize the balancing isomorphism. Independence of resolution and naturality follow
from the universal left derived functor. On representatives the scalar units both send
m to 1 tensor m, so the displayed equation follows after exact restriction. This
identifies the actual inverse mate and requires no flatness of the quotient map.
Positive exponent one, zero complexes, empty schemes and unbounded representatives
satisfy the same balancing and unit formulas. -/
theorem integral_reduction_pullback_normalization (n : ℕ) :
    ∃ b :
      (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory ⋙
          AdicCompletion.derivedReduction l E U n ≅
        AdicCompletion.derivedReduction l E X n ⋙
          (CondensedRing.upperStar
            (DerivedNakayama.quotientRing l E (n + 1)) j).mapDerivedCategory,
      ∀ M : DerivedCategory (AdicCompletion.Modules l E X),
        (CondensedRing.upperStar (DerivedNakayama.integerRing l E) j).mapDerivedCategory.map
            ((Mod.derivedExtendMapDerivedCategoryAdjunction
              (AdicCompletion.quotient l E X n)).unit.app M) ≫
          (CondensedRing.derivedComapUpperStarIso
            (DerivedNakayama.reductionRing l E (n + 1)) j).inv.app
              ((AdicCompletion.derivedReduction l E X n).obj M) =
        (Mod.derivedExtendMapDerivedCategoryAdjunction
          (AdicCompletion.quotient l E U n)).unit.app
            ((CondensedRing.upperStar
              (DerivedNakayama.integerRing l E) j).mapDerivedCategory.obj M) ≫
          (AdicCompletion.restrict l E U n).map (b.hom.app M) := by
  have h (M : DerivedCategory (AdicCompletion.Modules l E X)) :
      IsIso ((integralReductionPullbackMap l E j n).app M) := by
    have he : (integralReductionPullbackMap l E j n).app M =
        FreeParameterEvaluation.scalarPullComparison
          (Mon.mk (DerivedNakayama.integerRing l E))
          (Mon.mk (DerivedNakayama.quotientRing l E (n + 1)))
          (DerivedNakayama.reductionRing l E (n + 1)) j M := by
      rfl
    rw [he]
    exact FreeParameterEvaluation.scalarPullComparison_isIso
      (Mon.mk (DerivedNakayama.integerRing l E))
      (Mon.mk (DerivedNakayama.quotientRing l E (n + 1)))
      (DerivedNakayama.reductionRing l E (n + 1)) j M
  have := NatIso.isIso_of_isIso_app (integralReductionPullbackMap l E j n)
  refine ⟨asIso (integralReductionPullbackMap l E j n), fun M ↦ ?_⟩
  exact unit_mateEquiv_symm
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E U n))
    (.mk _ _ _ _ (CondensedRing.derivedComapUpperStarIso
      (DerivedNakayama.reductionRing l E (n + 1)) j).inv) M

end AlgebraicGeometry.ProEtale
