/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.CommonStagePullbackCompComponent

/-! # Localization of the finite-stage common pullback compositor

(blueprint: lem-pur-common-stage-pullback-composition-localization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The explicit finite-stage compositor is the localized integral compositor under the
prescribed rational-pullback object equalities.
Source: Stacks 07A4, 0941; the finite-stage composition convention.
(blueprint: lem-pur-common-stage-pullback-composition-localization).
Proof: The compositor is the localization of the integral isomorphism, conjugated by
`eqToIso` for the source and target object equalities. The hom of this conjugate is
heterogeneously equal to the localized hom by `conj_eqToHom_iff_heq`. -/
theorem commonStagePullbackRationalComposition_localization
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
    [IsAlgClosure (Padic l) Ω] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (h : Z ⟶ X)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L) :
    HEq (commonStagePullbackRationalComposition l Ω h f L M hM).hom
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Z).map
        (((integralPullbackComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).choose h f).hom.app
          (M.toStage hM).obj)) := by
  let K := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L
  have ha := (rationalDerivedPullback_existsUnique l K (h ≫ f)).exists.choose_spec.2.1
    (M.toStage hM)
  have hb := (congrArg (rationalDerivedPullback l K h).obj
    ((rationalDerivedPullback_existsUnique l K f).exists.choose_spec.2.1
      (M.toStage hM))).trans
    ((rationalDerivedPullback_existsUnique l K h).exists.choose_spec.2.1
      ((sfRationalConstructibleLocalization l K X).obj
        ((constructibleIntegralPullback l K f).obj (M.toStage hM).obj)))
  exact (conj_eqToHom_iff_heq _ _ ha hb).mp rfl

end WeilConjectures
