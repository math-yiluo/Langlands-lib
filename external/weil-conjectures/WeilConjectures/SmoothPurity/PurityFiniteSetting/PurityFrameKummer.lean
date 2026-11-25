/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FixedFinitePositiveCoefficientTwist
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1Decomposition
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal

/-!
# Concrete Kummer classes at every finite level

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
proposition-purity-vector-bundles, and the expanded finite-level prescription in the DAG
(blueprint: def-pur-frame-kummer-class).

Kummer classes use the actual Kummer extension at exponent ell^n, followed by
the root scalar-extension unit and exact etale-to-pro-etale inverse image. The
normalized pullback maps retain the local root and pure-tensor formulas.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace WeilConjectures.PurityFiniteSetting

/-- The existing finite Tate sheaf at the universal annihilator ell^n. In particular
this includes ramified levels not divisible by e. Source: proposition-purity-vector-bundles,
coefficient identification (blueprint: def-pur-frame-kummer-class). -/
abbrev frameTwistEtale (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  Scheme.finiteEtaleTateSheaf P.Coefficient P.diagonalExponent X
    P.diagonalExponent_annihilates (d : ℤ)

/-- Its canonical inverse image on the small pro-etale site; this is the finite
root-tensor presentation of A(d), not a chosen trivialization.
Source: proposition-purity-vector-bundles, theta (blueprint: def-pur-frame-kummer-class). -/
abbrev frameTwist (P : PurityFiniteSetting.{u}) (X : Scheme.{u}) (d : ℕ) :=
  (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).obj (P.frameTwistEtale X d)

/-- The canonical pullback of the constant coefficient unit, including site comparison.
Source: proposition-purity-vector-bundles, restriction to the complementary open
(blueprint: def-pur-frame-kummer-class). -/
def frameConstantPullback (P : PurityFiniteSetting.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} P.Coefficient) f).obj (P.constant Y) ≅ P.constant X :=
  (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} P.Coefficient) f).app
      (P.constantEtale Y) ≪≫
    (comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) X).mapIso
      ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} P.Coefficient) f).app
        (ModuleCat.of P.Coefficient P.Coefficient))

end WeilConjectures.PurityFiniteSetting
