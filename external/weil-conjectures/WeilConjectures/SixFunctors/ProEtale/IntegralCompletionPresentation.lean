/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlat
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import WeilConjectures.Algebra.Homology.HomTensorDifferential
public import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
public import WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import WeilConjectures.SixFunctors.ProEtale.IntegralPresentationEncoding
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import WeilConjectures.CategoryTheory.InverseMateEquivalence
import WeilConjectures.CategoryTheory.StrictRoosModel
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares

/-! # Canonical completeness in the completed integral presentation

Stacks Project, Tags 06YY, 0941, 08TC and 0145
(auxiliary; not a blueprint node).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- The existing finite continuous-to-constant encoding, at exponent n+1.
Source: blueprint integral-limit and finite-coefficient conventions; Stacks 00YV
(auxiliary; not a blueprint node). -/
abbrev FiniteEncoding (n : ℕ) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  FiniteDiscreteOrdinary.Encoding (Padic.coefficientExtensionRing l E (n + 1)) X

end AlgebraicGeometry.ProEtale.IntegralPresentation
