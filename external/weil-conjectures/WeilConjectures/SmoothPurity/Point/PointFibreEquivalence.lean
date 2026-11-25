/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdQbarCategory
import WeilConjectures.SmoothPurity.Point.PointQbarFibreShiftDescent
import WeilConjectures.SmoothPurity.Point.PointRationalSectionsHom
import WeilConjectures.SmoothPurity.Point.PointRationalSectionsLattice
import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
import Mathlib.RingTheory.Localization.BaseChange
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
import WeilConjectures.ConstructibleSheaf.SpecializationCriterion
import WeilConjectures.CategoryTheory.FilteredTwoColimitTransport
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleSheafOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated

set_option linter.privateModule false

/-!
# Exact equivalences given by the four geometric-point fibre functors

Source: Weil blueprint, `lemma-perfect-complexes-geometric-point`, order 1509;
main-20261015, sec-six-functors-basics/sk-def-sf-admissible, order 1868
(blueprint: lem-weil-point-fibre-equivalence).

For the three full-subcategory targets, shifts and distinguished triangles are
expressed after their fully faithful inclusions into the ambient derived categories.
This is precisely the inherited shift and distinguished-triangle convention.
The fourth target uses its recorded common-stage distinguished-triangle predicate.
-/

@[expose] public section

set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

section ExactAdjunction

variable {C : Type*} {C' : Type*} [Category C] [Category C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C'] (L : C ⥤ C') (R : C' ⥤ C)
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

end ExactAdjunction

section FiniteReconstruction

variable (k B : Type u) [Field k] [IsAlgClosed k] [CommRing B] [Finite B]

end FiniteReconstruction

attribute [local irreducible] pointStageFibre pointStageFibreScalarIso pointQbarFibre
  Functor.mapDerivedCategory DerivedCategory.pointFdQbarStageComp

end WeilConjectures
