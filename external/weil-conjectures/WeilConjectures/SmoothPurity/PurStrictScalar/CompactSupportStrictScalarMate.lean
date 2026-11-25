/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.ScalarReductionTowerBalancing
public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateEvaluationData
public import WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData

import all WeilConjectures.SmoothPurity.PurStrictScalar.FiniteScalarCoordinateData
import all WeilConjectures.SmoothPurity.Completed.CompletedIntegralFiniteFree
import all WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import all WeilConjectures.CategoryTheory.SmoothPurity.AdicBasisLimit
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarMateFiniteEvaluation
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import WeilConjectures.SmoothPurity.PurStrictScalar.StrictProperBiproductCoordinate

/-! # Finite scalar proper/open mate on strict compact-support reduction towers

Source: Stacks 07A6, 0B56, 0940 and 0E8I.
(blueprint: lem-pur-compact-support-strict-scalar-mate).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] AlgebraicGeometry.ProEtale.VaryingRing.exactAdj
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] CategoryTheory.Functor.rightDerivedFunctorIsoMapDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcScalarAdjunction
  AlgebraicGeometry.Scheme.pbcDerivedScalarAdjunction
  WeilConjectures.PurCompactSupport.finiteChange
  WeilConjectures.PurCompactSupport.projection
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryFactors
attribute [local irreducible] WeilConjectures.PurStrictScalar.ordinaryReduction
  WeilConjectures.PurStrictScalar.ordinaryReductionAdj
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.PurStrictScalar
attribute [local irreducible] AlgebraicGeometry.ProEtale.StrictTower.adj
  scalarAdj properRestriction

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The canonical pullback/tensor balancing square on whole strict towers, fixed
by the normalized scalar and geometric composite adjunctions.
Source: Stacks 07A6, 0B56 (blueprint: lem-pur-compact-support-strict-scalar-mate). -/
def strictScalarPull {Z W : Scheme.{u}} (g : Z ⟶ W) :
    G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g ⋙ T l E F i Z ≅
      T l E F i W ⋙ G (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g :=
  (((adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) g).comp
    (scalarAdj l E F i Z)).ofNatIsoRight (properRestriction l E F i g).symm).leftAdjointUniq
      ((scalarAdj l E F i W).comp
        (adj (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) g))

section BasisTransport
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Scheme.proEtaleRingModuleAdjunction
  AlgebraicGeometry.Scheme.proEtaleRingModulePullback

end BasisTransport

section MateInvertibility
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end MateInvertibility

section FiniteField
variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))] [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))] [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))] [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

end FiniteField

end WeilConjectures.PurStrictScalar
