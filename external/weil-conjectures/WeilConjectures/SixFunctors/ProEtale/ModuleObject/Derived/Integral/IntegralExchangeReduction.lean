/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import Mathlib.Analysis.Normed.Algebra.Ultra
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Ring.Ideal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.NumberTheory.Padics.ProperSpace
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFiniteExchangeComparison
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-! # Finite reduction of the integral proper exchange

Source: Bhatt--Scholze, Sections 6.7--6.8 (blueprint: lem-weil-pbc-integral-exchange-reduction).
-/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
  [FiniteDimensional ℚ_[ℓ] E]

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The proper exchange on integral constructible complexes becomes invertible modulo ℓ.
Source: Bhatt--Scholze, Section 6.7 and the integral finite-quotient comparison of Section 6.8;
Stacks proper base change (blueprint: lem-weil-pbc-integral-exchange-reduction).

Proof in words. The quotient O_E/ℓ is finite, since O_E is finite over ℤ_ℓ. Its quotient
 topology is discrete and its condensed coefficient sheaf on the pro-etale site is the
 inverse image of the constant finite coefficient sheaf on the etale site. A bounded
 constructible integral complex has a bounded constructible derived reduction over this
 finite ring. Reduction commutes with exact pullback. For proper pushforward, compute the
 reduction by the two-term free resolution of O_E/ℓ over O_E and use preservation of
 finite cones by the derived pushforward. The adjunction comparisons identify the
 reduced unit, pullback square and counit with the finite-coefficient ones, hence identify
 the specified reduced exchange arrow with etale exchange. Torsion proper base change
 makes that arrow invertible. Transport through the actual comparisons yields the
 asserted invertibility, without assuming integral or E exchange invertible. -/
theorem integralExchange_reduction_isIso [IsProper f]
    (sq : IsPullback g' f' f g)
    (M : integralConstructible ℓ E X) :
    IsIso ((integralReduction ℓ E Y').map
      ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
        (sq.toCommSq.asOver (Spec (.of k)))).app M).hom) := by
  obtain ⟨F, L, ⟨e⟩⟩ := integralFiniteExchange_comparison ℓ E k sq.toCommSq M
  have htors : IsAddTorsion (ULift.{u + 1} (integralResidue ℓ E)) := by
    intro x
    exact isOfFinAddOrder_of_finite x
  have hbc : IsIso (Etale.baseChange
      (ModuleCat.{u + 1} (ULift.{u + 1} (integralResidue ℓ E))) sq.toCommSq) :=
    Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring
      (ULift.{u + 1} (integralResidue ℓ E)) htors sq
  have hfiniteBC : IsIso (F.map ((Etale.baseChange
      (ModuleCat.{u + 1} (ULift.{u + 1} (integralResidue ℓ E))) sq.toCommSq).app L)) :=
    inferInstance
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 hfiniteBC

end AlgebraicGeometry.ProEtale.CondensedRing
