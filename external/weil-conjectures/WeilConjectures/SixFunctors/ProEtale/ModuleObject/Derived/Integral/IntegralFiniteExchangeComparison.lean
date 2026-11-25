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
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueExchange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResiduePerfect
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.IntegralReductionTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteExchangeComparison

/-! # Comparison of integral reduction with finite etale exchange

Source: Bhatt--Scholze, Sections 6.7--6.8
(blueprint: lem-weil-pbc-integral-finite-exchange-comparison).
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

/-- Reduction identifies the specified integral exchange with finite etale exchange.
Source: Bhatt--Scholze, Lemmas 6.5.4 and 6.5.11; Proposition 6.8.11(3);
comparison of the actual adjunction mates in `lem-weil-pbc-condensed-e-realization`
(blueprint: lem-weil-pbc-integral-finite-exchange-comparison).

Proof in words. O_E is finite free over ℤ_ℓ. Thus A = O_E/ℓ has discrete quotient
 topology. The ring object pulled from its condensed continuous functions
 is the constant A coefficient sheaf. Passing between internal module objects and
 sheaves of A modules retains the underlying abelian sheaves and scalar actions; the
 inverse constructions give an exact equivalence on derived categories. The bounded
 constructible reduction of M has finite constructible
 cohomology, so it is the pro-etale inverse image of a bounded etale complex L.
 Reduction commutes with pullback by the scalar tensor comparison. For direct image,
 use `integralModuleReductionSequence_shortExact` and exact monoidal inverse image
 from the point for the two-term finite free resolution of A over O_E. Preservation of finite
 triangles by Rf_* gives the actual scalar direct-image comparison. Site
 comparison identifies etale and pro-etale derived direct images of bounded-below
 etale objects. All comparisons are induced by the same underived adjunction maps.
 Thus they preserve units, counits and coherent pullback composition. Substitution in
 the unit-square-counit formula gives the asserted isomorphism of arrows, with the
 image of the displayed etale exchange as its target. No properness or Cartesian hypothesis and
 no exchange invertibility is used. -/
theorem integralFiniteExchange_comparison
    (sq : CommSq g' f' f g)
    (M : integralConstructible ℓ E X) :
    ∃ (F : DerivedCategory.Plus (Sheaf Y'.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} (integralResidue ℓ E)))) ⥤
        integralResidueDerived ℓ E Y')
      (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (integralResidue ℓ E))))),
      Nonempty (Arrow.mk ((integralReduction ℓ E Y').map
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
            (sq.asOver (Spec (.of k)))).app M).hom) ≅
        Arrow.mk (F.map ((Etale.baseChange
          (ModuleCat.{u + 1} (ULift.{u + 1} (integralResidue ℓ E))) sq).app L))) := by
  obtain ⟨N, _, ⟨e₁⟩⟩ := integralResidueExchange_comparison ℓ E k sq M
    (integralResidue_isDualizable ℓ E) (integralReduction_restrictTensor ℓ E)
  have hA : (ℓ : integralResidue ℓ E) = 0 := by
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  obtain ⟨F, L, ⟨e₂⟩⟩ :=
    finiteDiscreteExchange_comparison ℓ (integralResidue ℓ E) k hA sq N
  exact ⟨F, L, ⟨e₁ ≪≫ e₂⟩⟩

end AlgebraicGeometry.ProEtale.CondensedRing
