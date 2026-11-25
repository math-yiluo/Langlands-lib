/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeSourceAdjunct
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralExchangeTargetAdjunct

/-! # Coherence of integral localization and the specified exchange map -/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

variable {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  [f.IsOver (Spec (.of k))] [g.IsOver (Spec (.of k))]
  [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

/-- The proposition of `integralConstructible_exchange_equality`, named so that the theorem's
elaborated type stays small (the inline equation is very large once elaborated). -/
abbrev integralConstructibleExchangeEqualityStatement
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) : Prop :=
  integralConstructibleSourceHom ℓ E k f g K ≫
      (ContinuousMapRingObj.boundedConstructibleBaseChange ℓ E (sq.asOver (Spec (.of k)))).app
        ((integralScalarConstructible ℓ E X).obj K) =
    (integralScalarConstructible ℓ E Y').map
        ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
          (sq.asOver (Spec (.of k)))).app K) ≫
      integralConstructibleTargetHom ℓ E k f' g' K

/-- Integral coefficient extension respects the specified exchange arrow.
Source: Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-weil-pbc-continuous-integral-exchange-equality).
Proof. Apply injectivity of the inverse bounded f′ adjunction hom-equivalence. The source
and target adjunct calculations identify both sides with the same explicit composite. -/
theorem integralConstructible_exchange_equality
    (sq : CommSq g' f' f g) (K : integralConstructible ℓ E X) :
    integralConstructibleExchangeEqualityStatement ℓ E k f g f' g' sq K := by
  have h := (integralConstructible_exchange_source_adjunct ℓ E k f g f' g' sq K).trans
    (integralConstructible_exchange_target_adjunct ℓ E k f g f' g' sq K).symm
  have h2 := ((ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E
    (f'.asOver (Spec (.of k)))).homEquiv _ _).symm.injective h
  exact h2

end AlgebraicGeometry.ProEtale.CondensedRing
