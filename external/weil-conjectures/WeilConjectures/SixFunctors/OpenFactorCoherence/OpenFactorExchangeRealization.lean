/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorCoherenceData
public import WeilConjectures.SixFunctors.OpenExchangeRoos.OpenExchangeRoosRestriction

/-! # Open-factor data in the fixed coefficient presentation

Source: blueprint proposition-composition-base-change-rf-shriek--1, open-factor paragraph;
Bhatt--Scholze 3.4.10, 6.5.5, 6.5.8; Stacks 099N, 09BN, 0GL1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
namespace WeilConjectures.OpenFactorCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Transport the strict completed exchange and its restricted unit square.
Source: Stacks 099N(2),(5), 09BN and 0D6D; blueprint open-factor steps 10--11.
(blueprint: lem-sf-open-factor-exchange-realization).

Proof: the projection-normalized coefficient transport identifies the fixed strict
pullback towers with the published completed-exchange presentation. Descend the
same tower isomorphisms to the normalized Pull comparisons, preserving their
representative equations and quotient units. The finite open inverse-unit
transpose descends to OrdinaryExchange, with theta given by the fixed ordinary
pullback compositors. Under these identifications the ordered Rlim exchange in hb
is exactly beta: first invert the horizontal pull comparison, then complete the
ordinary exchange, then use the augmentation-normalized open/Rlim comparison,
then the source pull comparison. The strict pullback square and exact restriction
Roos comparison exist on all ambient inputs, giving completedSquare. Their two
augmentation coordinates agree, yielding square_unit. The restriction equation
of hb gives beta_restriction after these same transports. The extension of the
completed a-pullback is complete by hb; the reflector universal property makes
precomposition with the actual horizontal quotient unit injective for this target.
Transport this injectivity across horizontal.comparison to obtain the final
clause. Thus no conservativity of separate finite-reduction evaluations is
assumed. The statements include empty schemes, identity horizontal arrows and
zero inputs; each follows from the identical strict unit formulas. -/
theorem openFactorExchangeRealization
    (F : FiniteFieldDatum.{u}) (hl : l ≠ F.p)
    (U' U X' X : Over (Spec (.of F.k)))
    [LocallyOfFiniteType U'.hom] [QuasiCompact U'.hom]
    [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (a : U' ⟶ U) (j' : U' ⟶ X') (j : U ⟶ X) (h : X' ⟶ X)
    [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
    (sq : OpenImmersionSquare a.left j'.left j.left h.left)
    (od : Open l E j.left) (od' : Open l E j'.left)
    (hb : OpenExchangeRoos.Assertion l E a.left j'.left j.left h.left
      (qc := OpenExchangeRoos.finiteOpenQC F U X j) sq) :
    ∃ (oh : Pull l E h.left) (oa : Pull l E a.left) (b : OrdinaryExchange l E sq)
      (r : integralDerivedPullback.{u, u} l E h.left ⋙ star l E j'.left ≅
        star l E j.left ⋙ integralDerivedPullback.{u, u} l E a.left),
      (∀ K : D l E X.left,
        (star l E j'.left).map ((oh.unit l E).app K) ≫ r.hom.app K =
          (theta l E sq).hom.app K ≫ (oa.unit l E).app ((star l E j.left).obj K)) ∧
      (∀ K : D l E U.left, sfIntegralConstructible l E U.left K →
        (star l E j'.left).map (beta l E b oh oa od' K) ≫
            od'.restrictionIso.hom.app ((integralDerivedPullback.{u, u} l E a.left).obj K) =
          r.hom.app ((J l E j.left).obj K) ≫
            (integralDerivedPullback.{u, u} l E a.left).map (od.restrictionIso.hom.app K)) ∧
      (∀ K : D l E U.left, sfIntegralConstructible l E U.left K →
        Function.Injective
          (fun v : (integralDerivedPullback.{u, u} l E h.left).obj
              ((J l E j.left).obj K) ⟶
              (J l E j'.left).obj ((integralDerivedPullback.{u, u} l E a.left).obj K) ↦
            (oh.unit l E).app ((J l E j.left).obj K) ≫ v)) := by sorry

end WeilConjectures.OpenFactorCoherence
