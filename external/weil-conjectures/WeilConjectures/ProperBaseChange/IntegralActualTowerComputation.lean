/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.IntegralStrictModelChainTransport
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionData
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ZetaWeil.ProfiniteCoefficientSliceBaseChange
import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import all WeilConjectures.ProperBaseChange.IntegralCoefficientPresentation.IntegralCoefficientPresentationComparison

/-! # Natural computation of the actual pulled reduction tower

Source: Stacks 03D3, 06YY and 099N(5).
(blueprint: lem-weil-pbc-integral-actual-tower-computation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedReductionTower pbcIntegralDatum
  integralDetailedCoefficientComparison Functor.mapDerivedCategory HasDerivedCategory.standard
attribute [local implicit_reducible] pbcIntegralActualTowerFunctor

private theorem actualTowerCounit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    IsIso (pbcIntegralActualTowerCounit l E h P.obj) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  have hk := @restrictIso_kflat.{u} T.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T) _ _
    (purCoefficientIso l E T) P.obj P.property.1
  have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E T).exists.choose_spec
  change (adicLisseForget T).map (purCoefficientIso l E T).hom =
    (integralDetailedCoefficientComparison T l E).hom at he
  rw [he] at hk
  have hred := towerCounit_isIso T (pbcIntegralDatum l E)
    ((pbcIntegralTransportComplex T l E).obj P.obj) hk
  have hpull : IsIso (completedTowerPullbackComplexCounit h (pbcIntegralDatum l E)
      ((completedReductionComplexTowerFunctor T (pbcIntegralDatum l E)).obj
        ((pbcIntegralTransportComplex T l E).obj P.obj))) :=
    completedReductionPullbackCounit_isIso h (pbcIntegralDatum l E) _
  unfold pbcIntegralActualTowerCounit
  exact completedReduction_invertibleComposite _ _ _ _ _ (by infer_instance) hred hpull

private def actualTowerCounitNat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :=
  Functor.whiskerRight
      (Functor.whiskerRight (pbcIntegralDetailedTransportFactors T l E).hom
          (completedReductionTower T (pbcIntegralDatum l E)) ≫
        Functor.whiskerLeft (pbcIntegralTransportComplex T l E)
          (completedReductionTowerComplexNat (pbcIntegralDatum l E) T))
      (completedTowerPullback h (pbcIntegralDatum l E)) ≫
    Functor.whiskerLeft
      (pbcIntegralTransportComplex T l E ⋙
        completedReductionComplexTowerFunctor T (pbcIntegralDatum l E))
      (completedReductionPullbackComplexNat h (pbcIntegralDatum l E))

/-- Scalar transport is an equivalence, and the actual tower computation is natural
and invertible on good complexes.

Source: Stacks 03D3, 06YY and 099N(5).
(blueprint: lem-weil-pbc-integral-actual-tower-computation).

Proof: lift the normalized coefficient comparison to a ring-sheaf isomorphism.
Restriction along an isomorphism has an inverse scalar restriction, so it is an
equivalence. It preserves K-flatness; apply the existing reduction-tower counit
computation to the transported good complex. The coefficient inverse-image map
is invertible, hence ordinary tower pullback is exact and its derived counit is
invertible on every complex. Compose these two counits and the exact scalar
transport factor. Their existing naturality squares compose to a natural
transformation. Its component is the literal actual-tower counit, so the preceding
invertibility computation applies on good complexes. -/
theorem pbc_integral_actual_tower_computation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T) :
    (pbcIntegralTransportModules U l E).IsEquivalence ∧
    (∀ P : (integralOperationsGoodComplex l E T).FullSubcategory,
      IsIso (pbcIntegralActualTowerCounit l E h P.obj)) ∧
    ∃ c : DerivedCategory.Q ⋙ integralDetailedTransport T l E ⋙
        completedReductionTower T (pbcIntegralDatum l E) ⋙
          completedTowerPullback h (pbcIntegralDatum l E) ⟶
        pbcIntegralActualTowerFunctor l E h ⋙ DerivedCategory.Q,
      ∀ P : CochainComplex (integralTowerModules l E T) ℤ,
        c.app P = pbcIntegralActualTowerCounit l E h P := by
  have he := congrArg Iso.hom (purCoefficientIso_existsUnique l E U).exists.choose_spec
  change (adicLisseForget U).map (purCoefficientIso l E U).hom =
    (integralDetailedCoefficientComparison U l E).hom at he
  have hH : (pbcIntegralTransportModules U l E).IsEquivalence := by
    have hh := (IntegralCoefficientPresentation.restrict_equivalence
      (purCoefficientIso l E U)).1
    change (SheafOfModules.restrictScalars
      ((adicLisseForget U).map (purCoefficientIso l E U).hom)).IsEquivalence at hh
    rwa [he] at hh
  let c : DerivedCategory.Q ⋙ integralDetailedTransport T l E ⋙
        completedReductionTower T (pbcIntegralDatum l E) ⋙
          completedTowerPullback h (pbcIntegralDatum l E) ⟶
        pbcIntegralActualTowerFunctor l E h ⋙ DerivedCategory.Q :=
    { app := fun P ↦ pbcIntegralActualTowerCounit l E h P
      naturality := fun P Q f ↦ (actualTowerCounitNat l E h).naturality f }
  refine ⟨hH, actualTowerCounit_isIso l E h, c, ?_⟩
  intro P
  rfl

end WeilConjectures
