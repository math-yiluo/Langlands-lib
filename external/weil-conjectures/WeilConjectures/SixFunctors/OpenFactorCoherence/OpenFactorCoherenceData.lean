/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarCompletedPullback
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Completed.Open.CompletedOpenExchangeTransport
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
-- Existing reduction and open scalar mate: def-sf-open-reduction-coefficient-mate.
public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison

public import WeilConjectures.SixFunctors.OpenFactorCoherence.OpenFactorTensorModel

/-! # Fixed open-factor operations and normalized comparison data

Source: blueprint proposition-composition-base-change-rf-shriek--1, open-factor paragraph;
Bhatt--Scholze 3.4.10 and 6.5.8; Stacks 099N, 09BN, 0GL1.
(blueprint: def-sf-open-factor-fixed-data).

These are the existing open-factor definitions, extracted unchanged so that the
three realization lemmas can use their types before the final assembly theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.IntegralOnSlice.abSheafify
attribute [-instance] WeilConjectures.IntegralOnSlice.abLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport

namespace WeilConjectures.OpenFactorCoherence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option genSizeOf false in
set_option genInjectivity false in
/-- Canonical completion/open commutation and all of clauses (1) and (2).
The strict tower comparison is fixed by the actual quotient augmentation.
Source: Stacks 099N, 09BN, 0E8I
(blueprint: lem-sf-pf-open-factor-coherence). -/
structure Open {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] where
  tower : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ≅
    IntegralOnSlice.tower.{u, u} l E U none ⋙
      (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j)
  tower_unit : ∀ (P : Cx l E U) (n : ℕ),
    ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
        (op n) ≫ (tower.hom.app P).app (op n) =
      (jCx l E j).map (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))
  tower_unique : ∀ v : jCx l E j ⋙ IntegralOnSlice.tower.{u, u} l E X none ⟶
      IntegralOnSlice.tower.{u, u} l E U none ⋙
        (Functor.whiskeringRight ℕᵒᵖ (Cx l E U) (Cx l E X)).obj (jCx l E j),
    (∀ (P : Cx l E U) (n : ℕ),
      ((IntegralOnSlice.augmentation.{u, u} l E X none).app ((jCx l E j).obj P)).app
          (op n) ≫ (v.app P).app (op n) =
        (jCx l E j).map
          (((IntegralOnSlice.augmentation.{u, u} l E U none).app P).app (op n))) →
      v = tower.hom
  commutes : J l E j ⋙ C l E X ≅ C l E U ⋙ J l E j
  unit_commutes : ∀ K : D l E U,
    (eta l E X).app ((J l E j).obj K) ≫ commutes.hom.app K =
      (J l E j).map ((eta l E U).app K)
  commutes_unique : ∀ v : J l E j ⋙ C l E X ⟶ C l E U ⋙ J l E j,
    (∀ K : D l E U, (eta l E X).app ((J l E j).obj K) ≫ v.app K =
      (J l E j).map ((eta l E U).app K)) → v = commutes.hom
  restriction_complete : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsSfDerivedComplete l E U ((star l E j).obj K)
  extension_complete : ∀ K : D l E U, IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E X ((J l E j).obj K)
  pull : Pull l E j
  pull_unit : ∀ K : D l E X, IsSfDerivedComplete l E X K →
    IsIso ((pull.unit l E).app K)
  restrictionIso : J l E j ⋙ star l E j ≅ 𝟭 (D l E U)
  section_unit : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j).unit.app K ≫ restrictionIso.hom.app K = 𝟙 K
  fullyFaithful : ∀ (K L : D l E U), IsSfDerivedComplete l E U K →
    IsSfDerivedComplete l E U L → Function.Bijective
      (fun f : K ⟶ L ↦ (J l E j).map f)
  constructible : ∀ K : D l E U, sfIntegralConstructible l E U K →
    sfIntegralConstructible l E X ((J l E j).obj K)
  restriction_constructible : ∀ P : D l E X, sfIntegralConstructible l E X P →
    sfIntegralConstructible l E U ((star l E j).obj P)
  reduction_iso : ∀ (K : D l E U) (n : ℕ), sfIntegralConstructible l E U K →
    IsIso ((PurCompactSupport.openComparison
      (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) j).app K)
  interval : ∀ (K : D l E U) (n : ℕ) (a b : ℤ),
    sfIntegralConstructible l E U K →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E U n).obj K) ⊆
      Set.Icc a b →
    proEtaleCohomologicalSupport ((scalarReductionDerivedExtension.{u, u} l E X n).obj
      ((J l E j).obj K)) ⊆ Set.Icc a b

/-- Completion of the actual ambient open tensor map, transported to the recorded
completed tensor. This is the supplied gamma of def-exchange-projection.
Source: Stacks 0GL1 and Bhatt--Scholze 3.4.10
(blueprint: lem-sf-pf-open-factor-coherence). -/
def gamma {U X : Scheme.{u}} {j : U ⟶ X} [IsOpenImmersion j]
    (o : Open l E j) (tU : Tensor l E U) (tX : Tensor l E X)
    (K : D l E U) (P : D l E X) :
    (integralCompletedTensor.{u, u} l E X).obj ((J l E j).obj K, P) ⟶
      (J l E j).obj ((integralCompletedTensor.{u, u} l E U).obj (K, (star l E j).obj P)) :=
  tX.comparison.inv.app ((J l E j).obj K, P) ≫
    (C l E X).map ((openProjectionIso (completed l E) j
      tU.ordinary tX.ordinary K P).hom) ≫
    o.commutes.hom.app (tU.ordinary.tensor.obj (K, (star l E j).obj P)) ≫
    (J l E j).map (tU.comparison.hom.app (K, (star l E j).obj P))

/-- The ordinary pullback square, with the published composition normalization.
Source: Stacks 0D6D (blueprint: lem-sf-pf-open-factor-coherence). -/
def theta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} (sq : OpenImmersionSquare a j' j h) :
    star l E h ⋙ star l E j' ≅ star l E j ⋙ star l E a :=
  (geometricPullComposition (completed l E) j' h (completedPull_comp l E j' h)).symm ≪≫
    eqToIso (congrArg (fun f : U' ⟶ X ↦ star l E f) sq.w.symm) ≪≫
    geometricPullComposition (completed l E) a j (completedPull_comp l E a j)

set_option genSizeOf false in
set_option genInjectivity false in
/-- The ambient base-change map is fixed by the inverse open-unit transpose.
Source: Stacks 09BN (blueprint: lem-sf-pf-open-factor-coherence). -/
structure OrdinaryExchange {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : OpenImmersionSquare a j' j h) where
  comparison : J l E j ⋙ star l E h ≅ star l E a ⋙ J l E j'
  inverse : ∀ K : D l E U,
    (openDerivedAdjunction (completed l E) j').homEquiv _ _ (comparison.inv.app K) =
      (star l E a).map ((openDerivedAdjunction (completed l E) j).unit.app K) ≫
        (theta l E sq).inv.app ((J l E j).obj K)

/-- The strict-reduction completed exchange, expressed through the quotient completion
comparisons. Pull.model retains the strict finite maps; Open.unit_commutes fixes the
extension/limit comparison. Source: Stacks 099N and 09BN
(blueprint: lem-sf-pf-open-factor-coherence). -/
def beta {U' U X' X : Scheme.{u}} {a : U' ⟶ U} {j' : U' ⟶ X'}
    {j : U ⟶ X} {h : X' ⟶ X} [IsOpenImmersion j] [IsOpenImmersion j']
    {sq : OpenImmersionSquare a j' j h} (b : OrdinaryExchange l E sq)
    (oh : Pull l E h) (oa : Pull l E a) (oj' : Open l E j') (K : D l E U) :
    (integralDerivedPullback.{u, u} l E h).obj ((J l E j).obj K) ⟶
      (J l E j').obj ((integralDerivedPullback.{u, u} l E a).obj K) :=
  oh.comparison.inv.app ((J l E j).obj K) ≫
    (C l E X').map (b.comparison.hom.app K) ≫
    oj'.commutes.hom.app ((star l E a).obj K) ≫
    (J l E j').map (oa.comparison.hom.app K)

end WeilConjectures.OpenFactorCoherence
