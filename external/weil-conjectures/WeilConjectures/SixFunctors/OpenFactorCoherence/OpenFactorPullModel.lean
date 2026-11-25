/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion

/-! # Normalized comparison of pullback and quotient completion

Source: blueprint main-20261015, proposition-composition-base-change-rf-shriek--1, base-change
paragraph; Bhatt--Scholze, Definition 3.4.10 and Lemmas 6.5.5, 6.5.8; Stacks 099N, 09BN, 0GL1
(blueprint: def-sf-pull-completion-comparison).

The record Pull retains the strict quotient-tower realization of the published operations.
Its normalizations do not choose replacement operation functors.
Natural-number level n always means exponent n+1. A tower comparison is an isomorphism
of strict complex-valued functors, with its components fixed before localization.

## Main definitions

- `Pull`: strict-tower and representative normalization of completed pullback.
- `Pull.unit`: the actual ordinary-to-completed quotient unit.
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

/-- The matching locally bijective criterion at the same size.
Source: Stacks 098K (blueprint: def-sf-pull-completion-comparison). -/
instance (priority := 4000) siteLocallyBijective (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The original ordinary derived category over B_W. Source: Stacks 099N
(blueprint: def-sf-pull-completion-comparison). -/
abbrev D (W : Scheme.{u}) := DerivedCategory (integralTowerModules.{u, u} l E W)

/-- Actual cochain representatives. Source: Stacks 05RU
(blueprint: def-sf-pull-completion-comparison). -/
abbrev Cx (W : Scheme.{u}) := CochainComplex (integralTowerModules.{u, u} l E W) ℤ

/-- Exact ambient extension, with the published ringed-slice adjunction.
Source: Stacks 03DI (blueprint: def-sf-pull-completion-comparison). -/
abbrev J {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (openExtension (completed l E) j).mapDerivedCategory

/-- Ordinary exact open restriction. Source: Stacks 09BN
(blueprint: def-sf-pull-completion-comparison). -/
abbrev star {U X : Scheme.{u}} (j : U ⟶ X) := pull (completed l E) j

/-- Exact termwise extension before localization. Source: Stacks 03DJ
(blueprint: def-sf-pull-completion-comparison). -/
abbrev jCx {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  (openExtension (completed l E) j).mapHomologicalComplex (.up ℤ)

/-- Ordinary pullback on complexes, over the actual completed coefficient map.
Source: Stacks 099N (blueprint: def-sf-pull-completion-comparison). -/
abbrev pullCx {U X : Scheme.{u}} (g : U ⟶ X) :=
  (proEtaleRingModulePullback g ((completed l E).ring X)
    ((completed l E).ring U) ((completed l E).pull g)).mapHomologicalComplex (.up ℤ)

/-- Fixed quotient completion on the global site. Source: Stacks 08TC
(blueprint: def-sf-pull-completion-comparison). -/
abbrev C (W : Scheme.{u}) := IntegralOnSlice.completion.{u, u} l E W none

/-- Its actual quotient-augmentation unit. Source: Stacks 08TC
(blueprint: def-sf-pull-completion-comparison). -/
abbrev eta (W : Scheme.{u}) := IntegralOnSlice.completionUnit.{u, u} l E W none

set_option genSizeOf false in
set_option genInjectivity false in
/-- The completion comparison of a geometric pullback is normalized by an entire strict
quotient tower and the pure tensor/unit formula, not by evaluations in derived categories.
Source: Stacks 099N(2),(5) (blueprint: def-sf-pull-completion-comparison). -/
structure Pull {U X : Scheme.{u}} (g : U ⟶ X) where
  source_good : ∀ P : Cx l E X, IntegralOnSlice.Good.{u, u} l E X none P →
    integralOperationsGoodComplex.{u, u} l E X P
  good : ∀ P : Cx l E X, IntegralOnSlice.Good.{u, u} l E X none P →
    IntegralOnSlice.Good.{u, u} l E U none ((pullCx l E g).obj P)
  tower : pullCx l E g ⋙ IntegralOnSlice.tower.{u, u} l E U none ≅
    integralOperationsPullbackTowerFunctor.{u, u} l E g
  generators : ∀ (P : Cx l E X) (n : ℕ) (i : ℤ) (V : X.ProEt)
      (x : (P.X i).val.obj (op V)),
    (((tower.hom.app P).app (op n)).f i).val.app
        (op ((proEtaleBaseChange g).obj V))
      (IntegralOnSlice.generator.{u, u} l E U none n (((pullCx l E g).obj P).X i)
        (op ((proEtaleBaseChange g).obj V)) 1
        (((proEtaleRingModuleAdjunction g ((completed l E).ring X)
          ((completed l E).ring U) ((completed l E).pull g)).unit.app (P.X i)).val.app
            (op V) x)) =
      integralOperationsPullbackGenerator.{u, u} l E g n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E X n).obj P).X i) V
        (unrestrictedIntegralTensorSection.{u, u} l E X n (P.X i) (op V) 1 x)
  comparison : star l E g ⋙ C l E U ≅ integralDerivedPullback.{u, u} l E g
  model : ∀ (P : Cx l E X) (hP : IntegralOnSlice.Good.{u, u} l E X none P),
    comparison.hom.app (DerivedCategory.Q.obj P) ≫
        (integralDerivedPullbackComparison.{u, u} l E g).hom.app ⟨P, source_good P hP⟩ =
      (C l E U).map
        ((proEtaleRingModulePullback g ((completed l E).ring X)
          ((completed l E).ring U) ((completed l E).pull g)).mapDerivedCategoryFactors.hom.app P) ≫
        (IntegralOnSlice.completionComparison.{u, u} l E U none).hom.app
          ⟨(pullCx l E g).obj P, good P hP⟩ ≫
        DerivedCategory.Q.map (integralOperationsRoosMap (tower.hom.app P))

/-- Ordinary-to-completed pullback, with the actual quotient unit from Pull.model.
Source: Stacks 099N (blueprint: def-sf-pull-completion-comparison). -/
def Pull.unit {U X : Scheme.{u}} {g : U ⟶ X} (p : Pull l E g) :
    star l E g ⟶ integralDerivedPullback.{u, u} l E g :=
  Functor.whiskerLeft (star l E g) (eta l E U) ≫ p.comparison.hom

end WeilConjectures.OpenFactorCoherence
