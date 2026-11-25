/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteModuleCategoriesSupplement
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.ProperBaseChange.ExchangeChain.AdjunctionExchangeChain
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteEtaleRealizationFull
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # The finite discrete coefficient realization and three-step comparisons

The realization functor and the three-step diagram comparisons, split out of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRealizationFunctor`
so that they do not import the bounded
constructible six functors.
-/

@[expose] public section

universe u

open CategoryTheory Limits

-- Keep hom types on the category's direct quiver, including the diagram records.
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_finiteDiscreteRealizationCore
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

/-- Four isomorphisms identifying the three consecutive arrows in two diagrams. -/
structure FiniteDiscreteThreeStepComparison {C : Type*} [Category C]
    {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    (a : A0 ⟶ A1) (b : A1 ⟶ A2) (c : A2 ⟶ A3)
    (d : B0 ⟶ B1) (e : B1 ⟶ B2) (f : B2 ⟶ B3) where
  e0 : A0 ≅ B0
  e1 : A1 ≅ B1
  e2 : A2 ≅ B2
  e3 : A3 ≅ B3
  first : a ≫ e1.hom = e0.hom ≫ d
  second : b ≫ e2.hom = e1.hom ≫ e
  third : c ≫ e3.hom = e2.hom ≫ f

/-- Compose the three commuting squares. -/
noncomputable def FiniteDiscreteThreeStepComparison.arrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    Arrow.mk (a ≫ b ≫ c) ≅ Arrow.mk (d ≫ e ≫ f) :=
  Arrow.isoMk h.e0 h.e3 (by
    change h.e0.hom ≫ (d ≫ e ≫ f) = (a ≫ b ≫ c) ≫ h.e3.hom
    symm
    simp only [Category.assoc]
    rw [h.third, reassoc_of% h.second, reassoc_of% h.first])

/-- The three commuting squares identify their composite arrows.
Source: Mathlib `Arrow.isoMk`
(blueprint: lem-weil-pbc-three-step-arrow-comparison).

Proof. Reassociate and substitute the third, second and first square equations.
Use the endpoint isomorphisms in Arrow.isoMk. -/
theorem FiniteDiscreteThreeStepComparison.nonemptyArrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f) :
    Nonempty (Arrow.mk (a ≫ b ≫ c) ≅ Arrow.mk (d ≫ e ≫ f)) := ⟨h.arrowIso⟩

/-- Apply the three-step interface to arrows with specified factorizations. -/
theorem FiniteDiscreteThreeStepComparison.nonemptyArrowIsoOfFactorizations
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    (h : FiniteDiscreteThreeStepComparison a b c d e f)
    {η : A0 ⟶ A3} {θ : B0 ⟶ B3}
    (hη : η = a ≫ b ≫ c) (hθ : θ = d ≫ e ≫ f) :
    Nonempty (Arrow.mk η ≅ Arrow.mk θ) := by
  rw [hη, hθ]
  exact h.nonemptyArrowIso

/-- Three specified factors for each arrow, with their comparison squares. -/
structure FiniteDiscreteFactoredComparison {C : Type*} [Category C]
    {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    (a : A0 ⟶ A1) (b : A1 ⟶ A2) (c : A2 ⟶ A3)
    (d : B0 ⟶ B1) (e : B1 ⟶ B2) (f : B2 ⟶ B3)
    (η : A0 ⟶ A3) (θ : B0 ⟶ B3) where
  comparison : FiniteDiscreteThreeStepComparison a b c d e f
  source_eq : η = a ≫ b ≫ c
  target_eq : θ = d ≫ e ≫ f

/-- The comparison interface remembers the specified total arrows as well as their factors. -/
theorem FiniteDiscreteFactoredComparison.nonemptyArrowIso
    {C : Type*} [Category C] {A0 A1 A2 A3 B0 B1 B2 B3 : C}
    {a : A0 ⟶ A1} {b : A1 ⟶ A2} {c : A2 ⟶ A3}
    {d : B0 ⟶ B1} {e : B1 ⟶ B2} {f : B2 ⟶ B3}
    {η : A0 ⟶ A3} {θ : B0 ⟶ B3}
    (h : FiniteDiscreteFactoredComparison a b c d e f η θ) :
    Nonempty (Arrow.mk η ≅ Arrow.mk θ) :=
  h.comparison.nonemptyArrowIsoOfFactorizations h.source_eq h.target_eq

namespace ExchangeChain

/-- A comparison retaining its two diagrams as arguments.
(blueprint: def-weil-pbc-three-step-chain-comparison). -/
def Comparison {C : Type*} [Category C] (s t : ExchangeChain C) :=
  FiniteDiscreteThreeStepComparison s.first s.second s.third t.first t.second t.third

/-- Two actual arrows with specified three-step diagrams and a comparison of those diagrams. -/
structure FactoredComparison {C : Type*} [Category C] (s t : ExchangeChain C)
    (η : s.obj0 ⟶ s.obj3) (θ : t.obj0 ⟶ t.obj3) where
  comparison : Comparison s t
  source_eq : η = s.composite
  target_eq : θ = t.composite

/-- Recover the original arrow-level interface without changing any vertex or arrow. -/
def FactoredComparison.toOriginal {C : Type*} [Category C] {s t : ExchangeChain C}
    {η : s.obj0 ⟶ s.obj3} {θ : t.obj0 ⟶ t.obj3} (h : FactoredComparison s t η θ) :
    FiniteDiscreteFactoredComparison s.first s.second s.third
      t.first t.second t.third η θ :=
  ⟨h.comparison, h.source_eq, h.target_eq⟩

/-- The retained factorizations identify their original total arrows. -/
theorem FactoredComparison.nonemptyArrowIso {C : Type*} [Category C]
    {s t : ExchangeChain C} {η : s.obj0 ⟶ s.obj3} {θ : t.obj0 ⟶ t.obj3}
    (h : FactoredComparison s t η θ) : Nonempty (Arrow.mk η ≅ Arrow.mk θ) :=
  h.toOriginal.nonemptyArrowIso

end ExchangeChain

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (T : Scheme.{u})
  (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T)

/-- Realization is inverse image from the etale site followed by the given exact
coefficient equivalence, applied termwise to complexes. -/
@[irreducible] noncomputable def finiteDiscreteRealization :
    FiniteDiscreteEtalePlus B T ⥤ DerivedCategory (FiniteDiscreteInternalModules B T) :=
  DerivedCategory.Plus.ι ⋙
    D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)]) ⋙ D(E.functor)

noncomputable instance : (finiteDiscreteRealization B T E).CommShift ℤ := by
  unfold finiteDiscreteRealization
  infer_instance

instance : (finiteDiscreteRealization B T E).IsTriangulated := by
  unfold finiteDiscreteRealization
  infer_instance

instance : (finiteDiscreteRealization B T E).Full := by
  let V := DerivedCategory.Plus.ι ⋙
    D(ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)])
  have : V.Full := finiteDiscreteEtaleRealization_full B T
  exact inferInstanceAs (V ⋙ D(E.functor)).Full

/-- A sheaf in the underived realization has its single complex in the derived
realization's essential image. This is purely functorial and needs no descent theorem.
(blueprint: lem-weil-pbc-finite-discrete-single-realization)

Proof. Put the etale sheaf in degree zero, commute each of the two exact functors
with the single-complex functor, and apply the supplied sheaf isomorphism. -/
theorem finiteDiscreteRealization_single
    (M : FiniteDiscreteInternalModules B T)
    (hM : (ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)] ⋙ E.functor).essImage M) :
    (finiteDiscreteRealization B T E).essImage
      ((DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨A, ⟨e⟩⟩ := hM
  refine ⟨(DerivedCategory.Plus.singleFunctor _ 0).obj A, ⟨?_⟩⟩
  unfold finiteDiscreteRealization
  exact D(E.functor).mapIso
      ((ν^*(T)[ModuleCat.{u + 1} (ULift.{u + 1} B)]).mapDerivedCategorySingleFunctor 0 |>.app A) ≪≫
    (E.functor.mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso e

end AlgebraicGeometry.ProEtale.CondensedRing
