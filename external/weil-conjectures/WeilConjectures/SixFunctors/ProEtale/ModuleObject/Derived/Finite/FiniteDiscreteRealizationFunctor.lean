/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteModuleCategoriesSupplement
public import WeilConjectures.ProperBaseChange.FiniteDiscreteThreeStepComparison.FiniteDiscreteRealizationCore
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueComparisonInterface
public import WeilConjectures.ProperBaseChange.ExchangeChain.AdjunctionExchangeChain
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteEtaleRealizationFull
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison

/-! # Deriving the finite discrete coefficient realization -/

@[expose] public section

universe u

open CategoryTheory Limits

-- Keep hom types on the category's direct quiver, including the diagram records.
attribute [local instance 10000] CategoryTheory.CategoryStruct.toQuiver
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_finiteDiscreteRealizationFunctor
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] upperStarFromPoint upperStarFromPointComp
  monoidal_upperStarFromPoint laxBraided_upperStarFromPoint

section ExchangeStepCache

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
  [hTd : DiscreteTopology T] [hTf : Finite T] [hT : Fact (IsNilpotent (ℓ : T))]

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]

include ℓ k hTd hTf hT

variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)

end ExchangeStepCache

variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

variable (T : Scheme.{u})
  (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T)

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
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

open Scheme

/-- The actual internal exchange diagram, retaining its four ambient vertices.
(blueprint: def-weil-pbc-ambient-typed-bounded-exchange). -/
noncomputable def coefficientInternalExchangeChain
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (sq : CommSq g' f' f g)
    (K : residueExchangeDerived Λ X) : ExchangeChain (residueExchangeDerived Λ Y') :=
  Adjunction.exchangeChain (residueExchangeAdjunction Λ f)
    (residueExchangeAdjunction Λ f') (residueExchangeSquare Λ sq).hom K

/-- The actual etale exchange diagram, retaining its four vertices.
(blueprint: def-weil-pbc-ambient-typed-etale-exchange). -/
noncomputable def coefficientEtaleExchangeChain (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    ExchangeChain (FiniteDiscreteEtalePlus B₀ Y') :=
  Adjunction.exchangeChain
    (Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) f)
    (Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) f')
    (Etale.pullbackSquareComparison (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).hom L

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The original bounded exchange with endpoints fixed by its actual exchange diagram.
Source: boundedConstructibleBaseChange.
(blueprint: def-weil-pbc-ambient-typed-bounded-exchange). -/
noncomputable def coefficientAmbientBoundedExchange
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    (coefficientInternalExchangeChain (Profinite.continuousMapRingObj T) sq K.obj).obj0 ⟶
      (coefficientInternalExchangeChain (Profinite.continuousMapRingObj T) sq K.obj).obj3 :=
  ((FiniteDiscreteRingObj.boundedConstructibleBaseChange ℓ T (sq.asOver (Spec (.of k)))).app K).hom

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The typed cache is exactly the original bounded exchange component. -/
theorem coefficientAmbientBoundedExchange_eq
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    coefficientAmbientBoundedExchange ℓ k T sq K =
      ((FiniteDiscreteRingObj.boundedConstructibleBaseChange ℓ T
        (sq.asOver (Spec (.of k)))).app K).hom := by
  unfold coefficientAmbientBoundedExchange
  rfl

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar in
/-- The bounded exchange factors through the three actual diagram arrows. -/
theorem coefficientAmbientBoundedExchange_factorization
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    coefficientAmbientBoundedExchange ℓ k T sq K =
      (coefficientInternalExchangeChain (Profinite.continuousMapRingObj T) sq K.obj).composite := by
  rw [coefficientAmbientBoundedExchange_eq]
  exact (FiniteDiscreteRingObj.boundedConstructibleBaseChange_hom_eq_ambient ℓ k T sq K).trans
    (Adjunction.mate_eq_exchangeChain_composite
      (residueExchangeAdjunction (Profinite.continuousMapRingObj T) f)
      (residueExchangeAdjunction (Profinite.continuousMapRingObj T) f')
      (residueExchangeSquare (Profinite.continuousMapRingObj T) sq).hom K.obj)

/-- The original etale exchange, with endpoints fixed by its actual exchange diagram.
Source: Etale.baseChange.
(blueprint: def-weil-pbc-ambient-typed-etale-exchange). -/
noncomputable def coefficientEtaleExchange (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    (coefficientEtaleExchangeChain B₀ sq L).obj0 ⟶
      (coefficientEtaleExchangeChain B₀ sq L).obj3 :=
  (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L

/-- The typed bounded cache retains the original arrow, including both endpoints. -/
theorem coefficientAmbientBoundedExchange_arrow_eq
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]
    (sq : CommSq g' f' f g)
    (K : ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    Arrow.mk (coefficientAmbientBoundedExchange ℓ k T sq K) =
      Arrow.mk (((FiniteDiscreteRingObj.boundedConstructibleBaseChange ℓ T
        (sq.asOver (Spec (.of k)))).app K).hom) := by
  unfold coefficientAmbientBoundedExchange coefficientInternalExchangeChain
    Adjunction.exchangeChain residueExchangeUpperStar residueExchangeLowerStar
    FiniteDiscreteRingObj.boundedConstructibleLowerStar boundedConstructibleUpperStar
  rfl

/-- The mapped typed etale cache retains the original mapped arrow and its endpoints. -/
theorem coefficientEtaleExchange_map_arrow_eq (B₀ : Type) [CommRing B₀]
    {D : Type*} [Category D] (F : FiniteDiscreteEtalePlus B₀ Y' ⥤ D)
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    Arrow.mk ((coefficientEtaleExchangeChain B₀ sq L).mapHom F
        (coefficientEtaleExchange B₀ sq L)) =
      Arrow.mk (F.map ((Etale.baseChange
        (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L)) := by
  unfold ExchangeChain.mapHom coefficientEtaleExchange
  rfl

/-- The typed etale cache is exactly the original exchange component. -/
theorem coefficientEtaleExchange_eq (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    coefficientEtaleExchange B₀ sq L =
      (Etale.baseChange (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq).app L := by
  unfold coefficientEtaleExchange
  rfl

/-- The etale exchange factors through the three actual diagram arrows. -/
theorem coefficientEtaleExchange_factorization (B₀ : Type) [CommRing B₀]
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    coefficientEtaleExchange B₀ sq L =
      (coefficientEtaleExchangeChain B₀ sq L).composite := by
  rw [coefficientEtaleExchange_eq]
  unfold coefficientEtaleExchangeChain
  rw [Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus_eq_derivedPlus]
  exact (Etale.baseChange_app_eq_mateEquiv
    (ModuleCat.{u + 1} (ULift.{u + 1} B₀)) sq L).trans
      (Adjunction.mate_eq_exchangeChain_composite _ _ _ _)

/-- Every functor preserves this specified etale exchange factorization. -/
theorem coefficientEtaleExchange_map_factorization (B₀ : Type) [CommRing B₀]
    {D : Type*} [Category D] (F : FiniteDiscreteEtalePlus B₀ Y' ⥤ D)
    (sq : CommSq g' f' f g) (L : FiniteDiscreteEtalePlus B₀ X) :
    (coefficientEtaleExchangeChain B₀ sq L).mapHom F
        (coefficientEtaleExchange B₀ sq L) =
      ((coefficientEtaleExchangeChain B₀ sq L).map F).composite := by
  rw [coefficientEtaleExchange_factorization]
  exact ExchangeChain.mapHom_composite _ F

/-- The shared diagram predicate for the condensed coefficient ring of a finite discrete ring `T`.
The four vertices, three factors, and both original total exchange maps are retained.
(blueprint: def-weil-pbc-coefficient-exchange-diagram). -/
def coefficientExchangeSteps (B₀ : Type) [CommRing B₀]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [DiscreteTopology T] [Finite T] [Fact (IsNilpotent (ℓ : T))]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B₀ X ⥤
      residueExchangeDerived (Profinite.continuousMapRingObj T) X)
    (F1 : FiniteDiscreteEtalePlus B₀ Y' ⥤
      residueExchangeDerived (Profinite.continuousMapRingObj T) Y') : Prop :=
  ∀ (L : FiniteDiscreteEtalePlus B₀ X)
      (hL : ProEtale.boundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj T) X) (F0.obj L)),
    let N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj T) X) := ⟨F0.obj L, hL⟩
    let s := coefficientInternalExchangeChain (Profinite.continuousMapRingObj T) sq N.obj
    let t := (coefficientEtaleExchangeChain B₀ sq L).map F1
    Nonempty (ExchangeChain.FactoredComparison s t
      (coefficientAmbientBoundedExchange ℓ k T sq N)
      ((coefficientEtaleExchangeChain B₀ sq L).mapHom F1
        (coefficientEtaleExchange B₀ sq L)))

/-- Compatibility with the three specified exchange steps for realization functors. -/
def finiteDiscreteExchangeSteps [DiscreteTopology B] [Finite B] [Fact (IsNilpotent (ℓ : B))]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y')) :
    Prop :=
  coefficientExchangeSteps ℓ k B B sq F0 F1

/-- A step comparison identifies the two original specified total arrows.
Source: the factored comparison and the defining equations for the two typed arrows.
(blueprint: def-weil-pbc-coefficient-exchange-diagram).

Proof. Apply the generic factored-comparison arrow isomorphism. Rewrite both entire
arrow objects by the cache equations, retaining the original endpoints as well as
its morphisms. No component or derived functor is expanded in the consumer. -/
theorem finiteDiscreteExchangeSteps_arrowIso
    [DiscreteTopology B] [Finite B] [Fact (IsNilpotent (ℓ : B))]
    (sq : CommSq g' f' f g)
    (F0 : FiniteDiscreteEtalePlus B X ⥤ DerivedCategory (FiniteDiscreteInternalModules B X))
    (F1 : FiniteDiscreteEtalePlus B Y' ⥤ DerivedCategory (FiniteDiscreteInternalModules B Y'))
    (hsteps : finiteDiscreteExchangeSteps B ℓ k sq F0 F1)
    (L : FiniteDiscreteEtalePlus B X)
    (hL : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj B) X)
      (F0.obj L)) :
    Nonempty (Arrow.mk (((FiniteDiscreteRingObj.boundedConstructibleBaseChange
      ℓ B (sq.asOver (Spec (.of k)))).app
        ⟨F0.obj L, hL⟩).hom) ≅
      Arrow.mk (F1.map ((Etale.baseChange
        (ModuleCat.{u + 1} (ULift.{u + 1} B)) sq).app L))) := by
  obtain ⟨H⟩ := hsteps L hL
  have h := H.nonemptyArrowIso
  rw [coefficientAmbientBoundedExchange_arrow_eq,
    coefficientEtaleExchange_map_arrow_eq] at h
  exact h

end AlgebraicGeometry.ProEtale.CondensedRing
