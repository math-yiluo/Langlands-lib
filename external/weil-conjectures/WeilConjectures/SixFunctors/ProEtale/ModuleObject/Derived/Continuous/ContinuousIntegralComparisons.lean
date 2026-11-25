/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.OverSquare

public import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
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
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.ConstructibleSheaf.FreeLifting
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UnitBallRingObj.FiniteDiscreteCoefficient

/-! # Canonical comparisons for integral coefficient localization
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

section General

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

/-- Exact integral localization restricted to bounded constructible objects.
Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14.
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralScalarConstructible (X : Scheme.{u}) :
    integralConstructible ℓ E X ⥤
      ProEtale.BoundedConstructible (condensedRingObj (Profinite.continuousMapRingObj E) X) :=
  { obj := fun K ↦ ⟨(integralScalarExtension ℓ E X).obj K.obj,
      ProEtale.boundedConstructible_leftDerivedExtendScalars_obj _ _
        (coefficientMap (integralScalarMap ℓ E) X) K.obj K.property⟩
    map := fun h ↦ ObjectProperty.homMk ((integralScalarExtension ℓ E X).map h.hom)
    map_id := fun K ↦ by
      apply ObjectProperty.hom_ext
      exact (integralScalarExtension ℓ E X).map_id K.obj
    map_comp := fun f g ↦ by
      apply ObjectProperty.hom_ext
      exact (integralScalarExtension ℓ E X).map_comp f.hom g.hom }

/-- The integral coefficients `continuousIntegers ℓ E` are the closed unit ball of `E`, the
hypothesis of the unit-ball coefficient operations `UnitBallRingObj`. -/
instance fact_mem_continuousIntegers_iff :
    Fact (∀ x : E, x ∈ continuousIntegers ℓ E ↔ ‖x‖ ≤ 1) :=
  ⟨fun _ ↦ NNReal.coe_le_coe.symm⟩

variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The canonical pullback comparison restricted to bounded constructible objects, in the
orientation `T_T l_{h,O} ≅ l_{h,E} T_U`. Source: ChangeOfCoefficients.lean, `derivedPullIso`;
Bhatt--Scholze, Remark 6.8.15
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralConstructiblePullIso (K : integralConstructible ℓ E U) :
    (integralScalarConstructible ℓ E T).obj
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (h.asOver (Spec (.of k)))).obj K) ≅
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E)
        ℓ (h.asOver (Spec (.of k)))).obj
        ((integralScalarConstructible ℓ E U).obj K) :=
  ObjectProperty.isoMk _
    ((derivedPullIso (integralScalarMap ℓ E) h).app K.obj)

/-- Forward component of the canonical pull comparison, kept as a named morphism.
Source: Bhatt--Scholze, Remark 6.8.15; derivedPullIso.
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralConstructiblePullHom (K : integralConstructible ℓ E U) :=
  (integralConstructiblePullIso ℓ E k h K).hom

end Edge

end General

section FiniteIntermediateField

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]

section Edge

variable {T U : Scheme.{u}} [T.Over (Spec (.of k))] [U.Over (Spec (.of k))]
  [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
  [IsSeparated (T ↘ Spec (.of k))]
  [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
  [IsSeparated (U ↘ Spec (.of k))] (h : T ⟶ U) [h.IsOver (Spec (.of k))]

/-- The specified pushforward comparison restricted to bounded constructible objects.
Source: ChangeOfCoefficients.lean, `derivedPushHom`, the mate of restriction/pushforward;
Bhatt--Scholze, Remark 6.8.15
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralConstructiblePushHom
    (K : integralConstructible ℓ E T) :
    (integralScalarConstructible ℓ E U).obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (h.asOver (Spec (.of k)))).obj K) ⟶
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
        (h.asOver (Spec (.of k)))).obj
        ((integralScalarConstructible ℓ E T).obj K) :=
  ObjectProperty.homMk
    ((derivedPushHom (integralScalarMap ℓ E) h).app K.obj)

end Edge

section Square

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

/-- The specified source comparison `S_K`: first the pull comparison for `g`, then the
pullback of the push comparison for `f`. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralConstructibleSourceHom (K : integralConstructible ℓ E X) :
    (integralScalarConstructible ℓ E Y').obj
        ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g.asOver (Spec (.of k)))).obj
          ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
            (f.asOver (Spec (.of k)))).obj K)) ⟶
      (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E)
        ℓ (g.asOver (Spec (.of k)))).obj
        ((ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
          (f.asOver (Spec (.of k)))).obj
          ((integralScalarConstructible ℓ E X).obj K)) :=
  integralConstructiblePullHom ℓ E k g
      ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
        (f.asOver (Spec (.of k)))).obj K) ≫
    (boundedConstructibleUpperStar (Profinite.continuousMapRingObj E)
      ℓ (g.asOver (Spec (.of k)))).map
      (integralConstructiblePushHom ℓ E k f K)

/-- The specified target comparison `U_K`: first the push comparison for `f'`, then the
pushforward of the pull comparison for `g'`. Source: Bhatt--Scholze, Remark 6.8.15
(blueprint: def-weil-pbc-continuous-integral-comparisons). -/
noncomputable def integralConstructibleTargetHom (K : integralConstructible ℓ E X) :
    (integralScalarConstructible ℓ E Y').obj
        ((UnitBallRingObj.boundedConstructibleLowerStar ℓ (continuousIntegers ℓ E)
          (f'.asOver (Spec (.of k)))).obj
          ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj
            K)) ⟶
      (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
        (f'.asOver (Spec (.of k)))).obj
        ((boundedConstructibleUpperStar (Profinite.continuousMapRingObj E)
          ℓ (g'.asOver (Spec (.of k)))).obj
          ((integralScalarConstructible ℓ E X).obj K)) :=
  integralConstructiblePushHom ℓ E k f'
      ((boundedConstructibleUpperStar (integralCoeff ℓ E) ℓ (g'.asOver (Spec (.of k)))).obj K) ≫
    (ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E
      (f'.asOver (Spec (.of k)))).map
      (integralConstructiblePullHom ℓ E k g' K)

end Square

end FiniteIntermediateField

end AlgebraicGeometry.ProEtale.CondensedRing
