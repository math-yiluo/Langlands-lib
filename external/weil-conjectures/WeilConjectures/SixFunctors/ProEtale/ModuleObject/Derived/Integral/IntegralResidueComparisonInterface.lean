/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

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
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.IntegralResidueComparisonInterface

/-! # Interface for coherent integral residue comparisons

Source: Bhatt--Scholze, Lemma 6.5.9(3), and associativity of derived coefficient change.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface)
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

local instance instEssentiallySmallProfinite_integralIntegralResidueComparisonInterface
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]



/-- Derived direct image with its domain and codomain exposed explicitly. -/
@[irreducible] noncomputable def residueExchangeLowerStar
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeDerived Λ X ⥤ residueExchangeDerived Λ Y :=
  R((f)_*⟦Λ⟧)

/-- The actual derived adjunction, expressed through the typed functor interface. -/
@[irreducible] noncomputable def residueExchangeAdjunction
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeUpperStar Λ f ⊣ residueExchangeLowerStar Λ f :=
  by
    unfold residueExchangeUpperStar residueExchangeLowerStar
    exact derivedUpperStarLowerStarAdjunction Λ f




namespace IntegralResiduePullComparisons

variable {ℓ E} (c : IntegralResiduePullComparisons.{u} ℓ E)

/-- The direct-image comparison is the adjunction mate of the inverse pull comparison.
This is an actual construction; no direct-image isomorphism is chosen.
Source: Bhatt--Scholze, Lemma 6.5.9(3), projection comparison by adjunction.
(blueprint: def-weil-pbc-residue-exchange-comparison-interface). -/
noncomputable def push {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar (integralCoeff ℓ E) f ⋙ residueExchangeReduction ℓ E Y ⟶
      residueExchangeReduction ℓ E X ⋙
        residueExchangeLowerStar
          (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f :=
  (mateEquiv (residueExchangeAdjunction (integralCoeff ℓ E) f)
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
      (TwoSquare.mk _ _ _ _ (c.pull f).inv))

/-- The defining counit equation for the actual direct-image comparison.
Source: Mathlib, mateEquiv_counit.
(blueprint: lem-weil-pbc-integral-residue-push-counit)
Proof. Apply the counit identity of the mates equivalence to the inverse pull comparison.
-/
theorem push_counit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    (residueExchangeUpperStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).map
        ((c.push f).app K) ≫
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f).counit.app
        ((residueExchangeReduction ℓ E X).obj K) =
    (c.pull f).inv.app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≫
      (residueExchangeReduction ℓ E X).map
        ((residueExchangeAdjunction (integralCoeff ℓ E) f).counit.app K) := by
  exact mateEquiv_counit (residueExchangeAdjunction (integralCoeff ℓ E) f)
    (residueExchangeAdjunction
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)
    (TwoSquare.mk _ _ _ _ (c.pull f).inv) K

end IntegralResiduePullComparisons

/-- The actual derived extension/restriction adjunction, with typed reduction. -/
@[irreducible] noncomputable def residueExchangeReductionAdjunction (T : Scheme.{u}) :
    residueExchangeReduction ℓ E T ⊣
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory := by
  unfold residueExchangeReduction integralReduction
  exact Mod.derivedExtendMapDerivedCategoryAdjunction _

namespace IntegralResiduePullComparisons

variable {ℓ E}

/-- Conjugating the pull comparison between composite left adjoints compares the
composite right adjoints. No exactness of extension of scalars is used. -/
@[irreducible] noncomputable def restrictPushIso (c : IntegralResiduePullComparisons.{u} ℓ E)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    residueExchangeLowerStar
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f ⋙
        (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory ⋙
        residueExchangeLowerStar (integralCoeff ℓ E) f :=
  ((residueExchangeReductionAdjunction ℓ E Y).comp
      (residueExchangeAdjunction
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f)).rightAdjointUniq
    (((residueExchangeAdjunction (integralCoeff ℓ E) f).comp
      (residueExchangeReductionAdjunction ℓ E X)).ofNatIsoLeft (c.pull f))

end IntegralResiduePullComparisons

/-- The restricted residue coefficient, viewed in degree zero. -/
noncomputable abbrev residueExchangeCoefficient (T : Scheme.{u}) :
    residueExchangeDerived (integralCoeff ℓ E) T :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
      (Mod.regular (condensedRingObj
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))

end AlgebraicGeometry.ProEtale.CondensedRing
