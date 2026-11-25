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
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteDiscreteRingObj.FiniteDiscreteCoefficientBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralComparisons

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralReductionConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralResidueExchangeAlgebra
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedExchangeAmbient

/-! # Reduction of integral exchange to residue-coefficient exchange

Source: Bhatt--Scholze, Lemma 6.5.9(3) and Proposition 6.8.11(3)
(blueprint: lem-weil-pbc-integral-residue-exchange).
-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

-- Fix the size bound explicitly to avoid a recursive instance search on this site.
local instance instEssentiallySmallProfinite_integralResidueExchange
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeReduction

/-- Invertible push comparisons identify the ambient integral and residue exchange arrows. -/
private theorem integralResidue_exchange_arrow_iso
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (c : IntegralResiduePullComparisons.{u} ℓ E) (sq : CommSq g' f' f g)
    [IsIso (c.push f)] [IsIso (c.push f')]
    (K : residueExchangeDerived (integralCoeff ℓ E) X) :
    Nonempty (Arrow.mk ((residueExchangeReduction ℓ E Y').map
        ((residueExchangeBaseChange (integralCoeff ℓ E) sq).app K)) ≅
      Arrow.mk ((residueExchangeBaseChange
        (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) sq).app
        ((residueExchangeReduction ℓ E X).obj K))) := by
  let S := (c.pull g).app ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K) ≪≫
    (residueExchangeUpperStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) g).mapIso
      (asIso ((c.push f).app K))
  let T := asIso ((c.push f').app
      ((residueExchangeUpperStar (integralCoeff ℓ E) g').obj K)) ≪≫
    (residueExchangeLowerStar
      (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) f').mapIso
      ((c.pull g').app K)
  refine ⟨Arrow.isoMk S T ?_⟩
  simpa only [S, T, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom,
    Arrow.mk_hom, Category.assoc] using integralResidue_exchange_square ℓ E c sq K

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

/-- The residue ring `O_E/ℓ` is killed by `ℓ`, the hypothesis of the finite discrete
coefficient operations `FiniteDiscreteRingObj`. -/
instance fact_isNilpotent_natCast_integralResidue :
    Fact (IsNilpotent (ℓ : integralResidue ℓ E)) :=
  ⟨⟨1, by
    rw [pow_one]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))⟩⟩

/-- Derived coefficient reduction compares integral exchange to residue exchange.
Source: Bhatt--Scholze, Lemma 6.5.9(3) and Proposition 6.8.11(3), using the
two-term finite free resolution of O_E/ℓ over O_E
(blueprint: lem-weil-pbc-integral-residue-exchange).

Proof in words. Multiplication by ℓ is injective on O_E and its cokernel is A = O_E/ℓ.
The proved integral module reduction sequence, pulled back by the exact monoidal
inverse image from the profinite point, is the two-term finite free resolution of A_X.
Consequently derived reduction has cohomology only one degree below the bounds of M.
On each constructible stratum, finite presentations over the discrete valuation ring
show that its cohomology is finite over A, so reduction is bounded constructible; let N
be that same reduced object, equipped with this property. Tensor associativity gives
its canonical pullback comparison. The supplied hTensor identifies reduction after
restriction as a left derived functor of tensor by the residue module. The supplied
hPerfect and the projection formula for dualizable objects make the direct-image comparison
invertible: equivalently, direct image preserves the finite distinguished triangle for
multiplication by ℓ. These comparisons are adjunction mates of the underived scalar
comparisons. Their unit and counit equations, and compatibility of pullback composition,
identify the reduction of the unit-square-counit formula with the residue formula.
The resulting commuting square has invertible endpoint maps, hence is an arrow
isomorphism. This step uses neither etale origin nor proper base change. -/
theorem integralResidueExchange_comparison
    (sq : CommSq g' f' f g)
    (M : integralConstructible ℓ E X)
    (hPerfect : ∀ T : Scheme.{u},
      IsDualizable ((DerivedCategory.singleFunctor _ 0).obj
        ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
          (Mod.regular (condensedRingObj
            (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))))
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ N : ProEtale.BoundedConstructible
        (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X),
      Nonempty (N.obj ≅ (integralReduction ℓ E X).obj M.obj) ∧
      Nonempty (Arrow.mk ((integralReduction ℓ E Y').map
          ((UnitBallRingObj.boundedConstructibleBaseChange ℓ (continuousIntegers ℓ E)
            (sq.asOver (Spec (.of k)))).app M).hom) ≅
        Arrow.mk ((FiniteDiscreteRingObj.boundedConstructibleBaseChange ℓ
          (integralResidue ℓ E) (sq.asOver (Spec (.of k)))).app N).hom) := by
  obtain ⟨c, hc⟩ := integralResidue_comparisons ℓ E hPerfect hTensor
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X :=
    QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : IsNoetherian X := {}
  let N : ProEtale.BoundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) X) :=
    ⟨(integralReduction ℓ E X).obj M.obj,
      integralReduction_boundedConstructible ℓ E X M⟩
  refine ⟨N, ⟨Iso.refl _⟩, ?_⟩
  have : IsIso (c.push f) := hc f
  have : IsIso (c.push f') := hc f'
  rw [FiniteDiscreteRingObj.boundedConstructibleBaseChange_hom_eq_ambient ℓ k _ sq N,
    UnitBallRingObj.boundedConstructibleBaseChange_hom_eq_ambient ℓ k _ sq M]
  exact integralResidue_exchange_arrow_iso ℓ E c sq M.obj

end AlgebraicGeometry.ProEtale.CondensedRing
