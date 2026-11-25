/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
import all WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientProjectionComparison
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Proper formulas after the first residue reduction

This is the finite-coefficient step of the integral proper-base-change proof.
Completeness is neither assumed nor concluded here.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint

universe u u₁ u₂

open CategoryTheory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CategoryTheory.Limits
open AlgebraicGeometry.ProEtale.QuotientChange

set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  upperStar lowerStar derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp leftDerivedUpperStarTensor derivedTensor
  CategoryTheory.mateEquiv CategoryTheory.Adjunction.rightAdjointProjectionMap

section Helpers

attribute [local semireducible] L F adj IntegralQuotient.actualProjection
  IntegralQuotient.actualTensorPull

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

attribute [local instance] finiteProperCache1 finiteProperCache2 finiteProperCache3
  finiteProperCache4 finiteProperCache5 finiteProperCache6 finiteProperCache7
  finiteProperCache8 finiteProperCache9 finiteProperCache10 finiteProperCache11
  finiteProperCache12

attribute [local instance] sectionDerived modulesClosed modulesSymmetric modulesFlat

-- Compare canonical derived maps without expanding their resolving constructions.
private theorem quotient_formulas
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p]
    (hfin : Finite (Padic.coefficientExtensionRing l E 1))
    (htor : ∃ r : ℕ, (l ^ r : ℕ) • (1 : Padic.coefficientExtensionRing l E 1) = 0) :
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g)
      (K : DerivedCategory (Modules (IntegralQuotient.integral l E) X)),
      (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((D (IntegralQuotient.reduction l E 0) X).obj K) →
      IsIso ((D (IntegralQuotient.reduction l E 0) Y').map
        ((condensedAmbientExchange (IntegralQuotient.integral l E) sq).app K))) ∧
    (∀ (K : DerivedCategory (Modules (IntegralQuotient.integral l E) X))
      (M : DerivedCategory (Modules (IntegralQuotient.integral l E) Y)),
      (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((D (IntegralQuotient.reduction l E 0) X).obj K) →
      (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) Y ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((D (IntegralQuotient.reduction l E 0) Y).obj M) →
      IsIso ((D (IntegralQuotient.reduction l E 0) Y).map
        (moduleObjectProjectionMap (IntegralQuotient.integral l E) p K M))) := by
  classical
  let := hfin
  let := IntegralQuotient.quotientTopology l E 0
  have hf := finiteCoefficientProperFormulas (IntegralQuotient.finite l E 0)
    (Padic.coefficientExtensionRing l E 1) (Iso.refl _) l htor k p
  obtain ⟨_, _, _, b, hb, hi, _⟩ :=
    IntegralQuotient.integral_quotient_direct_image_comparison l E
  constructor
  · intro X' Y' g p' g' sq K hK
    let : ∀ T : Scheme.{u},
        HasDerivedCategory.{u + 1}
          (ModuleRingedComparison.modules (IntegralQuotient.integral l E) T) :=
      fun T ↦ inferInstance
    let : ∀ T : Scheme.{u},
        HasDerivedCategory.{u + 1}
          (ModuleRingedComparison.modules (IntegralQuotient.finite l E 0) T) :=
      fun T ↦ inferInstance
    have hex := IntegralQuotient.internal_rectangle (IntegralQuotient.reduction l E 0)
      (fun f ↦ b f 0) (fun f ↦ hb f 0) sq
    have hactual :
        (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) X ⊓
          _root_.DerivedCategory.finiteTorAmplitude _)
            ((D (IntegralQuotient.reduction l E 0) X).obj K) →
        IsIso ((condensedAmbientExchange (IntegralQuotient.finite l E 0) sq).app
          ((D (IntegralQuotient.reduction l E 0) X).obj K)) := by
      refine Eq.mp ?_ (hf.1 g p' g' sq
        ((D (IntegralQuotient.reduction l E 0) X).obj K))
      run_tac coefficientCongrGoal
    exact generic_condensed_exchange_iso (IntegralQuotient.integral l E)
      (IntegralQuotient.finite l E 0) (IntegralQuotient.reduction l E 0)
      (fun f ↦ b f 0) sq K hex (hi p 0) (hi p' 0) (hactual hK)
  · intro K M hK hM
    have hfinite :
        (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) X ⊓
          _root_.DerivedCategory.finiteTorAmplitude _)
            ((D (IntegralQuotient.reduction l E 0) X).obj K) →
        (constantModelBoundedConstructible (IntegralQuotient.finite l E 0) Y ⊓
          _root_.DerivedCategory.finiteTorAmplitude _)
            ((D (IntegralQuotient.reduction l E 0) Y).obj M) →
        IsIso (moduleObjectProjectionMap (IntegralQuotient.finite l E 0) p
          ((D (IntegralQuotient.reduction l E 0) X).obj K)
          ((D (IntegralQuotient.reduction l E 0) Y).obj M)) := by
      refine Eq.mp ?_ (hf.2
        ((D (IntegralQuotient.reduction l E 0) X).obj K)
        ((D (IntegralQuotient.reduction l E 0) Y).obj M))
      run_tac coefficientCongrGoal
    have hp : IsIso (((IntegralQuotient.actualProjection
        (IntegralQuotient.finite l E 0) p).app
          ((D (IntegralQuotient.reduction l E 0) X).obj K)).app
          ((D (IntegralQuotient.reduction l E 0) Y).obj M)) :=
      (congrArg IsIso (quotient_projection_eq (IntegralQuotient.finite l E 0) p
        ((D (IntegralQuotient.reduction l E 0) X).obj K)
        ((D (IntegralQuotient.reduction l E 0) Y).obj M))).mpr (hfinite hK hM)
    let := hp
    have := hi p 0
    have eq := IntegralQuotient.integral_quotient_projection_comparison
      l E p 0 (b p 0) (hb p 0) K M
    have hint := generic_projection_iso (IntegralQuotient.integral l E)
      (IntegralQuotient.finite l E 0) (IntegralQuotient.reduction l E 0) p (b p 0)
      (IntegralQuotient.scalarTensorIso l E 0 X) (IntegralQuotient.scalarTensorIso l E 0 Y)
      K M eq hp
    exact (congrArg IsIso (congrArg (D (IntegralQuotient.reduction l E 0) Y).map
      (quotient_projection_eq (IntegralQuotient.integral l E) p K M))).mp hint

private structure ReductionData where
  R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  S : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  commR : IsCommMonObj R.X
  commS : IsCommMonObj S.X
  a : R.X ⟶ S.X
  monHom : IsMonHom a

private def rawData (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (τ : TopologicalSpace (Padic.coefficientExtensionIntegers l E))
    (hτ : @IsTopologicalRing (Padic.coefficientExtensionIntegers l E) τ _)
    (σ : TopologicalSpace (Padic.coefficientExtensionRing l E 1))
    (hσ : @IsTopologicalRing (Padic.coefficientExtensionRing l E 1) σ _)
    (hc : @Continuous _ _ τ σ
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1))) : ReductionData.{u} := by
  letI := τ
  letI := σ
  letI := hτ
  letI := hσ
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionIntegers l E)) :=
    Sheaf.monObj_sheafCompose_obj _
      (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionIntegers l E))
  letI : MonObj (Profinite.continuousMapRingObjOfUniverse.{u, u}
      (Padic.coefficientExtensionRing l E 1)) :=
    Sheaf.monObj_sheafCompose_obj _
      (Profinite.continuousMapRingSheafOfUniverse (Padic.coefficientExtensionRing l E 1))
  let a := Profinite.continuousMapRingObjMapOfUniverse.{u, u}
    (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)) hc
  exact { R := Mon.mk (Profinite.continuousMapRingObjOfUniverse.{u, u}
              (Padic.coefficientExtensionIntegers l E))
          S := Mon.mk (Profinite.continuousMapRingObjOfUniverse.{u, u}
              (Padic.coefficientExtensionRing l E 1))
          commR := Profinite.isCommMonObj_continuousMapRingObjOfUniverse _
          commS := Profinite.isCommMonObj_continuousMapRingObjOfUniverse _
          a := a
          monHom := Profinite.isMonHom_continuousMapRingObjMapOfUniverse _ hc }

private def actualData (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ReductionData.{u} :=
  { R := Mon.mk (DerivedNakayama.integerRing l E)
    S := Mon.mk (DerivedNakayama.quotientRing l E 1)
    commR := inferInstance
    commS := AdicCompletion.quotientRing_isCommMonObj l E 1
    a := DerivedNakayama.reductionRing l E 1
    monHom := inferInstance }

private def quotientData (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] : ReductionData.{u} :=
  { R := Mon.mk (IntegralQuotient.integral l E)
    S := Mon.mk (IntegralQuotient.finite l E 0)
    commR := inferInstance
    commS := inferInstance
    a := IntegralQuotient.reduction l E 0
    monHom := inferInstance }

private theorem data_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    actualData l E = quotientData l E := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have htop := DerivedNakayama.coefficientTopology l E
  have hdis := DerivedNakayama.quotientDiscrete l E 1
  have ht := congrArg
    (TopologicalSpace.induced (fun x : Padic.coefficientExtensionIntegers l E ↦ (x : E)))
    htop
  change rawData l E _ _ _ _ _ = rawData l E _ _ _ _ _
  congr 1
  · exact ht.symm
  · exact hdis.eq_bot
private theorem residue_torsion (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    ∃ r : ℕ, (l ^ r : ℕ) • (1 : Padic.coefficientExtensionRing l E 1) = 0 := by
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have hgen : Ideal.span {Padic.coefficientExtensionUniformizer l E} =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hl : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    rw [← map_natCast (algebraMap (Padic l) E) l]
    change spectralNorm (Padic l) E ((algebraMap (Padic l) E) (l : Padic l)) < 1
    rw [spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E := (h.2.1 _).mpr hl
  refine ⟨1, ?_⟩
  simp only [pow_one, nsmul_eq_mul, mul_one]
  change Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E 1)
    (l : Padic.coefficientExtensionIntegers l E) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  simpa only [Padic.coefficientExtensionIdeal, pow_one, hgen] using hm

private def reducedFormulas (d : ReductionData.{u})
    {X Y : Scheme.{u}} (p : X ⟶ Y) : Prop := by
  letI := d.commR
  letI := d.commS
  letI := d.monHom
  let red := fun T : Scheme.{u} ↦
    (Mod.extendScalars (coefficientMap d.a T)).leftDerivedFunctor
  exact
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g)
      (K : DerivedCategory (QuotientChange.Modules d.R.X X)),
      (constantModelBoundedConstructible d.S.X X ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((red X).obj K) →
      IsIso ((red Y').map ((condensedAmbientExchange d.R.X sq).app K))) ∧
    (∀ (K : DerivedCategory (QuotientChange.Modules d.R.X X))
      (M : DerivedCategory (QuotientChange.Modules d.R.X Y)),
      (constantModelBoundedConstructible d.S.X X ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((red X).obj K) →
      (constantModelBoundedConstructible d.S.X Y ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
        ((red Y).obj M) →
      IsIso ((red Y).map (moduleObjectProjectionMap d.R.X p K M)))

end Helpers

/-- The first reduction of the canonical proper exchange and projection maps is
invertible when the input reductions have bounded constructible cohomology and finite
Tor amplitude. The original integral complexes need not be complete or bounded.
Source: blueprint latest, chap-Construction-of-f,
`sk-thm-sfb-proper-base-change/sk-thm-sfb-proper-base-change-integral.md`, paragraph (3),
the reduction-to-finite-coefficients step; Stacks Project, Tags 07A7, 0E47 and 0E48.
(blueprint: lem-sfb-integral-residue-proper-formulas).

Proof:
1. Put A = O_E/pi_E. The DVR and finite-quotient results make A a finite field killed
by l. Its quotient topology is discrete. The constant-function map identifies the
sheafified constant coefficient ring in finiteProperBaseChange with the continuous
condensed ring of A. This works in universe u by sheafifying ULift-valued constants;
on a profinite set, a continuous map to A is locally constant on its finite clopen
fibre partition. The constant map preserves one and products.
2. The proved coefficientTopology and quotientDiscrete lemmas identify the two
integer-ring topologies and identify the quotient topology with the discrete one.
Bundle both coefficient rings, their monoid structures and the actual quotient map.
The bundles are equal after those topology equalities; proof irrelevance identifies
the topological-ring, commutativity and continuity witnesses. Equality of the bundles
transports the full reduced assertion, including its canonical pullback, direct-image,
exchange and projection maps. No separate choice of a coefficient equivalence is needed.
3. Apply the finite proper-base-change theorem to the first reduction of K, using
its stated bounded constructible and finite-Tor properties. Apply the exchange
comparison rectangle from integral_quotient_exchange_comparison at exponent one.
The two scalar/geometric balancing comparisons and both scalar/direct-image mates
are isomorphisms. The finite exchange is invertible by the finite theorem. Cancel
the invertible outer comparisons in the rectangle. After the coefficient
identifications of step 2, the remaining arrow is precisely derivedReduction.map
of condensedAmbientExchange. This treats arbitrary base-changed schemes; only X
and Y have the standing hypotheses.
4. Apply the finite projection formula to the reductions of K and M. The scalar
tensor comparison identifies reduction of their integral tensor with the tensor of
their reductions. The projection comparison equation from
integral_quotient_projection_comparison identifies reduction of the actual
counit-defined projection map, conjugated by the scalar tensor, pullback and
scalar/direct-image comparisons, with this finite projection map. Every comparison
is invertible, so cancellation gives the second assertion. This uses the ordinary
uncompleted tensor. Empty schemes, zero complexes and noncomplete integral inputs
are included: every comparison used is defined on the ambient derived categories,
and all constructibility assumptions are on the finite reductions themselves. -/
theorem integralResidueProperFormulas
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    (∀ {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (p' : X' ⟶ Y') (g' : X' ⟶ X)
      (sq : ChosenCartesianSquare g' p' p g)
      (K : DerivedCategory (AdicCompletion.Modules l E X)),
      (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((AdicCompletion.derivedReduction l E X 0).obj K) →
      IsIso ((AdicCompletion.derivedReduction l E Y' 0).map
        ((condensedAmbientExchange (DerivedNakayama.integerRing l E) sq).app K))) ∧
    (∀ (K : DerivedCategory (AdicCompletion.Modules l E X))
      (M : DerivedCategory (AdicCompletion.Modules l E Y)),
      (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) X ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((AdicCompletion.derivedReduction l E X 0).obj K) →
      (constantModelBoundedConstructible (DerivedNakayama.quotientRing l E 1) Y ⊓
        _root_.DerivedCategory.finiteTorAmplitude _)
          ((AdicCompletion.derivedReduction l E Y 0).obj M) →
      IsIso ((AdicCompletion.derivedReduction l E Y 0).map
        (moduleObjectProjectionMap (DerivedNakayama.integerRing l E) p K M))) := by
  have hq := quotient_formulas l E k p
    (Padic.finite_coefficientExtensionRing l E 1 le_rfl) (residue_torsion l E)
  have h : reducedFormulas (quotientData l E) p := by
    refine Eq.mp ?_ hq
    conv_rhs => unfold reducedFormulas
    conv_lhs => unfold D
    run_tac coefficientCongrGoal
  have hactual : reducedFormulas (actualData l E) p := by
    rw [data_eq l E]
    exact h
  refine Eq.mp ?_ hactual
  conv_lhs => unfold reducedFormulas
  run_tac coefficientCongrGoal

end AlgebraicGeometry.ProEtale.CondensedRing
