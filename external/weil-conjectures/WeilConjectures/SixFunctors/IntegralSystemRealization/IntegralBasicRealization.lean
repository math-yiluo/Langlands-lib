/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralBasicRealizationData
import WeilConjectures.SixFunctors.IntegralSystemRealization.Reduction.IntegralReductionPullbackModel
import WeilConjectures.SixFunctors.IntegralSystemRealization.Proper.IntegralProperTowerTransition
import WeilConjectures.SixFunctors.IntegralSystemRealization.Open.IntegralOpenMateNormalization
import WeilConjectures.SixFunctors.IntegralSystemRealization.Support.IntegralSupportTowerNormalization
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Data.Nat.Prime.Infinite
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import all WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos

/-! # Assembly of primitive integral realization comparisons -/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField
  WeilConjectures.integralDerivedPullback WeilConjectures.integralCompletedTensor
  WeilConjectures.pullbackTensorCalculus
  WeilConjectures.coefficientSequenceCommRingSheaf
  WeilConjectures.coefficientSequenceCommRingPresheaf
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem primeUnit (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p) :
    IsUnit (l : D.k) := by
  let : Fintype D.k₀ := Fintype.ofFinite D.k₀
  let : Fact D.p.Prime := ⟨D.prime⟩
  have hc : Fintype.card D.k₀ = D.p ^ D.a := by
    simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq
  let : CharP D.k₀ D.p := charP_of_card_eq_prime_pow hc
  have hu : IsUnit (l : D.k₀) := (CharP.isUnit_natCast_iff D.prime).2 (by
    intro hdiv
    exact hl ((Nat.prime_dvd_prime_iff_eq D.prime (Fact.out : l.Prime)).1 hdiv).symm)
  simpa only [map_natCast] using hu.map (algebraMap D.k₀ D.k)

private def restrictedUnitIso (W : Scheme.{u}) (P : ObjectProperty (Integral l E W))
    (h : ∀ K : P.FullSubcategory,
      IsIso ((calculus l E W).adjunction.unit.app K.obj)) :
    P.ι ≅ P.ι ⋙ (calculus l E W).reduction ⋙ coefficientSequenceLimit l E W := by
  let η := Functor.whiskerLeft P.ι (calculus l E W).adjunction.unit
  haveI : ∀ K, IsIso (η.app K) := h
  exact NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun f ↦ η.naturality f)

private def properComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : ∀ K : (basicUnaryDomain l E X Y (Operations.push l E o p)).FullSubcategory,
      IsIso ((calculus l E X).adjunction.unit.app K.obj)) :
    basicUnarySource l E X Y (Operations.push l E o p) ≅
      basicUnaryTarget l E X Y (Operations.push l E o p) (ringedPush l E p) :=
  Functor.isoWhiskerLeft
      ((basicUnaryDomain l E X Y (Operations.push l E o p)).ι ⋙ (calculus l E X).reduction)
      (m.push l E p) ≪≫
    Functor.isoWhiskerRight
      (restrictedUnitIso l E X (basicUnaryDomain l E X Y (Operations.push l E o p)) h).symm
      (ringedPush l E p)

private def openComparison (o : Operations l E) (m : RealizationModel l E o)
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (hu : ∀ K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory,
      IsIso ((calculus l E Y).adjunction.unit.app ((ringedOpen l E j).obj K.obj)))
    (hr : ∀ K : (basicUnaryDomain l E X Y (Operations.shriek l E o j)).FullSubcategory,
      IsIso ((m.openReduction l E j).app K.obj)) :
    basicUnarySource l E X Y (Operations.shriek l E o j) ≅
      basicUnaryTarget l E X Y (Operations.shriek l E o j) (ringedOpen l E j) := by
  let P := basicUnaryDomain l E X Y (Operations.shriek l E o j)
  let r := Functor.whiskerLeft P.ι (m.openReduction l E j)
  haveI : ∀ K, IsIso (r.app K) := hr
  let η := Functor.whiskerLeft (P.ι ⋙ ringedOpen l E j) (calculus l E Y).adjunction.unit
  haveI : ∀ K, IsIso (η.app K) := hu
  exact Functor.isoWhiskerRight
    (NatIso.ofComponents (fun K ↦ asIso (r.app K)) (fun f ↦ r.naturality f))
    (coefficientSequenceLimit l E Y) ≪≫
      (NatIso.ofComponents (fun K ↦ asIso (η.app K)) (fun f ↦ η.naturality f)).symm

end WeilConjectures.IntegralSystemRealization
