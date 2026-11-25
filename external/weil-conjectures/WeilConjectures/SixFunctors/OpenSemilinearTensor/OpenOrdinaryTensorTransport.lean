/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenSemilinearTensorModelData
import WeilConjectures.SixFunctors.OpenSemilinearTensor.OpenRingedCoefficientTensorTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CoverLifting
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-! # Transport of the generator-normalized ordinary open tensor formula

Source: Stacks Project, Tags 03DI, 03EK and 0E8I.
(blueprint: lem-sf-open-ordinary-tensor-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenSemilinearTensor
open WeilConjectures.SemilinearSections SheafOfModules SheafOfModules.ScalarHomOrdinary
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

private theorem sliceCocontinuous {T : Scheme.{t}} (W : T.ProEt) :
    (cbcSliceFunctor T W).IsCocontinuous ((ProEt.topology T).over W)
      (ProEt.topology W.left) :=
  ((ProEt.sliceEquiv T W).toAdjunction.isCocontinuous_iff_coverPreserving
    ((ProEt.topology T).over W) (ProEt.topology W.left)).mpr (ProEt.sliceFrom_cover T W)

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{t}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The completed-coefficient tensor formula for supplied open transports.
Source: Stacks 03DI, 03EK and 0E8I
(blueprint: lem-sf-open-ordinary-tensor-transport).

Proof: the concrete slice equivalence is cocontinuous. Apply the normalized
ringed coefficient tensor transport with the actual completed ring sheaves,
completedMap, integral equivalence and its recorded forward-functor equality.
Its native tensor is the recorded ordinary tensor. Its original summand is the
specified extensionSection, and its restricted section is the integral counit
in restrictedSection. The two resulting equations are OrdinaryNaturality and
OrdinaryGenerators. -/
theorem openOrdinaryTensorTransport (o : Operations l E j) (hmap : IsIso o.completedMap) :
    ∃ μ : OrdinaryTensorComparison l E j o,
      OrdinaryNaturality l E j o μ ∧ OrdinaryGenerators l E j o μ := by
  obtain ⟨μ, hn, hg⟩ := ringedCoefficientTensorTransport.{t + 1, t, max u (t + 1)}
    (J := ProEt.topology X) (K := ProEt.topology U)
    (F := IntegralOpenReduction.sliceSite j)
    (hF := IntegralOpenReduction.sliceContinuous j)
    (hFc := sliceCocontinuous (IntegralOpenReduction.openObject j)) (ha := hmap)
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
    (completedIntegralCommRingSheafUnrestricted l E U) o.completedMap o.integral
    (eqToIso o.integralFunctor)
  refine ⟨μ, ?_, ?_⟩
  · intro M M' N N' f g
    convert hn f g using 1 <;> rfl
  · intro M N V b x y
    convert hg M N V b x y using 1 <;> rfl

end WeilConjectures.OpenSemilinearTensor
