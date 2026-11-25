/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.CondensedERealization.CondensedERealizationDefinitions

/-! # Integral operations and left realization comparisons

Source: Bhatt--Scholze, Proposition 6.8.14(2), Remark 6.8.15.
(blueprint: def-weil-pbc-condensed-e-left-system)

The records omit the rational adjunction and the right realization comparison.
Those are constructed by tensor extension and taking mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj TensorProduct
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
namespace WeilConjectures.CondensedERealization

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [NormedField E] [NormedAlgebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]
variable (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- Integral restrictions with their ambient adjunction normalization and a left comparison.
Source: BS 6.8.14(2), 6.8.15 (blueprint: def-weil-pbc-condensed-e-left-system). -/
structure LeftAlong (T U : Base k) (h : T.scheme ⟶ U.scheme)
    [h.IsOver (Spec (.of k))] (rT : At l E T.scheme) (rU : At l E U.scheme) where
  pull : Integral l E U.scheme ⥤ Integral l E T.scheme
  [pullAdditive : pull.Additive]
  [pullLinear : pull.Linear (PbcIntegralRing l E)]
  push : Integral l E T.scheme ⥤ Integral l E U.scheme
  [pushAdditive : push.Additive]
  [pushLinear : push.Linear (PbcIntegralRing l E)]
  pullAmbient : pull ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).completedPull h
  pushAmbient : push ⋙ ObjectProperty.ι (PbcIsBoundedConstructibleComplete U.scheme
    (pbcIntegralDatum l E)) ≅
    ObjectProperty.ι (PbcIsBoundedConstructibleComplete T.scheme (pbcIntegralDatum l E)) ⋙
      (pbcIntegralDatum l E).push h
  integralAdjunction : pull ⊣ push
  integral_unit : ∀ K : Integral l E U.scheme,
    (integralAdjunction.unit.app K).hom ≫ pushAmbient.hom.app (pull.obj K) ≫
        ((pbcIntegralDatum l E).push h).map (pullAmbient.hom.app K) =
      (proEtaleRingDerivedAdjunction h _ _ ((pbcIntegralDatum l E).integralRingIso h)).unit.app
          K.obj ≫
        ((pbcIntegralDatum l E).push h).map
          ((pbcIntegralDatum l E).ordinaryToCompleted h K.obj)
  integral_counit : ∀ K : Integral l E T.scheme,
    (pbcIntegralDatum l E).ordinaryToCompleted h (push.obj K).obj ≫
        pullAmbient.inv.app (push.obj K) ≫ (integralAdjunction.counit.app K).hom =
      ((pbcIntegralDatum l E).pull h).map (pushAmbient.hom.app K) ≫
        (proEtaleRingDerivedAdjunction h _ _
          ((pbcIntegralDatum l E).integralRingIso h)).counit.app K.obj
  pullComparison :
    ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) pull ⋙
        rT.realization.functor ≅
      rU.realization.functor ⋙
        boundedConstructibleUpperStar (Profinite.continuousCoefficientRingObj E) l
          (X := T.model) (Y := U.model)
      (Base.map T U h)

attribute [instance] LeftAlong.pullAdditive LeftAlong.pullLinear
  LeftAlong.pushAdditive LeftAlong.pushLinear

/-- Tensor extension of the integral inverse image.
Source: BS 6.8.15 (blueprint: def-weil-pbc-condensed-e-left-system). -/
abbrev LeftAlong.rationalPull {T U : Base k} {h : T.scheme ⟶ U.scheme}
    [h.IsOver (Spec (.of k))] {rT : At l E T.scheme} {rU : At l E U.scheme}
    (a : LeftAlong l E k T U h rT rU) :=
  ScalarLocalization.transport (PbcIntegralRing l E) (pbcUniformizer l E) a.pull

end WeilConjectures.CondensedERealization
