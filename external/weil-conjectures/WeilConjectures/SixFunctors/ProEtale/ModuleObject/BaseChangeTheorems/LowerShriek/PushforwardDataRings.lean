/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.PushforwardData
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.MorphismDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.OpenImmersionBaseChange
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Integral

/-!
# The pushforward data of the `ℓ`-adic coefficient rings

The pushforwards `Rf_*` and adjunctions `Lf^* ⊣ Rf_*` on the bounded constructible derived
categories of the `ℓ`-adic coefficient rings `ℚ̲̄_ℓ`, `E̲` and `𝒪̲_E` form pushforward data
(`ProEtale.CondensedRing.BoundedConstructiblePushforwardData`):
`ProEtale.CondensedRing.padicAlgClPushforwardData`,
`ProEtale.CondensedRing.continuousMapPushforwardData` and
`ProEtale.CondensedRing.padicIntegersPushforwardData`. This file shows that the compact-support
base change morphisms `Ex_!` of the three coefficient rings are the ones defined from these
pushforward data.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

/-! ### The coefficient ring `ℚ̲̄_ℓ` -/

/-- The pushforward datum of the coefficient ring `ℚ̲̄_ℓ`. -/
noncomputable def padicAlgClPushforwardData :
    BoundedConstructiblePushforwardData (Profinite.padicAlgClRingObj ℓ) ℓ k where
  lowerStar f := boundedConstructibleLowerStar ℓ f
  adj f := boundedConstructibleUpperStarLowerStarAdjunction ℓ f

lemma isIsoRefinementPushforward_padicAlgClPushforwardData :
    (padicAlgClPushforwardData ℓ k).IsIsoRefinementPushforward :=
  fun sq ↦ isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicAlgCl ℓ sq

/-! ### The coefficient ring `E̲` -/

/-- The pushforward datum of the coefficient ring `E̲`. -/
noncomputable def continuousMapPushforwardData (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    BoundedConstructiblePushforwardData (Profinite.continuousMapRingObj E) ℓ k where
  lowerStar f := ContinuousMapRingObj.boundedConstructibleLowerStar ℓ E f
  adj f := ContinuousMapRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f

lemma isIsoRefinementPushforward_continuousMapPushforwardData
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (continuousMapPushforwardData ℓ k E).IsIsoRefinementPushforward :=
  fun sq ↦ isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward ℓ E sq

/-! ### The coefficient ring `𝒪̲_E` -/

/-- The pushforward datum of the coefficient ring `𝒪̲_E`. -/
noncomputable def padicIntegersPushforwardData (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)]
    [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] :
    BoundedConstructiblePushforwardData (Profinite.padicIntegersRingObj.{u} ℓ E) ℓ k where
  lowerStar f := PadicIntegersRingObj.boundedConstructibleLowerStar ℓ E f
  adj f := PadicIntegersRingObj.boundedConstructibleUpperStarLowerStarAdjunction ℓ E f

lemma isIsoRefinementPushforward_padicIntegersPushforwardData (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] :
    (padicIntegersPushforwardData ℓ k E).IsIsoRefinementPushforward :=
  fun sq ↦ isIso_boundedConstructibleOpenImmersionLowerShriekRefinementPushforward_padicIntegers
    ℓ E sq

/-! ### The compact-support base change morphisms -/

variable {ℓ k} {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

lemma padicAlgClPushforwardData_lowerShriekOfCompactification (f : X ⟶ Y) :
    (padicAlgClPushforwardData ℓ k).lowerShriekOfCompactification (compactificationOverField f) =
      boundedConstructibleLowerShriek ℓ f :=
  rfl

lemma continuousMapPushforwardData_lowerShriekOfCompactification
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (f : X ⟶ Y) :
    (continuousMapPushforwardData ℓ k E).lowerShriekOfCompactification
        (compactificationOverField f) =
      ContinuousMapRingObj.boundedConstructibleLowerShriek ℓ E f :=
  rfl

lemma padicIntegersPushforwardData_lowerShriekOfCompactification (E : Type) [Field E]
    [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E] [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)]
    [FiniteDimensional ℚ_[ℓ] E] (f : X ⟶ Y) :
    (padicIntegersPushforwardData ℓ k E).lowerShriekOfCompactification
        (compactificationOverField f) =
      PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E f :=
  rfl

/-- The compact-support base change morphism of `ℚ̲̄_ℓ` is the one of its pushforward datum. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_eq_pushforwardData
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq =
      BoundedConstructiblePushforwardData.lowerShriekBaseChange
        (isIsoRefinementPushforward_padicAlgClPushforwardData ℓ k) sq := by
  rw [boundedConstructibleLowerShriekBaseChange_padicAlgCl_def]
  unfold boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
  simp only [boundedConstructibleBaseChange_def]
  rfl

/-- The compact-support base change morphism of `E̲` is the one of its pushforward datum. -/
lemma boundedConstructibleLowerShriekBaseChange_eq_pushforwardData
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange ℓ E sq =
      BoundedConstructiblePushforwardData.lowerShriekBaseChange
        (isIsoRefinementPushforward_continuousMapPushforwardData ℓ k E) sq := by
  unfold boundedConstructibleLowerShriekBaseChange
  unfold ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationBaseChangePasting
  simp only [ContinuousMapRingObj.boundedConstructibleBaseChange_def]
  rfl

/-- The compact-support base change morphism of `𝒪̲_E` is the one of its pushforward datum. -/
lemma boundedConstructibleLowerShriekBaseChange_padicIntegers_eq_pushforwardData
    (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
    [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E]
    (sq : IsPullback g' f' f g) :
    boundedConstructibleLowerShriekBaseChange_padicIntegers ℓ E sq =
      BoundedConstructiblePushforwardData.lowerShriekBaseChange
        (isIsoRefinementPushforward_padicIntegersPushforwardData ℓ k E) sq := by
  unfold boundedConstructibleLowerShriekBaseChange_padicIntegers
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
