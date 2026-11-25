/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.Etale.Derived.LisseFieldDual
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleOrigin
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.ProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ResidueFieldTransport

/-!
# Stability of module complexes of étale origin

Let `T` be a finite discrete commutative ring, `Λ = C(-, T)` and
`Φ = ProEtale.finiteCoefficientDerivedEquivalence` the comparison of `D(Mod_{Λ_X})` with the
derived category of pro-étale sheaves of `T`-modules. Call `C ∈ D(Mod_{Λ_X})` *bounded below of
étale origin* if `Φ C` is (`ProEtale.DerivedCategory.plusEtaleOrigin`). This file shows that this
class is stable under the operations entering the Künneth formula for nearby cycles.

* **Tensor products**, when `T` is a field
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj`): if `Φ C ≅ ν^* Q`
  and `Φ D ≅ ν^* Q'` with `Q`, `Q'` bounded below, then
  `Φ (C ⊗ D) ≅ Φ C ⊗ᴸ Φ D ≅ ν^* (Q ⊗ᴸ Q')` (`Φ` and `ν^*` are monoidal), and `Q ⊗ᴸ Q'` is bounded
  below since over a field every étale sheaf is flat, so that `Q` has Tor amplitude bounded below
  (`DerivedCategory.torAmplitudeGE_of_isGE_of_forall_flat`).
* **External products** `Lf₁^* A ⊗ Lf₂^* B`, when `T` is a field
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar`).
* **Bounded constructible complexes** are of étale origin
  (`ProEtale.plusEtaleOrigin_finiteCoefficientDerivedEquivalence_of_boundedConstructible`), in
  particular with coefficients `𝔽_E`
  (`ProEtale.CondensedRing.plusEtaleOrigin_of_boundedConstructible_residueField`).
-/

@[expose] public section

universe w v u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace DerivedCategory

variable {C : Type u'} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{w} C] [Abelian.HasFunctorialFlatResolution C]

/-- If every object of `C` is flat, an object of `D(C)` vanishing in degrees `< b` has Tor
amplitude in `[b, ∞)`: for every object `F`, `F[0]` has Tor amplitude in `[0, 0]`. -/
lemma torAmplitudeGE_of_isGE_of_forall_flat (hC : ∀ F : C, ObjectProperty.flat F)
    (K : DerivedCategory C) (b : ℤ) [K.IsGE b] : torAmplitudeGE C b K := fun F ↦ by
  have := isGE_tensor_of_torAmplitudeGE_right
    (torAmplitudeGE_of_torAmplitudeIn (torAmplitudeIn_singleFunctor_obj_of_flat (hC F))) K b
  rwa [add_zero] at this

end DerivedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme CondensedRing

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] [DiscreteTopology T]
  [Finite T]

/-- **Tensor products preserve module complexes of étale origin over a field**: if `T` is a field
and `Φ C`, `Φ D` are bounded below of étale origin, so is `Φ (C ⊗ D)`. Write `Φ C ≅ ν^* Q` and
`Φ D ≅ ν^* Q'` with `Q`, `Q'` bounded below; then `Φ (C ⊗ D) ≅ ν^* (Q ⊗ᴸ Q')`
(`ProEtale.finiteCoefficientDerivedEquivalenceTensorIso`,
`ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`), and `Q ⊗ᴸ Q'` is
bounded below as every étale sheaf of modules over a field is flat
(`AlgebraicGeometry.Etale.flat_of_isField`). -/
theorem plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj (hT : IsField T)
    {X : Scheme.{u}}
    {C D : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hC : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C))
    (hD : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj D)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj (C ⊗ D)) := by
  obtain ⟨Q, ⟨a, ha⟩, ⟨eQ⟩⟩ := hC
  obtain ⟨Q', ⟨b, hb⟩, ⟨eQ'⟩⟩ := hD
  have hΛ : IsField (ULift.{u + 1} T) := ULift.ringEquiv.toMulEquiv.isField hT
  have : (((Etale.derivedTensor (ModuleCat.{u + 1} (ULift.{u + 1} T)) X).obj Q).obj Q').IsGE
      (a + b) :=
    DerivedCategory.isGE_tensor_of_torAmplitudeGE
      (DerivedCategory.torAmplitudeGE_of_isGE_of_forall_flat (Etale.flat_of_isField hΛ) Q a) Q' b
  exact ⟨_, ⟨a + b, this⟩,
    ⟨(derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso _ Q).app Q' ≪≫
      ((ProEtale.derivedTensor _ X).mapIso eQ).app _ ≪≫
      ((ProEtale.derivedTensor _ X).obj _).mapIso eQ' ≪≫
      (finiteCoefficientDerivedEquivalenceTensorIso X T C D).symm⟩⟩

/-- **External products preserve module complexes of étale origin over a field**: if `T` is a
field and `Φ A`, `Φ B` are bounded below of étale origin, so is `Φ (Lf₁^* A ⊗ Lf₂^* B)`. -/
theorem plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj_leftDerivedUpperStar
    (hT : IsField T) {X₁ X₂ Y : Scheme.{u}} (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂)
    {A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₁) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X₁))}
    {B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X₂) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X₂))}
    (hA : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X₁
      ((finiteCoefficientDerivedEquivalence X₁ T).functor.obj A))
    (hB : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X₂
      ((finiteCoefficientDerivedEquivalence X₂ T).functor.obj B)) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) Y
      ((finiteCoefficientDerivedEquivalence Y T).functor.obj
        (L((f₁)^*⟦Profinite.continuousMapRingObj T⟧).obj A ⊗
          L((f₂)^*⟦Profinite.continuousMapRingObj T⟧).obj B)) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_tensorObj T hT
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T f₁ hA)
    (plusEtaleOrigin_finiteCoefficientDerivedEquivalence_leftDerivedUpperStar_obj T f₂ hB)

/-- **Bounded constructible module complexes are of étale origin**: for a bounded constructible
complex `C` of module objects over `Λ_X`, `Φ C` is bounded below of étale origin
(`ProEtale.isEtaleOrigin_of_isConstructible`). -/
theorem plusEtaleOrigin_finiteCoefficientDerivedEquivalence_of_boundedConstructible
    {X : Scheme.{u}}
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X))}
    (hC : boundedConstructible (condensedRingObj (Profinite.continuousMapRingObj T) X) C) :
    DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (ULift.{u + 1} T)) X
      ((finiteCoefficientDerivedEquivalence X T).functor.obj C) :=
  (isEtaleOrigin_of_isConstructible T hC).plusEtaleOrigin

namespace CondensedRing

open PadicAlgCl

/-- **Bounded constructible `𝔽_E`-complexes are of étale origin**: for a finite subextension
`E ⊆ ℚ̄_ℓ` with residue field `𝔽_E` and a bounded constructible complex `C` of module objects over
`𝔽̲_{E,X}`, `Φ C` is bounded below of étale origin. -/
theorem plusEtaleOrigin_of_boundedConstructible_residueField {ℓ : ℕ} [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) {X : Scheme.{u}}
    {C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) X))}
    (hC : boundedConstructible
      (condensedRingObj (Profinite.continuousMapRingObj (integersResidueField ℓ E.1)) X) C) :
    DerivedCategory.plusEtaleOrigin
      (ModuleCat.{u + 1} (ULift.{u + 1} (integersResidueField ℓ E.1))) X
      ((finiteCoefficientDerivedEquivalence X (integersResidueField ℓ E.1)).functor.obj C) :=
  plusEtaleOrigin_finiteCoefficientDerivedEquivalence_of_boundedConstructible _ hC

end CondensedRing

end AlgebraicGeometry.ProEtale
