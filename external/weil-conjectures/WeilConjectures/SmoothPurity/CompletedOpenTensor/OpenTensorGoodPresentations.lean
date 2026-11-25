/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentativeData
import WeilConjectures.SixFunctors.CanonicalOpenRestriction.OpenRestrictionGoodComplex

/-! # Natural tensor presentations on good complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

attribute [local irreducible] IntegralOnSlice.duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard constantSheaf
  completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

/-- Natural tensor presentations on pairs of good complexes.
Source: Stacks sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
canonical derived tensor models, representative part of original step 4.
(blueprint: lem-pur-open-tensor-good-presentations).

Proof: lift exact extension and restriction from good complexes into the K-flat
subcategories. Whisker the natural canonical tensor models by those lifts. Compose
with tensor of the exact derived-functor representative counits and identities.
The two component equalities are the definitions of sourceRepresentative and
openRepresentative; the K-flatness witnesses agree by proof irrelevance. -/
theorem openTensorGoodPresentations (C : Context l E j) :
    ∃ (cs : ((integralOperationsGoodLocalization l E U).prod
          (integralOperationsGoodLocalization l E V)) ⋙ ordinarySource l E j C ≅
        ((((integralOperationsGoodComplex l E U).ι ⋙
            OpenSemilinearTensor.extensionComplex l E j C.operations).prod
          (integralOperationsGoodComplex l E V).ι) ⋙
            OpenSemilinearTensor.total l E V) ⋙ DerivedCategory.Q)
      (cu : ((integralOperationsGoodLocalization l E U).prod
          (integralOperationsGoodLocalization l E V)) ⋙ ordinaryOpen l E j C ≅
        (((integralOperationsGoodComplex l E U).ι.prod
          ((integralOperationsGoodComplex l E V).ι ⋙
            OpenSemilinearTensor.restrictionComplex l E j C.operations)) ⋙
              OpenSemilinearTensor.total l E U) ⋙ DerivedCategory.Q),
      (∀ (P : (integralOperationsGoodComplex l E U).FullSubcategory)
        (Q : (integralOperationsGoodComplex l E V).FullSubcategory),
        cs.app (P, Q) = sourceRepresentative l E j C P.obj Q.obj
          P.property.1 Q.property.1 P.property.2) ∧
      (∀ (P : (integralOperationsGoodComplex l E U).FullSubcategory)
        (Q : (integralOperationsGoodComplex l E V).FullSubcategory)
        (hR : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E U)
          ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q.obj)),
        cu.app (P, Q) = openRepresentative l E j C P.obj Q.obj P.property.1 hR) := by
  let iU := (integralOperationsGoodComplex l E U).ι
  let iV := (integralOperationsGoodComplex l E V).ι
  let LU := integralOperationsGoodLocalization l E U
  let LV := integralOperationsGoodLocalization l E V
  let ext := OpenSemilinearTensor.extensionComplex l E j C.operations
  let res := OpenSemilinearTensor.restrictionComplex l E j C.operations
  let extGood : (integralOperationsGoodComplex l E U).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E V)) :=
    ObjectProperty.lift _ (iU ⋙ ext)
      (fun P ↦ C.strictOpen.kflat P.obj P.property.1 P.property.2)
  let resGood : (integralOperationsGoodComplex l E V).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U)) :=
    ObjectProperty.lift _ (iV ⋙ res)
      (fun Q ↦ (CanonicalOpenRestriction.restriction_preservesGood l E j C.operations
        Q.obj Q.property).1)
  let idU : (integralOperationsGoodComplex l E U).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E U)) :=
    ObjectProperty.lift _ iU (fun P ↦ P.property.1)
  let idV : (integralOperationsGoodComplex l E V).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (CochainComplex.IsKFlatIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E V)) :=
    ObjectProperty.lift _ iV (fun Q ↦ Q.property.1)
  let H := ((iU ⋙ ext).prod iV) ⋙ OpenSemilinearTensor.total l E V
  let HU := (iU.prod (iV ⋙ res)) ⋙ OpenSemilinearTensor.total l E U
  let eext : LU ⋙ shriek l E j C.operations ≅ iU ⋙ ext ⋙ DerivedCategory.Q :=
    isoWhiskerLeft iU (extension l E j C.operations).mapDerivedCategoryFactors
  let eres : LV ⋙ star l E j C.operations ≅ iV ⋙ res ⋙ DerivedCategory.Q :=
    isoWhiskerLeft iV (restriction l E j C.operations).mapDerivedCategoryFactors
  let cs : (LU.prod LV) ⋙ ordinarySource l E j C ≅ H ⋙ DerivedCategory.Q :=
    isoWhiskerRight (NatIso.prod eext (Iso.refl LV)) (tensorV l E (V := V)) ≪≫
      (isoWhiskerLeft (extGood.prod idV)
        (IntegralOnSlice.duality l E V none).models.comparison).symm
  let cu : (LU.prod LV) ⋙ ordinaryOpen l E j C ≅ HU ⋙ DerivedCategory.Q :=
    isoWhiskerRight (NatIso.prod (Iso.refl LU) eres) (tensorU l E (U := U)) ≪≫
      (isoWhiskerLeft (idU.prod resGood)
        (IntegralOnSlice.duality l E U none).models.comparison).symm
  refine ⟨cs, cu, ?_, ?_⟩
  · intro P Q
    rfl
  · intro P Q hR
    rfl

end WeilConjectures.CompletedOpenTensor
