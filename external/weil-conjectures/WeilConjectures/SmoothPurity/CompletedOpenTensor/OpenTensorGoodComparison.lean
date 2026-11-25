/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentativeData
import WeilConjectures.SmoothPurity.CompletedOpenTensor.OpenTensorGoodPresentations

/-! # The ordinary open comparison on good complexes -/

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

/-- The natural strict open tensor comparison on flat-term K-flat representatives.
Source: Stacks sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
representative part of original step 4.
(blueprint: lem-pur-open-tensor-good-comparison).

Proof: include good complexes into the K-flat tensor models. Whisker the canonical
natural tensor comparisons by exact extension and restriction and their representative
counits. TotalComparison.naturality makes its chain maps a natural isomorphism of
total complexes. Compose these three isomorphisms and the inverse extension counit.
Their components are definitionally the source and open representatives in the formula.
No completion or localization descent is asserted in this lemma. -/
theorem openTensorGoodComparison (C : Context l E j) :
    ∃ γ₀ : ((integralOperationsGoodLocalization l E U).prod
          (integralOperationsGoodLocalization l E V)) ⋙ ordinarySource l E j C ≅
        ((integralOperationsGoodLocalization l E U).prod
          (integralOperationsGoodLocalization l E V)) ⋙
            (ordinaryOpen l E j C ⋙ shriek l E j C.operations),
      ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ)
        (Q : CochainComplex (scalarReductionSource l E V) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E U) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E V) Q)
        (hfP : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)}
          (Scheme.ProEt.topology U) (completedIntegralCommRingSheafUnrestricted l E U) P)
        (hfQ : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)}
          (Scheme.ProEt.topology V) (completedIntegralCommRingSheafUnrestricted l E V) Q)
        (hR : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E U)
          ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q)),
        γ₀.hom.app (⟨P, hP, hfP⟩, ⟨Q, hQ, hfQ⟩) =
          (sourceRepresentative l E j C P Q hP hQ hfP).hom ≫
            DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom ≫
            (extension l E j C.operations).mapDerivedCategoryFactors.inv.app
              (openComplex l E j C P Q) ≫
            (shriek l E j C.operations).map (openRepresentative l E j C P Q hP hR).inv := by
  obtain ⟨cs, cu, hcs, hcu⟩ := openTensorGoodPresentations l E j C
  let iU := (integralOperationsGoodComplex l E U).ι
  let iV := (integralOperationsGoodComplex l E V).ι
  let LU := integralOperationsGoodLocalization l E U
  let LV := integralOperationsGoodLocalization l E V
  let ext := OpenSemilinearTensor.extensionComplex l E j C.operations
  let res := OpenSemilinearTensor.restrictionComplex l E j C.operations
  let H := ((iU ⋙ ext).prod iV) ⋙ OpenSemilinearTensor.total l E V
  let HU := (iU.prod (iV ⋙ res)) ⋙ OpenSemilinearTensor.total l E U
  let θ : H ≅ HU ⋙ ext := NatIso.ofComponents
    (fun A ↦ C.strictOpen.totalComparison.chain A.1.obj A.2.obj)
    (by
      intro A B f
      exact C.strictOpen.totalComparison.naturality f.1.hom f.2.hom)
  let γ₀ : (LU.prod LV) ⋙ ordinarySource l E j C ≅
      (LU.prod LV) ⋙ (ordinaryOpen l E j C ⋙ shriek l E j C.operations) :=
    cs ≪≫ isoWhiskerRight θ DerivedCategory.Q ≪≫
      (isoWhiskerLeft HU (extension l E j C.operations).mapDerivedCategoryFactors).symm ≪≫
      isoWhiskerRight cu.symm (shriek l E j C.operations)
  refine ⟨γ₀, ?_⟩
  intro P Q hP hQ hfP hfQ hR
  let A : (integralOperationsGoodComplex l E U).FullSubcategory := ⟨P, hP, hfP⟩
  let B : (integralOperationsGoodComplex l E V).FullSubcategory := ⟨Q, hQ, hfQ⟩
  change (cs.app (A, B)).hom ≫
      DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom ≫
      (extension l E j C.operations).mapDerivedCategoryFactors.inv.app
        (openComplex l E j C P Q) ≫
      (shriek l E j C.operations).map (cu.app (A, B)).inv = _
  rw [hcs A B, hcu A B hR]

end WeilConjectures.CompletedOpenTensor
