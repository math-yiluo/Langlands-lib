/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedOpenTensor.CompletedOpenTensorRepresentativeData
import WeilConjectures.SmoothPurity.CompletedOpenTensor.OpenTensorGoodComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Descent of the ordinary open total tensor comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
namespace WeilConjectures.CompletedOpenTensor
open IntegralOpenReduction

attribute [local irreducible] IntegralOnSlice.duality SheafOfModules.monoidalCategory
  HasDerivedCategory.standard

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U V : Scheme.{t}} (j : U ⟶ V) [IsOpenImmersion j]

/-- The ordinary open total-tensor chain map descends with its representative counits.
Source: Stacks sites-cohomology.tex Tag 0GL1 and sites-modules.tex Tag 0E8I;
step 4 of lem-pur-completed-open-tensor-representatives.
(blueprint: lem-pur-open-tensor-ordinary-descent).

Proof: exact open restriction is the scalar-normalized slice inverse image. The existing
restriction theorem preserves
flat-term K-flat complexes. Restrict both inputs to the resolving categories of such complexes.
The derived tensor model comparisons, the exact extension/restriction representative
counits, and strictOpen.totalComparison.chain give a natural isomorphism between
restrictions of the two ordinary derived bifunctors. TotalComparison.naturality
proves naturality before localization. The two-variable localization universal
property descends this natural isomorphism uniquely. Its map-preimage equation is
exactly the displayed square with sourceRepresentative and openRepresentative.
The comparison is natural for arbitrary derived inputs; only its computation uses
flat-term K-flat inputs. There are no completion, quotient reduction or total-limit
assertions in this step. Zero complexes and empty or identity open immersions obey
the same chain formulas and require no additional hypothesis. -/
theorem openTensorOrdinaryDescent (C : Context l E j) :
    ∃ γ : OrdinaryMap l E j C,
      ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ)
        (Q : CochainComplex (scalarReductionSource l E V) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E U) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients
          (R := completedIntegralCommRingSheafUnrestricted l E V) Q)
        (hfP : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)}
          (Scheme.ProEt.topology U) (completedIntegralCommRingSheafUnrestricted l E U) P)
        (_hfQ : SemilinearSections.flatTerms.{t + 1, t, max u (t + 1)}
          (Scheme.ProEt.topology V) (completedIntegralCommRingSheafUnrestricted l E V) Q)
        (hR : CochainComplex.IsKFlatIndependentCoefficients
            (R := completedIntegralCommRingSheafUnrestricted l E U)
            ((OpenSemilinearTensor.restrictionComplex l E j C.operations).obj Q)),
          (γ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              (shriek l E j C.operations).map (openRepresentative l E j C P Q hP hR).hom ≫
              (extension l E j C.operations).mapDerivedCategoryFactors.hom.app
                (openComplex l E j C P Q) =
            (sourceRepresentative l E j C P Q hP hQ hfP).hom ≫
              DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom)  := by
  obtain ⟨γ₀, hγ₀⟩ := openTensorGoodComparison l E j C
  let iU := (integralOperationsGoodComplex l E U).ι
  let iV := (integralOperationsGoodComplex l E V).ι
  let LU := integralOperationsGoodLocalization l E U
  let LV := integralOperationsGoodLocalization l E V
  let WU := (HomologicalComplex.quasiIso (scalarReductionSource l E U) (.up ℤ)).inverseImage iU
  let WV := (HomologicalComplex.quasiIso (scalarReductionSource l E V) (.up ℤ)).inverseImage iV
  let : LU.IsLocalization WU := integralOperationsGoodLocalization_isLocalization l E U
  let : LV.IsLocalization WV := integralOperationsGoodLocalization_isLocalization l E V
  let F := ordinarySource l E j C
  let G := ordinaryOpen l E j C ⋙ shriek l E j C.operations
  let : Localization.Lifting (LU.prod LV) (WU.prod WV) ((LU.prod LV) ⋙ F) F := ⟨Iso.refl _⟩
  let : Localization.Lifting (LU.prod LV) (WU.prod WV) ((LU.prod LV) ⋙ G) G := ⟨Iso.refl _⟩
  let γ : F ≅ G := Localization.liftNatIso (LU.prod LV) (WU.prod WV)
    ((LU.prod LV) ⋙ F) ((LU.prod LV) ⋙ G) F G γ₀
  refine ⟨γ, ?_⟩
  intro P Q hP hQ hfP hfQ hR
  let A : (integralOperationsGoodComplex l E U).FullSubcategory := ⟨P, hP, hfP⟩
  let B : (integralOperationsGoodComplex l E V).FullSubcategory := ⟨Q, hQ, hfQ⟩
  have hc : γ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      γ₀.hom.app (A, B) := by
    change (Localization.liftNatTrans (LU.prod LV) (WU.prod WV)
      ((LU.prod LV) ⋙ F) ((LU.prod LV) ⋙ G) F G γ₀.hom).app
        ((LU.prod LV).obj (A, B)) = _
    rw [Localization.liftNatTrans_app]
    change (𝟙 _ ≫ γ₀.hom.app (A, B) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  rw [hc, hγ₀ P Q hP hQ hfP hfQ hR]
  simp only [Category.assoc]
  rw [← (shriek l E j C.operations).map_comp_assoc,
    Iso.inv_hom_id, (shriek l E j C.operations).map_id, Category.id_comp,
    Iso.inv_hom_id_app]
  exact congrArg
    (fun f ↦ (sourceRepresentative l E j C P Q hP hQ hfP).hom ≫ f)
    (Category.comp_id (DerivedCategory.Q.map (C.strictOpen.totalComparison.chain P Q).hom))

end WeilConjectures.CompletedOpenTensor
