/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ConstructibleTensorModel.ConstructibleTensorCompletionPresentation
public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import Mathlib.CategoryTheory.Localization.Prod

/-! # Representative-normalized comparison of ordinary tensor models

Source: Stacks 07A4 and 06YS; fully faithful localization descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOfSpec false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralOrdinary
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local implicit_reducible] PurCompactSupport.completed
  integralOperationsGoodLocalization integralOperationsTensorOnGood
attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  pullbackTensorCalculus pullbackTensorIntegralTensorModel integralCompletedTensorComparison
  coefficientSequenceLimit

private theorem compare_localized_models
    {A B C : Type*} [Category* A] [Category* B] [Category* C]
    (q : A ⥤ B) (W : MorphismProperty A) [q.IsLocalization W]
    {T : A ⥤ C} {F G : B ⥤ C} (a : T ≅ q ⋙ F) (b : T ≅ q ⋙ G) :
    ∃ e : F ≅ G, ∀ P : A, a.hom.app P ≫ e.hom.app (q.obj P) = b.hom.app P := by
  let ff := Localization.fullyFaithfulWhiskeringLeft q W C
  let r := a.symm ≪≫ b
  let e : F ≅ G := ff.preimageIso r
  refine ⟨e, ?_⟩
  intro P
  have h := congrArg (fun z ↦ z.app P) (ff.map_preimage r.hom)
  change e.hom.app (q.obj P) = r.hom.app P at h
  exact (congrArg (fun z ↦ a.hom.app P ≫ z) h).trans
    (Iso.hom_inv_id_app_assoc a P _)

/-- Ordinary tensor and the supplied ringed tensor have the same signed total model.
Source: Stacks 07A4 and 06YS; the product localization universal property.
(blueprint: lem-sf-ordinary-tensor-ringed-model-comparison).

Proof: restrict the ringed tensor representative to the good complexes. Its source
is the same signed total tensor as tensorRepresentativeIso. Their composite gives
an isomorphism after precomposition by the product good localization. Fully faithful
whiskering lifts that isomorphism and its inverse. The map-preimage equation,
composed with the first representative, gives the displayed normalization on every
pair. Empty schemes and zero complexes use the same localization argument. -/
theorem tensorRingedModelComparison (X : Scheme.{u})
    (d : IntegralSystemRealization.RingedModels l E) :
    ∃ e : ConstructibleTensorModel.ordinaryTensor l E X ≅ (d.tensor X).ordinary.tensor,
      ∀ P Q : (integralOperationsGoodComplex l E X).FullSubcategory,
        (ConstructibleTensorModel.tensorRepresentativeIso l E X).hom.app (P, Q) ≫
          e.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
        (d.tensor X).ordinary.representative.hom.app
          (⟨P.obj, P.property⟩, ⟨Q.obj, Q.property⟩) := by
  let G := integralOperationsGoodComplex l E X
  let q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage G.ι
  let : q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  let i : G.FullSubcategory ⥤
      (proEtaleFlatRepresentatives X ((PurCompactSupport.completed l E).ring X)).FullSubcategory :=
    ObjectProperty.ιOfLE (fun _ h ↦ h)
  let r := Functor.isoWhiskerLeft (i.prod i) (d.tensor X).ordinary.representative
  obtain ⟨e, he⟩ := compare_localized_models (q.prod q) (W.prod W)
    (ConstructibleTensorModel.tensorRepresentativeIso l E X) r
  refine ⟨e, ?_⟩
  intro P Q
  simpa only [q, integralOperationsGoodLocalization, Functor.prod_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, r, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, i,
    ObjectProperty.ιOfLE] using
      he (P, Q)

end WeilConjectures.IntegralOrdinary
