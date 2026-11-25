/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.IntegralSystemOperations
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroExact
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.SixFunctors.IntegralSystemRealization.Ordinary.OrdinaryOpenFiniteEvaluation

/-! # Invertibility of the open evaluation mate

Source: Zheng Construction 4.1 and Lemma 4.10; Stacks 03DI and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

private theorem inverseMate_isIso_of_counit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (w : TwoSquare R₁ H G R₂) (e : L₁ ⋙ H ≅ G ⋙ L₂)
    (he : ∀ N, H.map (a.counit.app N) =
      e.hom.app (R₁.obj N) ≫ L₂.map (w.app N) ≫ b.counit.app (H.obj N)) :
    IsIso ((mateEquiv a b).symm w) := by
  have hm : mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv) = w := by
    refine NatTrans.ext (funext fun N ↦ ?_)
    apply (b.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    rw [mateEquiv_counit, he]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [← hm, Equiv.symm_apply_apply]
  exact e.isIso_inv

namespace WeilConjectures.IntegralSystemRealization
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private local instance additiveOfLimits
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [PreservesFiniteLimits F] : F.Additive :=
  Functor.additive_of_preserves_binary_products F

private local instance finiteLimits {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    PreservesFiniteLimits
      (show normalizedDVRModules l E X n ⥤ normalizedDVRModules l E U n from
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteLimits (finiteCoefficientRing l E (n + 1)) j

private local instance finiteColimits {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    PreservesFiniteColimits
      (show normalizedDVRModules l E X n ⥤ normalizedDVRModules l E U n from
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) j) :=
  sfIntrinsicPullback_preservesFiniteColimits (finiteCoefficientRing l E (n + 1)) j

private local instance extensionLimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) : PreservesFiniteLimits
      (show normalizedDVRModules l E U n ⥤ normalizedDVRModules l E X n from
        sfIntrinsicExtensionByZero j (finiteCoefficientRing l E (n + 1))) :=
  sfIntrinsicExtensionByZero_preservesFiniteLimits j (finiteCoefficientRing l E (n + 1))

private local instance extensionColimits {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (n : ℕ) : PreservesFiniteColimits
      (show normalizedDVRModules l E U n ⥤ normalizedDVRModules l E X n from
        sfIntrinsicExtensionByZero j (finiteCoefficientRing l E (n + 1))) :=
  sfIntrinsicExtensionByZero_preservesFiniteColimits j (finiteCoefficientRing l E (n + 1))

attribute [local irreducible] Functor.leftAdjoint Functor.mapDerivedCategory
  pullbackTensorSequenceInverse
  pullbackTensorSequenceInverseEvaluation pullbackTensorLevelIntrinsic

private def ordinaryEvaluation {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    pullbackTensorSequenceInverse l E j ⋙ coefficientSequenceEvaluation l E U n ≅
      coefficientSequenceEvaluation l E X n ⋙
        sfIntrinsicPullback (finiteCoefficientRing l E (n + 1)) j :=
  (pullbackTensorSequenceInverseEvaluation l E j n).symm ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceEvaluation l E X n)
      (pullbackTensorLevelIntrinsic l E j n)

private theorem ordinaryEvaluation_complex {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ)
    (P : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    (NatTrans.mapHomologicalComplex (ordinaryEvaluation l E j n).hom (.up ℤ)).app P =
      (pullbackTensorInverseEvaluationComplex l E j n).inv.app P ≫
        (NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic l E j n) (.up ℤ)).hom.app
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  simp [ordinaryEvaluation, pullbackTensorInverseEvaluationComplex]

private theorem derivedEvaluation_eq {U X : Scheme.{u}} (j : U ⟶ X) (n : ℕ) :
    Functor.mapDerivedCategorySquareIso
      (B' := normalizedDVRModules l E X n) (E := normalizedDVRModules l E U n)
      (ordinaryEvaluation l E j n) =
      pullbackTensorDerivedEvaluation l E j n := by
  apply (pullbackTensorDerivedEvaluation_existsUnique l E j n).unique
  · intro P
    have h := Functor.exactSquare_fac
      (E := normalizedDVRModules l E X n) (F := normalizedDVRModules l E U n)
      (ordinaryEvaluation l E j n) P
    rw [ordinaryEvaluation_complex l E j n P, DerivedCategory.Q.map_comp] at h
    exact h
  · exact (pullbackTensorDerivedEvaluation_existsUnique l E j n).exists.choose_spec

private theorem ordinaryMate_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (a : Open l E j) (n : ℕ) :
    IsIso ((mateEquiv a.adjunction
      (sfIntrinsicOpenAdjunction (finiteCoefficientRing l E (n + 1)) j)).symm
        (ordinaryEvaluation l E j n).hom) := by
  obtain ⟨L, b, e, he⟩ := ordinaryOpenFiniteEvaluation l E j a n
  let c := b.ofNatIsoRight (pullbackTensorLevelIntrinsic l E j n)
  have hc (N : coefficientSequenceModules l E X) :
      (coefficientSequenceEvaluation l E X n).map (a.adjunction.counit.app N) =
        e.hom.app ((pullbackTensorSequenceInverse l E j).obj N) ≫
          L.map ((ordinaryEvaluation l E j n).hom.app N) ≫
            c.counit.app ((coefficientSequenceEvaluation l E X n).obj N) := by
    simp only [ordinaryEvaluation, c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Adjunction.ofNatIsoRight_counit, Functor.whiskerRight_app, Functor.map_comp,
      Category.assoc]
    simpa only [← L.map_comp_assoc, Iso.hom_inv_id_app, L.map_id,
      Category.id_comp, Category.comp_id, Functor.comp_obj] using he N
  have : IsIso ((mateEquiv a.adjunction c).symm
      (ordinaryEvaluation l E j n).hom) :=
    inverseMate_isIso_of_counit a.adjunction c (ordinaryEvaluation l E j n).hom e hc
  exact inverseMate_change_left a.adjunction a.adjunction
    (sfIntrinsicOpenAdjunction (finiteCoefficientRing l E (n + 1)) j) c
    (ordinaryEvaluation l E j n).hom

/-- The evaluation mate for exact extension by zero is invertible on the full
sequence-site derived category.
Source: Zheng Construction 4.1; Stacks 03DI, 03DJ, 0941
(blueprint: lem-sf-integral-system-open-evaluation).

Proof: present an open immersion as localization of the ringed sequence site.
Ordinary extension by zero is the sheafification of the direct sum over lifts to
the open. Evaluation at n keeps the n-th summands and their coefficient action;
there is at most one lift, so this is the finite ordinary extension by zero.
The resulting evaluation comparison is an isomorphism. Its inverse is the mate
of the ordinary inverse-image evaluation comparison: on each summand the open
unit is the identity, so the two adjunction transposes agree. All four functors
are exact. Applying them termwise to complexes and localizing therefore preserves
this isomorphism and its mate equation. The fixed cochain normalization of
pullbackTensorDerivedEvaluation identifies the localized inverse-image comparison
with the one in the statement. Uniqueness of left adjoints transports the formula
from the slice extension to any a with its specified adjunction. For an empty
open all summands vanish, and for an identity open the comparison is the unitor;
the same argument applies to zero complexes. -/
theorem integralSystemOpenEvaluation_isIso {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (a : Open l E j) (n : ℕ) :
    IsIso ((mateEquiv a.adj (finiteOpenAdj l E j n)).symm
      (pullbackTensorDerivedEvaluation l E j n).hom) := by
  have := ordinaryMate_isIso l E j a n
  have h := (exact_localization_inverse_mate
    (A := coefficientSequenceModules l E U) (B := coefficientSequenceModules l E X)
    (D := normalizedDVRModules l E U n) (F := normalizedDVRModules l E X n) a.adjunction
    (sfIntrinsicOpenAdjunction (finiteCoefficientRing l E (n + 1)) j)
    (ordinaryEvaluation l E j n)).1
  rw [derivedEvaluation_eq l E j n] at h
  exact h

end WeilConjectures.IntegralSystemRealization
