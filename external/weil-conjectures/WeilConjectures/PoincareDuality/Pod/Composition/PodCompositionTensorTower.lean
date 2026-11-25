/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorTowerComposition
import all WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorCompositionSections
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelReduction

/-! # Composition of normalized strict tensor tower maps

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-composition-tensor-tower).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsRoos integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 2001] integralOperationsFiniteHasMap
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
  Functor.ofOpSequence Functor.ofSequence
  integralOperationsTensorLevel integralOperationsRestrict integralOperationsTensorComposite
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

attribute [local irreducible] integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection integralOperationsTensorSection

-- The sectionwise tensor calculation keeps three coefficient transports explicit.
/-- Composition of the strict tensor-tower maps, before Roos realization.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-composition-tensor-tower).

Proof: at every positive quotient, apply the tensor generator formula to a
homogeneous pure tensor. The two factors are carried by the quotient comparisons.
Their coefficient-generator formulas and the section formula for the compositor
identify the successive restrictions with the composite restriction. Pure tensors
generate the presheaf tensor, the maps respect the sheafification units, and the
direct-sum inclusions generate each total degree. These facts give equality of the
whole degreewise maps. Every map is already a natural transformation of strict
towers. Extensionality in quotient level and degree gives the displayed natural
transformation equation, retaining every strict arrow. This is entirely before
products, cones, localization,
representative comparisons and the derived completed tensor. Zero complexes and
empty schemes satisfy the same generator argument. -/
theorem podCompositionTensorTower
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    [(isoReductionIntegralInverse l E f).Additive]
    [(isoReductionIntegralInverse l E h).Additive]
    [(isoReductionIntegralInverse l E (h ≫ f)).Additive]
    (hf : PodCompletionReindex.QuotientGenerators l E f (A.completion f))
    (hh : PodCompletionReindex.QuotientGenerators l E h (A.completion h))
    (hhf : PodCompletionReindex.QuotientGenerators l E (h ≫ f) (A.completion (h ≫ f)))
    (htf : PodCompletedTensorReindex.Generators l E f (A.completion f) (A.tensor f))
    (hth : PodCompletedTensorReindex.Generators l E h (A.completion h) (A.tensor h))
    (hthf : PodCompletedTensorReindex.Generators l E (h ≫ f)
      (A.completion (h ≫ f)) (A.tensor (h ≫ f)))
    (ha : ∀ (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory) :
    PodTensorTowerComposition l E A h f P Q  := by
  unfold PodTensorTowerComposition
  intro α FP FQ CY
  apply (cancel_epi ((A.tensor (h ≫ f)).tower P Q).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  apply finite_tensor_ext l E Z n.unop
    (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P).obj)
    (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q).obj) k
  intro p q hpq U x y
  subst k
  change (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop)) at x
  change (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop)) at y
  with_unfolding_all simp only [eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app]
  have hτ := tensor_unit_section l E (h ≫ f) (A.completion (h ≫ f)) hhf
    (A.tensor (h ≫ f)) hthf P Q n.unop p q U.unop x y
  let sY := integralOperationsTotalTensorSection l E V n.unop P.obj Q.obj p q
    (op ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop))
    (unrestrictedIntegralTensorSection l E V n.unop (P.obj.X p)
      (op ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop)) 1 x)
    (unrestrictedIntegralTensorSection l E V n.unop (Q.obj.X q)
      (op ((proEtaleIsoPostcompose (h ≫ f)).obj U.unop)) 1 y)
  have hi := congrArg (fun a ↦ (((a.app n).f (p + q)).val.app U) sY)
    ((A.tensor (h ≫ f)).tower P Q).hom_inv_id
  have hi' := congrArg
    (fun z ↦ (((((A.tensor (h ≫ f)).tower P Q).inv.app n).f (p + q)).val.app U) z) hτ
  with_unfolding_all simp only [NatTrans.id_app, HomologicalComplex.id_f,
    SheafOfModules.id_val, PresheafOfModules.id_app] at hi
  have hinv := hi'.symm.trans hi
  with_unfolding_all simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    SheafOfModules.comp_val, PresheafOfModules.comp_app, CategoryTheory.comp_apply]
  erw [hinv]
  let sX := integralOperationsTotalTensorSection l E Z n.unop
    (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P).obj)
    (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q).obj) p q U
    (unrestrictedIntegralTensorSection l E Z n.unop _ U 1 x)
    (unrestrictedIntegralTensorSection l E Z n.unop _ U 1 y)
  have idY : (𝟙 (((((podReindexTower l E (h ≫ f)).obj
      ((integralOperationsTensorTowerFunctor l E V).obj (P.obj, Q.obj))).obj n).X
        (p + q)).val.obj U)) sY = sY := by rfl
  have idX : (𝟙 ((((integralOperationsTensorLevel l E Z n.unop).obj
      (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P).obj,
        ((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q).obj)).X
          (p + q)).val.obj U)) sX = sX := by rfl
  erw [idY, idX]
  dsimp only [sY, sX]
  exact podTensorCompositionSections l E A h f hf hh htf hth ha
    P Q n.unop p q U.unop x y

end WeilConjectures
