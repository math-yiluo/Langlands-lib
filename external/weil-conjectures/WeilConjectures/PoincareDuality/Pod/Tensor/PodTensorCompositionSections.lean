/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Tensor.PodTensorTowerComposition
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingFiniteTensorComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower
import all WeilConjectures.CategoryTheory.Ringed.RingedHomCompositionModel
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement

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

private theorem total_restrict (S : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E S) ℤ) (p q : ℤ)
    {U V : S.ProEtᵒᵖ} (a : U ⟶ V)
    (x : (((unrestrictedIntegralFiniteComplex l E S n).obj P).X p).val.obj U)
    (y : (((unrestrictedIntegralFiniteComplex l E S n).obj Q).X q).val.obj U) :
    ((((integralOperationsTensorLevel l E S n).obj (P,Q)).X (p+q)).val.map a)
        (integralOperationsTotalTensorSection l E S n P Q p q U x y) =
      integralOperationsTotalTensorSection l E S n P Q p q V
        ((((unrestrictedIntegralFiniteComplex l E S n).obj P).X p).val.map a x)
        ((((unrestrictedIntegralFiniteComplex l E S n).obj Q).X q).val.map a y) := by
  rw [← finiteTensorGenerator_eq, ← finiteTensorGenerator_eq]
  exact CategoryTheory.HomCompositionProof.generator_restrict (ProEt.topology S)
    (integralCoefficientCommRingSheaf l E S n) _ _ p q (p+q) rfl a x y

open scoped TensorProduct ChangeOfRings in
private theorem reduction_restrict (S : Scheme.{u}) (n : ℕ)
    (M : integralTowerModules l E S) {U V : S.ProEtᵒᵖ} (a : U ⟶ V)
    (x : M.val.obj U) :
    ((unrestrictedIntegralReductionFunctor l E S n).obj M).val.map a
        (unrestrictedIntegralTensorSection l E S n M U 1 x) =
      unrestrictedIntegralTensorSection l E S n M V 1 (M.val.map a x) := by
  unfold unrestrictedIntegralTensorSection
  erw [← PresheafOfModules.naturality_apply]
  apply congrArg ((eqToHom
    ((scalarReductionExistence l E S n).choose_spec.choose M).symm).val.app V)
  change ((SheafOfModules.changeOfRings
    (completedIntegralCommRingProjectionUnrestricted l E S n) M).val.presheaf.map a)
      ((toSheafify (ProEt.topology S)
        (SheafOfModules.changeOfRingsPresheaf
          (completedIntegralCommRingProjectionUnrestricted l E S n) M).presheaf).app U
            ((1 : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
              ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E S).obj.obj U,
                ((completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U).hom] x)) = _
  have hn := NatTrans.naturality_apply
    (toSheafify (ProEt.topology S)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E S n) M).presheaf) a
      ((1 : (integralCoefficientCommRingSheaf l E S n).obj.obj U)
        ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E S).obj.obj U,
          ((completedIntegralCommRingProjectionUnrestricted l E S n).hom.app U).hom] x)
  have hr := SheafOfModules.UnrestrictedTowerProof.restriction_tmul
    (completedIntegralCommRingProjectionUnrestricted l E S n) M a
    (1 : (integralCoefficientCommRingSheaf l E S n).obj.obj U) x
  rw [map_one] at hr
  with_unfolding_all exact hn.symm.trans (congrArg
    ((toSheafify (ProEt.topology S)
      (SheafOfModules.changeOfRingsPresheaf
        (completedIntegralCommRingProjectionUnrestricted l E S n) M).presheaf).app V) hr)

private theorem quotient_unit_section
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.QuotientGenerators l E g D)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (hP : integralOperationsGoodComplex l E Y P) (n : ℕ) (i : ℤ) (U : X.ProEt)
    (x : (P.X i).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((D.quotient P hP n).hom.f i).val.app (op U))
        (unrestrictedIntegralTensorSection l E Y n (P.X i)
          (op ((proEtaleIsoPostcompose g).obj U)) 1 x) =
      unrestrictedIntegralTensorSection l E X n
        (((isoReductionIntegralComplex l E g).obj P).X i) (op U) 1 x := by
  have h := hD P hP n i U 1 x
  have ho : ((isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
      (ULift.{u+1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U)) 1 = 1 :=
    (RingCat.Hom.hom _).map_one
  exact h.trans (congrArg (fun c ↦ unrestrictedIntegralTensorSection l E X n
    (((isoReductionIntegralComplex l E g).obj P).X i) (op U) c x) ho)

private theorem tensor_unit_section
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g)
    (hD : PodCompletionReindex.QuotientGenerators l E g D)
    (T : PodCompletedTensorReindex l E g D)
    (hT : PodCompletedTensorReindex.Generators l E g D T)
    (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
    (n : ℕ) (p q : ℤ) (U : X.ProEt)
    (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
    (y : (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    ((((T.tower P Q).hom.app (op n)).f (p+q)).val.app (op U))
      (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
        (op ((proEtaleIsoPostcompose g).obj U))
        (unrestrictedIntegralTensorSection l E Y n (P.obj.X p)
          (op ((proEtaleIsoPostcompose g).obj U)) 1 x)
        (unrestrictedIntegralTensorSection l E Y n (Q.obj.X q)
          (op ((proEtaleIsoPostcompose g).obj U)) 1 y)) =
      integralOperationsTotalTensorSection l E X n
        (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
        p q (op U)
        (unrestrictedIntegralTensorSection l E X n
          ((((podGoodReindex l E g D).obj P).obj).X p) (op U) 1 x)
        (unrestrictedIntegralTensorSection l E X n
          ((((podGoodReindex l E g D).obj Q).obj).X q) (op U) 1 y) := by
  rw [hT]
  rw [quotient_unit_section l E g D hD, quotient_unit_section l E g D hD]
  rfl

private theorem unit_total_restrict (S : Scheme.{u}) (n : ℕ)
    (P Q : CochainComplex (integralTowerModules l E S) ℤ) (p q : ℤ)
    {U V : S.ProEtᵒᵖ} (a : U ⟶ V)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((integralOperationsTensorLevel l E S n).obj (P,Q)).X (p+q)).val.map a)
        (integralOperationsTotalTensorSection l E S n P Q p q U
          (unrestrictedIntegralTensorSection l E S n (P.X p) U 1 x)
          (unrestrictedIntegralTensorSection l E S n (Q.X q) U 1 y)) =
      integralOperationsTotalTensorSection l E S n P Q p q V
        (unrestrictedIntegralTensorSection l E S n (P.X p) V 1 ((P.X p).val.map a x))
        (unrestrictedIntegralTensorSection l E S n (Q.X q) V 1 ((Q.X q).val.map a y)) := by
  rw [total_restrict l E S n P Q p q a]
  erw [reduction_restrict l E S n (P.X p) a x,
    reduction_restrict l E S n (Q.X q) a y]

attribute [local irreducible] integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection integralOperationsTensorSection

-- The sectionwise tensor calculation keeps three coefficient transports explicit.
/-- Successive tensor comparisons agree on the original unit-coefficient generators.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-tensor-composition-sections).
Proof: the ordinary compositor restricts both original sections. Restriction
commutes with finite reduction units and total tensor inclusions. Apply the two
successive tensor generator equations. On the other side, the total tensor map
acts on each factor; naturality of reduction units and the compositor section
formula give precisely the same two sections. No tower extensionality, inverse
comparison, Roos construction or localization is involved. -/
theorem podTensorCompositionSections
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
    (htf : PodCompletedTensorReindex.Generators l E f (A.completion f) (A.tensor f))
    (hth : PodCompletedTensorReindex.Generators l E h (A.completion h) (A.tensor h))
    (ha : ∀ (M : scalarReductionSource l E V) (U : Z.ProEt)
      (x : M.val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))),
      ((A.composition h f).hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale f)).inv.app U).op x)
    (P Q : (integralOperationsGoodComplex l E V).FullSubcategory)
    (n : ℕ) (p q : ℤ) (U : Z.ProEt)
    (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)))
    (y : (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))) :
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    let FP := (podGoodReindex l E f (A.completion f)).obj P
    let FQ := (podGoodReindex l E f (A.completion f)).obj Q
    let CY := (integralOperationsTensorTowerFunctor l E V).obj (P.obj, Q.obj)
    (((((A.tensor h).tower FP FQ).hom.app (op n)).f (p+q)).val.app (op U))
      (((((A.tensor f).tower P Q).hom.app (op n)).f (p+q)).val.app
        (op ((proEtaleIsoPostcompose h).obj U))
        ((((α.hom.app (CY.obj (op n))).f (p+q)).val.app (op U))
          (integralOperationsTotalTensorSection l E V n P.obj Q.obj p q
            (op ((proEtaleIsoPostcompose (h ≫ f)).obj U))
            (unrestrictedIntegralTensorSection l E V n (P.obj.X p)
              (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) 1 x)
            (unrestrictedIntegralTensorSection l E V n (Q.obj.X q)
              (op ((proEtaleIsoPostcompose (h ≫ f)).obj U)) 1 y)))) =
      ((((integralOperationsTensorLevel l E Z n).map
        (Prod.mkHom (α.hom.app P.obj) (α.hom.app Q.obj))).f (p+q)).val.app (op U))
        (integralOperationsTotalTensorSection l E Z n
          (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj P).obj)
          (((podGoodReindex l E (h ≫ f) (A.completion (h ≫ f))).obj Q).obj) p q (op U)
          (unrestrictedIntegralTensorSection l E Z n _ (op U) 1 x)
          (unrestrictedIntegralTensorSection l E Z n _ (op U) 1 y)) := by
  intro α FP FQ CY
  have hα (K : CochainComplex (scalarReductionSource l E V) ℤ) (i : ℤ) :
      (α.hom.app K).f i = (A.composition h f).hom.app (K.X i) := by
    change (A.composition h f).hom.app (K.X i) ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [hα]
  erw [ha]
  erw [unit_total_restrict l E V n P.obj Q.obj p q]
  erw [tensor_unit_section l E f (A.completion f) hf (A.tensor f) htf]
  erw [tensor_unit_section l E h (A.completion h) hh (A.tensor h) hth]
  erw [finite_tensor_map_section l E Z n]
  simp only [Functor.mapHomologicalComplex_map_f]
  erw [finite_reduction_map_section, finite_reduction_map_section]
  rw [hα, hα]
  erw [ha, ha]
  rfl

end WeilConjectures
