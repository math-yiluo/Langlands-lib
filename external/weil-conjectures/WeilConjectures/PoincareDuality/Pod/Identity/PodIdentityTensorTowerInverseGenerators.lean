/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorModels

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
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
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped TensorProduct ChangeOfRings
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] integralOperationsRoos
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
  integralOperationsTensorLevel integralOperationsTensorComposite podGoodReindex
  SheafOfModules.restrictScalars Functor.map₂HomologicalComplex
  Functor.ofOpSequence Functor.ofSequence
attribute [local implicit_reducible] isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward
  PresheafOfModules.pushforward₀ PresheafOfModules.pushforward₀Obj
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'

private theorem quotient_unit_section
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (D : PodCompletionReindex l E g)
    (hD : PodCompletionReindex.QuotientGenerators l E g D)
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

attribute [local irreducible] integralOperationsTotalTensorSection
  unrestrictedIntegralTensorSection

/-- The inverse normalized strict tensor comparison fixes unit tensor generators.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-identity-tensor-tower-inverse-generators).

Proof: QuotientGenerators carries each unit reduction section to the corresponding
unit section, because the coefficient relabelling preserves one. Generators then
carries the total tensor of the two original unit sections to the reindexed total
tensor. Apply the inverse tensor comparison to this equality and use hom_inv_id
at the quotient index, degree and site object. -/
theorem podIdentityTensorTowerInverseGenerators
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)]
    (D : PodCompletionReindex l E (𝟙 W))
    (hD : PodCompletionReindex.QuotientGenerators l E (𝟙 W) D)
    (T : PodCompletedTensorReindex l E (𝟙 W) D)
    (hT : PodCompletedTensorReindex.Generators l E (𝟙 W) D T)
    (P Q : (integralOperationsGoodComplex l E W).FullSubcategory)
    (n : ℕ) (p q : ℤ) (U : W.ProEtᵒᵖ)
    (x : ((((podGoodReindex l E (𝟙 W) D).obj P).obj).X p).val.obj U)
    (y : ((((podGoodReindex l E (𝟙 W) D).obj Q).obj).X q).val.obj U) :
    (((T.tower P Q).inv.app (op n)).f (p + q)).val.app U
      (integralOperationsTotalTensorSection l E W n
        ((podGoodReindex l E (𝟙 W) D).obj P).obj
        ((podGoodReindex l E (𝟙 W) D).obj Q).obj p q U
        (unrestrictedIntegralTensorSection l E W n _ U 1 x)
        (unrestrictedIntegralTensorSection l E W n _ U 1 y)) =
      integralOperationsTotalTensorSection l E W n P.obj Q.obj p q
        (op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop))
        (unrestrictedIntegralTensorSection l E W n (P.obj.X p)
          (op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop)) 1 x)
        (unrestrictedIntegralTensorSection l E W n (Q.obj.X q)
          (op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop)) 1 y) := by
  let V := op ((proEtaleIsoPostcompose (𝟙 W)).obj U.unop)
  let x₀ := unrestrictedIntegralTensorSection l E W n (P.obj.X p) V 1 x
  let y₀ := unrestrictedIntegralTensorSection l E W n (Q.obj.X q) V 1 y
  have ht := hT P Q n p q U.unop x₀ y₀
  simp only [op_unop] at ht
  erw [quotient_unit_section l E (𝟙 W) D hD,
    quotient_unit_section l E (𝟙 W) D hD] at ht
  calc
    _ = (((T.tower P Q).inv.app (op n)).f (p + q)).val.app U
        ((((T.tower P Q).hom.app (op n)).f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W n P.obj Q.obj p q V x₀ y₀)) :=
      congrArg (fun z ↦ (((T.tower P Q).inv.app (op n)).f (p + q)).val.app U z) ht.symm
    _ = _ := by
      have hc := congrArg
        (fun f ↦ ((f.app (op n)).f (p + q)).val.app U
          (integralOperationsTotalTensorSection l E W n P.obj Q.obj p q V x₀ y₀))
        (T.tower P Q).hom_inv_id
      simpa only [NatTrans.comp_app, HomologicalComplex.comp_f,
        SheafOfModules.comp_val, PresheafOfModules.comp_app, ConcreteCategory.comp_apply,
        NatTrans.id_app, HomologicalComplex.id_f, SheafOfModules.id_val,
        PresheafOfModules.id_app, ModuleCat.id_apply] using hc

end WeilConjectures
