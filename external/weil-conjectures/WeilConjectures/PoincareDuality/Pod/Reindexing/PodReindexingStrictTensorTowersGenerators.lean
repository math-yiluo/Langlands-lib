/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingFiniteTensorComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # Generator part of strict tensor tower reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers-generators).

This is the first strictly smaller component of the strict-tower assertion. The
unproved construction is the sectionwise tensor comparison together with the two
quotient maps of `D`; its inverse is obtained from the inverse quotient maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The strict tower isomorphism and its pure tensor generator formula.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers).
The statement records only the levelwise isomorphism and the generator equation;
tower naturality is a separate component.
-/
theorem podReindexingStrictTensorTowersGenerators
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.Laws l E g D) :
    ∃ τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj),
      ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (n : ℕ) (p q : ℤ) (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj P.obj).X p).val.obj
          (op ((proEtaleIsoPostcompose g).obj U)))
        (y : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X q).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        ((((τ P Q).hom.app (op n)).f (p + q)).val.app (op U))
            (integralOperationsTotalTensorSection l E Y n P.obj Q.obj p q
              (op ((proEtaleIsoPostcompose g).obj U)) x y) =
          integralOperationsTotalTensorSection l E X n
            (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
            p q (op U) ((((D.quotient P.obj P.property n).hom.f p).val.app (op U)) x)
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y) := by
  classical
  have hc (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :=
    podReindexingFiniteTensorComparison l E g n P.obj Q.obj
      (((podGoodReindex l E g D).obj P).obj)
      (((podGoodReindex l E g D).obj Q).obj)
      (D.quotient P.obj P.property n) (D.quotient Q.obj Q.property n)
  choose e he using hc
  have ht (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) :
      (isoReductionIntegralComplex l E g).map
          ((integralOperationsTensorTransition l E Y n).app (P.obj, Q.obj)) ≫
        (e P Q n).hom =
      (e P Q (n + 1)).hom ≫
        (integralOperationsTensorTransition l E X n).app
          (((podGoodReindex l E g D).obj P).obj,
            ((podGoodReindex l E g D).obj Q).obj) := by
    apply (e P Q (n + 1)).inv_comp_eq.mp
    apply HomologicalComplex.hom_ext
    intro k
    let πm := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology X)).map
      (completedIntegralCommRingProjectionUnrestricted l E X (n + 1))
    let πn := (integralOperationsForgetSheaf.{u + 1} (ProEt.topology X)).map
      (completedIntegralCommRingProjectionUnrestricted l E X n)
    let δ := integralCoefficientSheafTransition l E X n
    have hπ : πm ≫ δ = πn := integralProjection_step l E X n
    let : Presheaf.IsLocallySurjective (ProEt.topology X) πm.hom :=
      completedProjection_locallySurjective l E X (n + 1)
    apply genericRestrictedTotal_hom_ext
      (integralCoefficientCommRingSheaf l E X (n + 1))
      (integralCoefficientCommRingSheaf l E X n) πm πn δ hπ
      ((unrestrictedIntegralFiniteComplex l E X (n + 1)).obj
        (((podGoodReindex l E g D).obj P).obj))
      ((unrestrictedIntegralFiniteComplex l E X (n + 1)).obj
        (((podGoodReindex l E g D).obj Q).obj))
      (((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)).obj
        ((unrestrictedIntegralFiniteComplex l E X n).obj
          (((podGoodReindex l E g D).obj P).obj),
         (unrestrictedIntegralFiniteComplex l E X n).obj
          (((podGoodReindex l E g D).obj Q).obj))).X k) k
    intro p q hpq U x y
    subst k
    let x₀ := ((D.quotient P.obj P.property (n + 1)).inv.f p).val.app U x
    let y₀ := ((D.quotient Q.obj Q.property (n + 1)).inv.f q).val.app U y
    have hx : ((D.quotient P.obj P.property (n + 1)).hom.f p).val.app U x₀ = x := by
      change (((D.quotient P.obj P.property (n + 1)).inv ≫
        (D.quotient P.obj P.property (n + 1)).hom).f p).val.app U x = x
      rw [Iso.inv_hom_id]
      rfl
    have hy : ((D.quotient Q.obj Q.property (n + 1)).hom.f q).val.app U y₀ = y := by
      change (((D.quotient Q.obj Q.property (n + 1)).inv ≫
        (D.quotient Q.obj Q.property (n + 1)).hom).f q).val.app U y = y
      rw [Iso.inv_hom_id]
      rfl
    have hg := he P Q (n + 1) p q U.unop x₀ y₀
    simp only [op_unop] at hg
    erw [hx, hy] at hg
    have hi : ((e P Q (n + 1)).inv.f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E X (n + 1)
          (((podGoodReindex l E g D).obj P).obj)
          (((podGoodReindex l E g D).obj Q).obj) p q U x y) =
        integralOperationsTotalTensorSection l E Y (n + 1) P.obj Q.obj p q
          (op ((proEtaleIsoPostcompose g).obj U.unop)) x₀ y₀ := by
      erw [← hg]
      change (((e P Q (n + 1)).hom ≫ (e P Q (n + 1)).inv).f (p + q)).val.app U _ = _
      rw [Iso.hom_inv_id]
      rfl
    change ((e P Q n).hom.f (p + q)).val.app U
        ((((integralOperationsTensorTransition l E Y n).app (P.obj, Q.obj)).f
          (p + q)).val.app (op ((proEtaleIsoPostcompose g).obj U.unop))
          (((e P Q (n + 1)).inv.f (p + q)).val.app U
            (integralOperationsTotalTensorSection l E X (n + 1)
              (((podGoodReindex l E g D).obj P).obj)
              (((podGoodReindex l E g D).obj Q).obj) p q U x y))) =
      (((integralOperationsTensorTransition l E X n).app
        ((((podGoodReindex l E g D).obj P).obj),
          (((podGoodReindex l E g D).obj Q).obj))).f (p + q)).val.app U
        (integralOperationsTotalTensorSection l E X (n + 1)
          (((podGoodReindex l E g D).obj P).obj)
          (((podGoodReindex l E g D).obj Q).obj) p q U x y)
    erw [hi, (integralOperationsTensorTransition_existsUnique l E Y n).exists.choose_spec]
    erw [he P Q n]
    have hquot : PodCompletionReindex.QuotientTransition l E g D :=
      hD.2.2.2.2.2.2.2.1
    erw [hquot P.obj P.property n p U.unop x₀,
      hquot Q.obj Q.property n q U.unop y₀, hx, hy]
    exact ((integralOperationsTensorTransition_existsUnique l E X n).exists.choose_spec
      _ _ p q U x y).symm
  let τ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory) :
      (podReindexTower l E g).obj
          ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) ≅
        (integralOperationsTensorTowerFunctor l E X).obj
          (((podGoodReindex l E g D).obj P).obj,
            ((podGoodReindex l E g D).obj Q).obj) := by
    let h : (podReindexTower l E g).obj
          ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj)) ⟶
        (integralOperationsTensorTowerFunctor l E X).obj
          (((podGoodReindex l E g D).obj P).obj,
            ((podGoodReindex l E g D).obj Q).obj) :=
      NatTrans.ofOpSequence (fun n ↦ (e P Q n).hom) (by
        intro n
        simpa only [podReindexTower, Functor.whiskeringRight_obj_obj,
          Functor.comp_map, Functor.comp_obj, integralOperationsTensorTowerFunctor,
          Functor.flip_obj_map, Functor.flip_obj_obj, Functor.ofOpSequence_obj,
          Functor.ofOpSequence_map_homOfLE_succ] using ht P Q n)
    exact NatIso.ofComponents (fun n ↦ e P Q n.unop) (fun f ↦ h.naturality f)
  refine ⟨τ, ?_⟩
  intro P Q n p q U x y
  exact he P Q n p q U x y

end WeilConjectures
