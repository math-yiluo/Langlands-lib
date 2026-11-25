/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletedTensorReindex.PodCompletionTensorNormalization
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarTensorLevelTower

/-! # Naturality part of strict tensor tower reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers-naturality).

The quotient normalization fixes the comparison on reduced original-section
generators. Tensor extensionality and the tensor-map formula then prove the
naturality square before any derived limit is taken.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
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

attribute [local instance 2001] integralOperationsFiniteHasMap
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] integralOperationsTensorTowerFunctor
  Functor.ofOpSequence Functor.ofSequence
  integralOperationsTensorLevel integralOperationsRestrict integralOperationsTensorComposite
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj podGoodReindex isoSectionwiseModuleInverseImage
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj

/-- Evaluation of the strict tensor tower on a morphism is its finite-level map.
Source: the strict tower construction, Stacks 012Z
(blueprint: lem-pod-reindexing-strict-tensor-towers-naturality). -/
private theorem tensorTower_map_app (W : Scheme.{u}) (n : ℕ)
    {P Q P' Q' : CochainComplex (integralTowerModules l E W) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    ((integralOperationsTensorTowerFunctor l E W).map (Prod.mkHom a b)).app (op n) =
      (integralOperationsTensorLevel l E W n).map (Prod.mkHom a b) := by
  rfl

/-- Reindexing leaves the underlying section map unchanged.
Source: sectionwise inverse image along a site isomorphism, Stacks 00WX
(blueprint: lem-pod-reindexing-strict-tensor-towers-naturality). -/
private theorem reindexTower_map_section {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    {S T : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E Y) ℤ} (a : S ⟶ T)
    (n : ℕ) (k : ℤ) (U : X.ProEt)
    (x : ((S.obj (op n)).X k).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
    (((((podReindexTower l E g).map a).app (op n)).f k).val.app (op U)) x =
      (((a.app (op n)).f k).val.app (op ((proEtaleIsoPostcompose g).obj U))) x := by
  rfl

/-- Naturality of a generator-compatible strict tower family.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindexing-strict-tensor-towers-naturality).
STATEMENT-DISPUTED: the former signature omitted quotient normalization; repaired here.
The quotient-generator normalization is required: an arbitrary objectwise
family of quotient isomorphisms need not be natural. At scalar one it identifies
reduced original sections under D.quotient. The assumed tensor formula therefore
computes τ on tensors of these sections. Precompose the desired equality with
τ inverse, apply finite tensor extensionality, and use the inverse formula deduced
from τ hom-inverse cancellation. The tensor-map and reduction-map formulas send
both composites to the tensor of the same two mapped sections. Tower and complex
extensionality finish. This includes zero complexes, zero sections, and the empty site.
-/
theorem podReindexingStrictTensorTowersNaturality
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (D : PodCompletionReindex l E g) (hD : PodCompletionReindex.QuotientGenerators l E g D)
    (τ : ∀ P Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (podReindexTower l E g).obj
            ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj,Q.obj)) ≅
          (integralOperationsTensorTowerFunctor l E X).obj
            (((podGoodReindex l E g D).obj P).obj,((podGoodReindex l E g D).obj Q).obj))
    (hgen : ∀ (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
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
              ((((D.quotient Q.obj Q.property n).hom.f q).val.app (op U)) y)) :
      ∀ (P Q P' Q' : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (a : P ⟶ P') (b : Q ⟶ Q'),
        (podReindexTower l E g).map
            ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom)) ≫
            (τ P' Q').hom =
          (τ P Q).hom ≫ (integralOperationsTensorTowerFunctor l E X).map
            (Prod.mkHom ((podGoodReindex l E g D).map a).hom
              ((podGoodReindex l E g D).map b).hom) := by
  have hu (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (n : ℕ) (p : ℤ) (U : X.ProEt)
      (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :
      (((D.quotient P.obj P.property n).hom.f p).val.app (op U))
          (unrestrictedIntegralTensorSection l E Y n (P.obj.X p)
            (op ((proEtaleIsoPostcompose g).obj U)) 1 x) =
        unrestrictedIntegralTensorSection l E X n
          ((((podGoodReindex l E g D).obj P).obj).X p) (op U) 1 x := by
    have h := hD P.obj P.property n p U 1 x
    have h1 : (isoSectionwiseConstantMap.{u, u} g (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))).hom.app (op U) 1 =
        (1 : (integralCoefficientCommRingSheaf l E X n).obj.obj (op U)) := map_one _
    erw [h1] at h
    exact h
  have ht (P Q : (integralOperationsGoodComplex l E Y).FullSubcategory)
      (n : ℕ) (p q : ℤ) (U : X.ProEt)
      (x : (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U)))
      (y : (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U))) :=
    hgen P Q n p q U
      (unrestrictedIntegralTensorSection l E Y n (P.obj.X p)
        (op ((proEtaleIsoPostcompose g).obj U)) 1 x)
      (unrestrictedIntegralTensorSection l E Y n (Q.obj.X q)
        (op ((proEtaleIsoPostcompose g).obj U)) 1 y)
  simp only [hu] at ht
  intro P Q P' Q' a b
  apply (cancel_epi (τ P Q).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply NatTrans.ext
  funext n
  apply HomologicalComplex.hom_ext
  intro k
  apply finite_tensor_ext l E X n.unop
    (((podGoodReindex l E g D).obj P).obj)
    (((podGoodReindex l E g D).obj Q).obj) k
  intro p q hpq U x y
  subst k
  change (P.obj.X p).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) at x
  change (Q.obj.X q).val.obj (op ((proEtaleIsoPostcompose g).obj U.unop)) at y
  with_unfolding_all simp only [eqToHom_refl, SheafOfModules.id_val,
    PresheafOfModules.id_app]
  have hτ := ht P Q n.unop p q U.unop x y
  let sY := integralOperationsTotalTensorSection l E Y n.unop P.obj Q.obj p q
    (op ((proEtaleIsoPostcompose g).obj U.unop))
    (unrestrictedIntegralTensorSection l E Y n.unop (P.obj.X p)
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 x)
    (unrestrictedIntegralTensorSection l E Y n.unop (Q.obj.X q)
      (op ((proEtaleIsoPostcompose g).obj U.unop)) 1 y)
  have hi := congrArg (fun f ↦ (((f.app n).f (p + q)).val.app U) sY)
    (τ P Q).hom_inv_id
  have hi' := congrArg (fun z ↦ ((((τ P Q).inv.app n).f (p + q)).val.app U) z) hτ
  with_unfolding_all simp only [NatTrans.id_app, HomologicalComplex.id_f, SheafOfModules.id_val,
    PresheafOfModules.id_app] at hi
  have hinv := hi'.symm.trans hi
  with_unfolding_all simp only [NatTrans.comp_app, HomologicalComplex.comp_f,
    SheafOfModules.comp_val,
    PresheafOfModules.comp_app, CategoryTheory.comp_apply]
  erw [hinv]
  dsimp only [sY]
  erw [reindexTower_map_section l E g
    ((integralOperationsTensorTowerFunctor l E Y).map (Prod.mkHom a.hom b.hom))
    n.unop (p + q) U.unop]
  rw [tensorTower_map_app l E Y n.unop a.hom b.hom,
    tensorTower_map_app l E X n.unop
      ((podGoodReindex l E g D).map a).hom ((podGoodReindex l E g D).map b).hom]
  let sX := integralOperationsTotalTensorSection l E X n.unop
    (((podGoodReindex l E g D).obj P).obj) (((podGoodReindex l E g D).obj Q).obj)
    p q U
    (unrestrictedIntegralTensorSection l E X n.unop
      ((((podGoodReindex l E g D).obj P).obj).X p) U 1 x)
    (unrestrictedIntegralTensorSection l E X n.unop
      ((((podGoodReindex l E g D).obj Q).obj).X q) U 1 y)
  have idY : (𝟙 (((((podReindexTower l E g).obj
      ((integralOperationsTensorTowerFunctor l E Y).obj (P.obj, Q.obj))).obj n).X
        (p + q)).val.obj U)) sY = sY := by rfl
  have idX : (𝟙 ((((integralOperationsTensorLevel l E X n.unop).obj
      (((podGoodReindex l E g D).obj P).obj,
        ((podGoodReindex l E g D).obj Q).obj)).X (p + q)).val.obj U)) sX = sX := by rfl
  erw [idY, idX]
  dsimp only [sY, sX]
  erw [finite_tensor_map_section l E Y n.unop a.hom b.hom p q
    (op ((proEtaleIsoPostcompose g).obj U.unop))]
  erw [finite_reduction_map_section l E Y n.unop (a.hom.f p),
    finite_reduction_map_section l E Y n.unop (b.hom.f q), ht]
  erw [finite_tensor_map_section l E X n.unop
    ((podGoodReindex l E g D).map a).hom ((podGoodReindex l E g D).map b).hom p q U]
  erw [finite_reduction_map_section l E X n.unop,
    finite_reduction_map_section l E X n.unop]
  rfl

end WeilConjectures
