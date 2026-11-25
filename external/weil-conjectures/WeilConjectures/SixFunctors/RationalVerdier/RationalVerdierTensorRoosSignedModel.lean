/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.RationalVerdier.RationalVerdierTensorTowerSignedCoordinate
import Mathlib.CategoryTheory.CommSq

/-! # Coherent signed braiding in the strict Roos tensor model

Source: Stacks 06YL, 08TC and 0941.
(blueprint: lem-coef-rational-verdier-tensor-roos-signed-model). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier
attribute [local irreducible] HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory coefficientTotalTensor pullbackTensorCalculus
  integralOperationsTensorTowerFunctor
  SheafOfModules.monoidalCategory
attribute [local implicit_reducible] pullbackTensorRestrictedTower
  integralOperationsGoodLocalization integralOperationsTensorOnGood
  integralOperationsTensorComplexFunctor pullbackTensorReferenceTensor
  coefficientSequenceInternalHom coefficientSequenceLimit integralOperationsRoosFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
/-- The coherent derived braiding is represented by the strict tower signed map.
There is no ordinary tensor augmentation in this statement: both source and target
are already completed tensor models.

Source: Stacks 06YL, 08TC, 0941; full tensor-model normalization and the signed
representative clause of the coherent braiding.
(blueprint: lem-coef-rational-verdier-tensor-roos-signed-model).

Proof: expand the reference tensor model into reduction, the coherent K-flat
comparison, the Roos limit model and the strict tensor-tower comparison. Coherent
reduction preserves K-flatness of the good inputs. The representative equation
for pullbackTensorBraiding identifies the signed total map with its derived
braiding after the coherent K-flat comparisons. Naturality of the limit/Roos
isomorphism transports it to Roos of the restricted signed map. The remaining
strict tensor-tower comparisons give precisely strictTensorSignedSwap. Cancel
the model isomorphisms on the two sides. No completeness of the inputs is used. -/
theorem tensor_roos_signed_model
    (P Q : (integralOperationsGoodComplex l E X).FullSubcategory) :
    DerivedCategory.Q.map
        (integralOperationsRoosFunctor.map (strictTensorSignedSwap l E X P.obj Q.obj)) ≫
        (pullbackTensorReferenceTensorModel l E X Q P).inv =
      (pullbackTensorReferenceTensorModel l E X P Q).inv ≫
        (coefficientSequenceLimit l E X).map
          ((pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X)
            (pullbackTensorCalculus l E X).systemClosed
            (pullbackTensorCalculus l E X).systemTensorModel).hom.app
              ((pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj P.obj),
               (pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj Q.obj))) := by
  let R := (pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)
  let L := coefficientSequenceLimit l E X
  let T := (pullbackTensorCalculus l E X).systemClosed.tensor
  let β := pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
    (pullbackTensorCalculus l E X).systemClosed
    (pullbackTensorCalculus l E X).systemTensorModel
  let σ := pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) (R.obj P.obj) (R.obj Q.obj)
  let a := T.mapIso (Iso.prod ((pullbackTensorReductionModel l E X).app P)
    ((pullbackTensorReductionModel l E X).app Q))
  let a' := T.mapIso (Iso.prod ((pullbackTensorReductionModel l E X).app Q)
    ((pullbackTensorReductionModel l E X).app P))
  let m := pullbackTensorSystemModel l E X _ _
    (pullbackTensorReductionGood l E X P) (pullbackTensorReductionGood l E X Q)
  let m' := pullbackTensorSystemModel l E X _ _
    (pullbackTensorReductionGood l E X Q) (pullbackTensorReductionGood l E X P)
  let S := (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)
  let C := HomologicalComplex.complexOfFunctorsToFunctorToComplex
    (T := ℕᵒᵖ) (V := integralTowerModules l E X) (c := .up ℤ)
  let r := Functor.isoWhiskerRight
      (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors
      (coefficientConstantTowerLimit l E X) ≪≫
    Functor.isoWhiskerLeft S (pullbackTensorRoosModel l E X)
  let t := pullbackTensorTensorTower l E X P.obj Q.obj
  let t' := pullbackTensorTensorTower l E X Q.obj P.obj
  let F := integralOperationsRoosFunctor (A := integralTowerModules l E X) ⋙ DerivedCategory.Q
  have hσ : DerivedCategory.Q.map σ.hom ≫ m'.hom =
      m.hom ≫ β.hom.app (DerivedCategory.Q.obj (R.obj P.obj),
        DerivedCategory.Q.obj (R.obj Q.obj)) := by
    dsimp only [σ, m, m', pullbackTensorSystemModel, β, pullbackTensorBraiding]
    exact (pullbackTensorBraiding_existsUnique _ _ _ _).exists.choose_spec _ _
      (pullbackTensorReductionGood l E X P) (pullbackTensorReductionGood l E X Q)
  have hm : CommSq
      (L.map (β.hom.app (DerivedCategory.Q.obj (R.obj P.obj),
        DerivedCategory.Q.obj (R.obj Q.obj)))) (L.map m.inv) (L.map m'.inv)
      (L.map (DerivedCategory.Q.map σ.hom)) := by
    exact (CommSq.mk hσ).vert_inv.map L
  have ha : CommSq
      (L.map (β.hom.app
        ((pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj P.obj),
          (pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj Q.obj))))
      (L.map a.hom) (L.map a'.hom)
      (L.map (β.hom.app (DerivedCategory.Q.obj (R.obj P.obj),
        DerivedCategory.Q.obj (R.obj Q.obj)))) := by
    have h := β.hom.naturality
      (Prod.mkHom ((pullbackTensorReductionModel l E X).hom.app P)
        ((pullbackTensorReductionModel l E X).hom.app Q))
    have h' : CommSq
        (β.hom.app
          ((pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj P.obj),
            (pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj Q.obj)))
        a.hom a'.hom
        (β.hom.app (DerivedCategory.Q.obj (R.obj P.obj),
          DerivedCategory.Q.obj (R.obj Q.obj))) := by
      constructor
      exact h.symm
    exact h'.map L
  have hr : CommSq (L.map (DerivedCategory.Q.map σ.hom))
      (r.app _).hom (r.app _).hom (F.map (C.map (S.map σ.hom))) := by
    constructor
    exact r.hom.naturality σ.hom
  have ht : CommSq (F.map (C.map (S.map σ.hom))) (F.map t.hom) (F.map t'.hom)
      (F.map (strictTensorSignedSwap l E X P.obj Q.obj)) := by
    constructor
    change F.map (C.map (S.map σ.hom)) ≫ F.map t'.hom =
      F.map t.hom ≫ F.map (t.inv ≫ C.map (S.map σ.hom) ≫ t'.hom)
    rw [← F.map_comp, ← F.map_comp, Iso.hom_inv_id_assoc]
  have h := ha.vert_comp (hm.vert_comp (hr.vert_comp ht))
  have hh : CommSq
      (L.map (β.hom.app
        ((pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj P.obj),
          (pullbackTensorCalculus l E X).reduction.obj (DerivedCategory.Q.obj Q.obj))))
      (pullbackTensorReferenceTensorModel l E X P Q).hom
      (pullbackTensorReferenceTensorModel l E X Q P).hom
      (F.map (strictTensorSignedSwap l E X P.obj Q.obj)) := by
    have he (K : CochainComplex (coefficientSequenceModules l E X) ℤ) :
        (r.app K).hom = (pullbackTensorLimitRoos l E X K).hom := by
      rfl
    have hw := h.w
    constructor
    dsimp only [pullbackTensorReferenceTensorModel, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom] at hw ⊢
    dsimp only [a, a', m, m', t, t', F, L, Functor.comp_map] at hw
    simp only [he] at hw
    simp only [Category.assoc, Functor.mapIso_hom, T, R, L, F, Functor.comp_map,
      Functor.comp_obj, Functor.prod_obj, ObjectProperty.ι_obj] at hw ⊢
    exact hw
  exact hh.vert_inv.w

end WeilConjectures.RationalVerdier
