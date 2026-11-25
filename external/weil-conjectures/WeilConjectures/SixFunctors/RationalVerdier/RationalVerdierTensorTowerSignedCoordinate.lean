/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
public import WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import WeilConjectures.SixFunctors.RationalVerdier.CoefficientTensorTowerSignedSquare
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralTensorTransitionCompatibility
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerTransitionSquare

/-! # Signed interchange in the strict finite tensor tower

Source: Stacks 03EL, 06YL, 07A4 and 0941.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.RationalVerdier
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Restrict the coherent chain braiding to its actual strict quotient tower and
transport through the fixed finite tensor comparisons. It is defined before
completion and does not use any ordinary-to-completed augmentation.
Source: Stacks 06YL, 07A4, 0941.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate). -/
def strictTensorSignedSwap
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) :
    (integralOperationsTensorTowerFunctor l E X).obj (P, Q) ⟶
      (integralOperationsTensorTowerFunctor l E X).obj (Q, P) :=
  (pullbackTensorTensorTower l E X P Q).inv ≫
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
        (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj Q)).hom) ≫
    (pullbackTensorTensorTower l E X Q P).hom

section Helpers
attribute [local implicit_reducible] sheafCompose
  integralCoefficientCommRingSheaf
attribute [local implicit_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.restrict
  integralCoefficientSheaf
  unrestrictedIntegralReductionFunctor
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [local irreducible] coefficientTensorGenerator
  pullbackTensorTensorTower pullbackTensorTensorTowerLevel
  coefficientEvaluationTensorIso SheafOfModules.monoidalCategory
  completedIntegralCommRingSheafUnrestricted
  pullbackTensorRestrictedLevel pullbackTensorReductionEvaluationComplex
  pullbackTensorOrdinaryReduction coefficientSequenceEvaluation coefficientSequenceRestriction
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceTopology

private theorem generator_transport
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (i j k : ℤ) (h : i + j = k) (U : X.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R P Q i j k h U x y =
      (eqToHom (congrArg
        (fun n : ℤ ↦ (((IntegralHom.totalTensor.{u, u} X R).obj P).obj Q).X n)
          h)).val.app U (IntegralHom.totalPair.{u, u} X R P Q i j U x y) := by
  subst k
  unfold coefficientTensorGenerator
  rfl

private theorem strict_signed_level
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) :
    (strictTensorSignedSwap l E X P Q).app (op n) =
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        (pullbackTensorSignedTotal (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)
          ((unrestrictedIntegralFiniteComplex l E X n).obj P)
          ((unrestrictedIntegralFiniteComplex l E X n).obj Q)).hom := by
  exact ((pullbackTensorTensorTower l E X P Q).app (op n)).inv_comp_eq.mpr
    (coefficientTensorTower_signed_square l E X P Q n)

private theorem tower_normalization
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ)
    (p q k : ℤ) (h : p + q = k) (U : X.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)).app (op n)).f k).val.app U
      (IntegralOnSlice.generator l E X none n _ U a
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q k h U x y)) =
      coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        ((unrestrictedIntegralFiniteComplex l E X n).obj P)
        ((unrestrictedIntegralFiniteComplex l E X n).obj Q) p q k h U
        (unrestrictedIntegralTensorSection l E X n (P.X p) U a x)
        (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y) := by
  subst k
  have hn := (IntegralAmbient.tensorTowerModel l E X).exists.choose_spec P Q n p q U a x y
  change _ = integralOperationsTotalTensorSection l E X n P Q p q U _ _ at hn
  exact hn.trans (finite_coefficient_generator l E X P Q n p q U _ _).symm

private theorem tensorGenerator_smul_right
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (P Q : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : X.ProEtᵒᵖ) (a : R.obj.obj U)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
        P Q p q k h U x (a • y) =
      a • coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
        P Q p q k h U x y := by
  let b := pullbackTensorSignedTotal (ProEt.topology X) R P Q
  have hinv (x : (((coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) R).obj (P, Q)).X k).val.obj U) :
      (b.inv.f k).val.app U ((b.hom.f k).val.app U x) = x :=
    congrArg (fun f : (coefficientTotalTensor.{u, u + 1, u}
      (ProEt.topology X) R).obj (P, Q) ⟶
        (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R).obj (P, Q) ↦
      (f.f k).val.app U x) b.hom_inv_id
  have hi : Function.Injective ((b.hom.f k).val.app U) := by
    intro x y hxy
    exact (hinv x).symm.trans
      ((congrArg ((b.inv.f k).val.app U) hxy).trans (hinv y))
  have hf (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
      (b.hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X) R
          P Q p q k h U x y) =
      (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u}
        (ProEt.topology X) R Q P q p k ((add_comm q p).trans h) U y x :=
    (pullbackTensorSignedTotal_existsUnique (ProEt.topology X) R P Q).exists.choose_spec
      p q k h U x y
  apply hi
  rw [map_smul, hf, hf,
    tensorGenerator_smul_left (J := ProEt.topology X) (R := R)]
  exact smul_comm _ _ _

private theorem reduction_section_smul
    (n : ℕ) (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj U) (x : M.val.obj U) :
    unrestrictedIntegralTensorSection l E X n M U a x =
      a • unrestrictedIntegralTensorSection l E X n M U 1 x := by
  exact identifiedSection_smul (completedIntegralCommRingProjectionUnrestricted l E X n)
    (unrestrictedIntegralReductionFunctor l E X n)
    ((unrestrictedIntegralReductionExistence l E X n).choose_spec.choose) M U a x

private theorem reduction_generator_zsmul
    (n : ℕ) (M : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
    (a : (integralCoefficientCommRingSheaf l E X n).obj.obj U) (c : ℤ)
    (x : M.val.obj U) :
    IntegralOnSlice.generator l E X none n M U a (c • x) =
      c • IntegralOnSlice.generator l E X none n M U a x := by
  let φ := completedIntegralCommRingProjectionUnrestricted l E X n
  let e := (eqToHom (IntegralOnSlice.reduction_obj l E X none n M).symm).val.app U
  change e (SheafOfModules.UnrestrictedTowerProof.tensorSection φ M U a (c • x)) =
    c • e (SheafOfModules.UnrestrictedTowerProof.tensorSection φ M U a x)
  exact (congrArg e ((extensionSectionAdd φ M U a).map_zsmul c x)).trans
    (map_zsmul e.hom _ _)

end Helpers

attribute [local implicit_reducible] IntegralOnSlice.Site IntegralOnSlice.topology
  IntegralOnSlice.ring IntegralOnSlice.finite IntegralOnSlice.restrict
  integralCoefficientSheaf

attribute [local irreducible] IntegralAmbient.tensorTowerIso
  completedIntegralCommRingSheafUnrestricted coefficientTensorGenerator
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  coefficientSequenceCommRingSystem coefficientSequenceTopology

-- The generator comparison unfolds the sheafified tensor tower at every level.
/-- At one finite quotient, scalar extension of a signed chain map agrees with
interchange of the two quotient tensor factors. This assertion concerns only
finite quotient complexes, without a mapping fibre or derived localization.

Source: Stacks 03EL, 06YL and 07A4; blueprint signed transposition paragraph.
(blueprint: lem-coef-rational-verdier-tensor-tower-signed-coordinate).

Proof: the normalized balanced-tensor comparison sends the quotient generator
of a homogeneous tensor x tensor y with coefficient a to (a tensor x) tensor
(1 tensor y). The coherent signed swap interchanges these factors and multiplies
by (-1)^(ij). Moving the degree-zero coefficient a between the two factors by
balancedness gives exactly the image of the signed ordinary generator. The two
maps agree on all such generators; sheafification and the direct-sum summand
inclusions detect equality. This also applies to zero sections and an empty site. -/
theorem tensor_tower_signed_coordinate
    (P Q : CochainComplex (integralTowerModules l E X) ℤ)
    (s : (constructibleTensorTotal l E X).obj (P, Q) ⟶
      (constructibleTensorTotal l E X).obj (Q, P))
    (hs : ∀ (i j : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
      (s.f (i + j)).val.app U (IntegralHom.totalPair.{u, u}
        X (completedIntegralCommRingSheafUnrestricted l E X) P Q i j U x y) =
        (i * j).negOnePow •
          (eqToHom (congrArg
            (fun k : ℤ ↦ ((constructibleTensorTotal l E X).obj (Q, P)).X k)
              (add_comm j i))).val.app U
            (IntegralHom.totalPair.{u, u} X
              (completedIntegralCommRingSheafUnrestricted l E X) Q P j i U y x))
    (n : ℕ) :
    ((IntegralOnSlice.tower l E X none).map s).app (op n) ≫
        ((IntegralAmbient.tensorTowerIso l E X).hom.app (Q, P)).app (op n) =
      ((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)).app (op n) ≫
        (strictTensorSignedSwap l E X P Q).app (op n) := by
  have hs' (p q : ℤ) (U : X.ProEtᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
      (s.f (p + q)).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
          (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q) rfl U x y) =
        (p * q).negOnePow •
          coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) Q P q p (p + q)
            (add_comm q p) U y x := by
    rw [generator_transport, generator_transport]
    simp only [eqToHom_refl, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply]
    with_unfolding_all exact hs p q U x y
  rw [strict_signed_level l E X P Q n]
  apply HomologicalComplex.hom_ext
  intro k
  apply IntegralAmbient.tensorLevel_hom_ext l E X P Q n k
  intro p q hpq U a x y
  subst k
  let fp := (unrestrictedIntegralFiniteComplex l E X n).obj P
  let fq := (unrestrictedIntegralFiniteComplex l E X n).obj Q
  let b := (pullbackTensorSignedTotal (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) fp fq).hom
  change ((((IntegralAmbient.tensorTowerIso l E X).hom.app (Q, P)).app
      (op n)).f (p + q)).val.app U
      (((IntegralOnSlice.reduction l E X none n).map (s.f (p + q))).val.app U
        (IntegralOnSlice.generator l E X none n _ U a
          (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q)
            rfl U x y))) =
    (b.f (p + q)).val.app U
      (((((IntegralAmbient.tensorTowerIso l E X).hom.app (P, Q)).app
        (op n)).f (p + q)).val.app U
          (IntegralOnSlice.generator l E X none n _ U a
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (completedIntegralCommRingSheafUnrestricted l E X) P Q p q (p + q)
              rfl U x y)))
  erw [IntegralOnSlice.generator_map]
  erw [hs']
  simp only [Units.smul_def]
  erw [reduction_generator_zsmul]
  erw [map_zsmul]
  erw [tower_normalization, tower_normalization]
  have hb := (pullbackTensorSignedTotal_existsUnique (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) fp fq).exists.choose_spec
      p q (p + q) rfl U
        (unrestrictedIntegralTensorSection l E X n (P.X p) U a x)
        (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y)
  change (b.f (p + q)).val.app U _ = _ at hb
  rw [hb]
  simp only [Units.smul_def]
  congr 1
  erw [reduction_section_smul l E X n (Q.X q) U a y,
    reduction_section_smul l E X n (P.X p) U a x]
  exact (tensorGenerator_smul_left (J := ProEt.topology X)
    (R := integralCoefficientCommRingSheaf l E X n) fq fp q p (p + q) (add_comm q p) U a
      (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y)
      (unrestrictedIntegralTensorSection l E X n (P.X p) U 1 x)).trans
    (tensorGenerator_smul_right X (integralCoefficientCommRingSheaf l E X n)
      fq fp q p (p + q) (add_comm q p) U a
      (unrestrictedIntegralTensorSection l E X n (Q.X q) U 1 y)
      (unrestrictedIntegralTensorSection l E X n (P.X p) U 1 x)).symm

end WeilConjectures.RationalVerdier
