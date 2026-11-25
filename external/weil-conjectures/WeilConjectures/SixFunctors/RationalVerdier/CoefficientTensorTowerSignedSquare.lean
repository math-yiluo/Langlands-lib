/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
public import WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import all WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Finite.FinitePullbackTensorBraiding
import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality

/-! # Signed braiding and the coherent strict tensor tower

Source: Stacks 07A4 and 0941.
(blueprint: lem-coef-tensor-tower-signed-square). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.RationalVerdier
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

section Helpers
attribute [local implicit_reducible] sheafCompose
  integralCoefficientCommRingSheaf
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

private theorem ab_eqToHom_zsmul {A B : AddCommGrpCat.{u + 1}} (h : A = B)
    (a : ℤ) (x : A) : (eqToHom h) (a • x) = a • (eqToHom h) x := by
  subst B
  rfl

private theorem evaluationSection_zsmul
    (M : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : ℤ) (x : M.val.obj (op (n, U.unop))) :
    coefficientEvaluationSection l E X M n U (a • x) =
      a • coefficientEvaluationSection l E X M n U x := by
  unfold coefficientEvaluationSection
  apply ab_eqToHom_zsmul

private theorem signedTotal_generator
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u + 1}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
    (R : Sheaf J CommRingCat.{u + 1})
    (P Q : CochainComplex (SheafOfModules.{u + 1}
      ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)) ℤ)
    (p q k : ℤ) (h : p + q = k) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    ((pullbackTensorSignedTotal J R P Q).hom.f k).val.app U
        (coefficientTensorGenerator.{u, u + 1, u} J R P Q p q k h U x y) =
      (p * q).negOnePow • coefficientTensorGenerator.{u, u + 1, u} J R Q P q p k
        ((add_comm q p).trans h) U y x :=
  (pullbackTensorSignedTotal_existsUnique J R P Q).exists.choose_spec p q k h U x y

private theorem evaluation_signed_section
    (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
    (p q k : ℤ) (hpq : p + q = k) (U : X.ProEtᵒᵖ)
    (x : (P.X p).val.obj (op (n, U.unop)))
    (y : (Q.X q).val.obj (op (n, U.unop))) :
    ((coefficientEvaluationTensorIso l E X n Q P).hom.f k).val.app U
        (coefficientEvaluationSection l E X _ n U
          (((pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
            (coefficientSequenceCommRingSheaf l E X) P Q).hom.f k).val.app
              (op (n, U.unop))
                (coefficientTensorGenerator.{u, u + 1, u}
                  (coefficientSequenceTopology (ProEt.topology X))
                  (coefficientSequenceCommRingSheaf l E X) P Q p q k hpq
                  (op (n, U.unop)) x y))) =
      ((pullbackTensorSignedTotal (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X n)
        (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P)
        (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj Q)).hom.f
          k).val.app U
            (coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
              (integralCoefficientCommRingSheaf l E X n)
              (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P)
              (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj Q)
              p q k hpq U (coefficientEvaluationSection l E X (P.X p) n U x)
                (coefficientEvaluationSection l E X (Q.X q) n U y)) := by
  rw [signedTotal_generator]
  simp only [Units.smul_def]
  rw [evaluationSection_zsmul]
  erw [map_zsmul]
  erw [pullbackTensorEvaluationTensor_generator_cast]
  simpa only [Units.smul_def] using (signedTotal_generator (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) _ _ p q k hpq U _ _).symm

-- Keep coefficient-site transport abstract during the pure-section calculation.
private theorem evaluation_signed
    (n : ℕ) (P Q : CochainComplex (coefficientSequenceModules l E X) ℤ) :
    ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).map
        (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) P Q).hom ≫
        (coefficientEvaluationTensorIso l E X n Q P).hom =
      (coefficientEvaluationTensorIso l E X n P Q).hom ≫
        (pullbackTensorSignedTotal (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P)
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj Q)).hom := by
  let e := coefficientEvaluationTensorIso l E X n P Q
  apply e.inv_comp_eq.mp
  apply HomologicalComplex.hom_ext
  intro k
  apply CategoryTheory.ScalarHomTensor.total_pure_hom_ext.{u + 1, u, u}
    (J := ProEt.topology X) (R := integralCoefficientCommRingSheaf l E X n)
    (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj P)
    (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj Q) k _
  intro p q hpq U x y
  obtain ⟨x0, rfl⟩ := evaluationSection_surjective l E X (P.X p) n U x
  obtain ⟨y0, rfl⟩ := evaluationSection_surjective l E X (Q.X q) n U y
  have hn := pullbackTensorEvaluationTensor_generator_cast l E X n P Q p q k hpq U x0 y0
  have hi := cochainIso_inv_section e k U _ _ hn
  change ((coefficientEvaluationTensorIso l E X n Q P).hom.f k).val.app U
      (((coefficientSequenceEvaluation l E X n).map
        ((pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) P Q).hom.f k)).val.app U
        ((e.inv.f k).val.app U _)) = _
  erw [hi, evaluationSection_map]
  exact evaluation_signed_section l E X n P Q p q k hpq U x0 y0

private theorem signed_natural
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P P' Q Q' : CochainComplex (IntegralHom.Modules.{u, u} X R) ℤ}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R).map
        (Prod.mkHom a b) ≫ (pullbackTensorSignedTotal (ProEt.topology X) R P' Q').hom =
      (pullbackTensorSignedTotal (ProEt.topology X) R P Q).hom ≫
        (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X) R).map
          (Prod.mkHom b a) := by
  rw [pullbackTensorSignedTotal_eq, pullbackTensorSignedTotal_eq]
  exact (pullbackTensorNativeIso (ProEt.topology X) R).hom.naturality (Prod.mkHom a b)

private theorem map_paste
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {A A' B B' C₀ C₀' : C} {Z Z' : D}
    (r : Z ⟶ F.obj A) (r' : Z' ⟶ F.obj A') (f : Z ⟶ Z')
    (a : A ⟶ A') (e : A ⟶ B) (e' : A' ⟶ B')
    (t : B ⟶ C₀) (t' : B' ⟶ C₀') (b : C₀ ⟶ C₀')
    (hr : f ≫ r' = r ≫ F.map a) (he : a ≫ e' ≫ t' = e ≫ t ≫ b) :
    f ≫ r' ≫ F.map e' ≫ F.map t' =
      r ≫ F.map e ≫ F.map t ≫ F.map b := by
  rw [← Category.assoc f, hr]
  simp only [Category.assoc]
  rw [← F.map_comp, ← F.map_comp, he]
  simp only [F.map_comp]

private theorem compose_squares
    {C : Type*} [Category* C] {A A' B B' D D' : C}
    (f : A ⟶ A') (e : A ⟶ B) (e' : A' ⟶ B')
    (g : B ⟶ B') (t : B ⟶ D) (t' : B' ⟶ D') (h : D ⟶ D')
    (he : f ≫ e' = e ≫ g) (ht : t ≫ h = g ≫ t') :
    f ≫ e' ≫ t' = e ≫ t ≫ h := by
  rw [← Category.assoc, he, Category.assoc, ← ht]

private theorem restrictedLevel_natural
    (C D : CochainComplex (coefficientSequenceModules l E X) ℤ) (b : C ⟶ D) (n : ℕ) :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)).app
        (op n) ≫ (pullbackTensorRestrictedLevel l E X D n).hom =
      (pullbackTensorRestrictedLevel l E X C n).hom ≫
        ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
          (((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).map b) := by
  apply HomologicalComplex.hom_ext
  intro k
  unfold pullbackTensorRestrictedLevel
  dsimp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex, Iso.app, Iso.trans, Iso.symm, Iso.refl,
    HomologicalComplex.comp_f, NatTrans.comp_app, NatTrans.id_app]
  change ((coefficientSequenceRestriction l E X).map (b.f k)).app (op n) ≫
      (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
        ((D).X k) =
    (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.app
        ((C).X k) ≫
      (scalarReductionRestriction l E X n).map
        ((coefficientSequenceEvaluation l E X n).map (b.f k))
  exact (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom.naturality (b.f k)

private theorem tensorTowerLevel_def
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) :
    pullbackTensorTensorTowerLevel l E X P Q n =
      pullbackTensorRestrictedLevel l E X _ n ≪≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
        (coefficientEvaluationTensorIso l E X n _ _) ≪≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).mapIso
        ((coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n)).mapIso
            (Iso.prod ((pullbackTensorReductionEvaluationComplex l E X n).app P).symm
              ((pullbackTensorReductionEvaluationComplex l E X n).app Q).symm)) := by
  unfold pullbackTensorTensorTowerLevel
  rfl

-- Assemble the three finite comparison squares without unfolding their choices.
/-- Coherent signed total interchange commutes with the prescribed strict tower comparison.
Source: Stacks 07A4 and 0941
(blueprint: lem-coef-tensor-tower-signed-square).
Proof: the evaluation comparison sends each homogeneous pure tensor to the tensor
of its evaluated sections. Its square with the signed swap follows from this
formula and the Koszul formula, since evaluation preserves integer multiplication.
The inverse reduction-evaluation maps commute with braiding by naturality. Paste
these two squares with restriction-evaluation naturality and use the prescribed
finite component of the strict tower comparison. This works for every unbounded
complex and does not use flatness or completion. -/
theorem coefficientTensorTower_signed_square
    (P Q : CochainComplex (integralTowerModules l E X) ℤ) (n : ℕ) :
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
      (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map
        (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj P)
          (((pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)).obj Q)).hom)).app
            (op n) ≫ (pullbackTensorTensorTower l E X Q P).hom.app (op n) =
      (pullbackTensorTensorTower l E X P Q).hom.app (op n) ≫
        ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
          (pullbackTensorSignedTotal (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X n)
            ((unrestrictedIntegralFiniteComplex l E X n).obj P)
            ((unrestrictedIntegralFiniteComplex l E X n).obj Q)).hom := by
  let G := (pullbackTensorOrdinaryReduction l E X).mapHomologicalComplex (.up ℤ)
  let V := (coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)
  let S := (scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)
  let B := coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
  let T := coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
  let b := (pullbackTensorSignedTotal (coefficientSequenceTopology (ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X) (G.obj P) (G.obj Q)).hom
  let c := (pullbackTensorSignedTotal (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n) (V.obj (G.obj P)) (V.obj (G.obj Q))).hom
  let d := (pullbackTensorSignedTotal (ProEt.topology X)
    (integralCoefficientCommRingSheaf l E X n)
    ((unrestrictedIntegralFiniteComplex l E X n).obj P)
    ((unrestrictedIntegralFiniteComplex l E X n).obj Q)).hom
  let aP := (pullbackTensorReductionEvaluationComplex l E X n).inv.app P
  let aQ := (pullbackTensorReductionEvaluationComplex l E X n).inv.app Q
  have h := evaluation_signed l E X n (G.obj P) (G.obj Q)
  have h' := signed_natural X (integralCoefficientCommRingSheaf l E X n) aP aQ
  change T.map (Prod.mkHom aP aQ) ≫ d = c ≫ T.map (Prod.mkHom aQ aP) at h'
  have h'' := compose_squares (V.map b) _ _ c _ _ d h h'
  have hr := restrictedLevel_natural l E X _ _ b n
  have hpaste := map_paste S _ _ _ _ _ _ _ _ _ hr h''
  have hcomp :
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)).app
          (op n) ≫ (pullbackTensorTensorTowerLevel l E X Q P n).hom =
      (pullbackTensorTensorTowerLevel l E X P Q n).hom ≫ S.map d := by
    -- Keep the chosen comparisons folded during kernel checking.
    rw [tensorTowerLevel_def, tensorTowerLevel_def]
    dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    change _ ≫ (pullbackTensorRestrictedLevel l E X (B.obj (G.obj Q, G.obj P)) n).hom ≫
      S.map (coefficientEvaluationTensorIso l E X n (G.obj Q) (G.obj P)).hom ≫
      S.map (T.map (Prod.mkHom aQ aP)) =
      (pullbackTensorRestrictedLevel l E X (B.obj (G.obj P, G.obj Q)) n).hom ≫
        S.map (coefficientEvaluationTensorIso l E X n (G.obj P) (G.obj Q)).hom ≫
        S.map (T.map (Prod.mkHom aP aQ)) ≫ S.map d
    exact hpaste
  have hlevel := congrArg Iso.hom (pullbackTensorTensorTower_app l E X P Q n)
  have hlevel' := congrArg Iso.hom (pullbackTensorTensorTower_app l E X Q P n)
  have hcomp' :
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).map b)).app
          (op n) ≫ (pullbackTensorTensorTower l E X Q P).hom.app (op n) =
      (pullbackTensorTensorTower l E X P Q).hom.app (op n) ≫ S.map d :=
    (congrArg (fun f ↦ _ ≫ f) hlevel').trans (hcomp.trans
      (congrArg (fun f ↦ f ≫ S.map d) hlevel.symm))
  exact hcomp'

end Helpers
end WeilConjectures.RationalVerdier
