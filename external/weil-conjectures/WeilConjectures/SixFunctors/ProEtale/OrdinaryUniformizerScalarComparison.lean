/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.InternalQuotientTowerModel
import all WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
import all WeilConjectures.AlgebraicGeometry.AdmissibleScalarRealizationExact
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.SixFunctors.ProEtale.InternalDiscreteQuotientComparison
import all WeilConjectures.SixFunctors.ProEtale.InternalFirstResidueRingIso

/-! # The ordinary uniformizer action under the constant coefficient comparison

Source: integral-models proof (1), constant coefficient comparison; Stacks Project,
algebraization.tex, Lemma derived-completion-koszul (0A0E), rank-one scalar action.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj TensorProduct

-- Live's `InternalSectionTensorComparison` made these global; the port keeps them local there.
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
namespace AlgebraicGeometry.ProEtale.InternalCompletionTransport
open IntegralModelsStacks
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

local instance ordinaryModulesMonoidal :
    MonoidalCategory (ConstantCompletion.Mod (ring l E X)) :=
  SheafOfModules.monoidalCategory (ring l E X)

attribute [local irreducible] IntegralConstantModel.pointComparison upperStarFromPoint
  Padic.coefficientExtensionAbsoluteValue spectralNorm

section ScalarAction
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [UnivLE.{max v w, u}] [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]
    (R : Sheaf J AddCommGrpCat.{u}) [MonObj R] [IsCommMonObj R]

private theorem internal_leftUnitor_inv
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) :
    (λ_ M).inv.hom = (λ_ M.X).inv ≫ (MonObj.one : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ R) ▷ M.X ≫
      Mod.tensorObjπ (Mod.regular R) M := by
  apply (cancel_mono (λ_ M).hom.hom).1
  rw [← Mod.comp_hom', Iso.inv_hom_id, Mod.id_hom']
  have hπ := InternalAbelianSheafModule.comparison_internal_leftUnitorπ J R M
  change Mod.tensorObjπ (Mod.regular R) M ≫ (λ_ M).hom.hom =
    Mod.act (A := R) M.X at hπ
  rw [Category.assoc, Category.assoc, hπ, Mod.one_act, Iso.inv_hom_id]

private theorem internal_scalar_underlying
    (d : End (Mod.regular R)) (M : Mod (Sheaf J AddCommGrpCat.{u}) R) :
    ((λ_ M).inv ≫ d.asHom ▷ M ≫ (λ_ M).hom).hom =
      (λ_ M.X).inv ≫ ((MonObj.one : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ R) ≫
        d.asHom.hom) ▷ M.X ≫ Mod.act (A := R) M.X := by
  simp only [Mod.comp_hom', internal_leftUnitor_inv J R, Category.assoc]
  have hπ := InternalAbelianSheafModule.comparison_internal_leftUnitorπ J R M
  change Mod.tensorObjπ (Mod.regular R) M ≫ (λ_ M).hom.hom =
    Mod.act (A := R) M.X at hπ
  rw [Mod.tensorObjπ_whiskerRight_assoc, hπ]
  simp only [comp_whiskerRight, Category.assoc]

private theorem internal_action_sections
    (c : 𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ R)
    (M : Mod (Sheaf J AddCommGrpCat.{u}) R) (U : Cᵒᵖ) (m : M.X.obj.obj U) :
    (((λ_ M.X).inv ≫ c ▷ M.X ≫ Mod.act (A := R) M.X).hom.app U) m =
      (show ((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M).val.obj U from
        (show (InternalAbelianSheafModule.sectionRingSheaf J R).obj.obj U from
          ((Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫ c.hom).app U)
            (ULift.up 1)) •
          (show ((InternalAbelianSheafModule.sectionModuleFunctor J R).obj M).val.obj U
            from m)) := by
  let I := sheafToPresheaf J AddCommGrpCat.{u}
  have h :
      I.map ((λ_ M.X).inv ≫ c ▷ M.X ≫ Mod.act (A := R) M.X) =
        (λ_ (I.obj M.X)).inv ≫
          (Functor.LaxMonoidal.ε I ≫ I.map c) ▷ I.obj M.X ≫
          Functor.LaxMonoidal.μ I R M.X ≫ I.map (Mod.act (A := R) M.X) := by
    simp only [Functor.map_comp]
    rw [← Functor.LaxMonoidal.left_unitality_inv]
    simp only [Category.assoc, comp_whiskerRight]
    rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  have hh := congrArg (fun k ↦ (k.app U).hom m) h
  have hunit : ((λ_ (I.obj M.X)).inv.app U).hom m =
      (ULift.up 1) ⊗ₜ[ℤ] m := by rfl
  simp only [NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply, hunit] at hh
  exact hh

end ScalarAction

section ConstantElement
universe v w
variable {C : Type v} [Category.{w} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{u}]
    [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

private def coefficientVector {A : AddCommGrpCat.{u}} (a : A) :
    𝟙_ AddCommGrpCat.{u} ⟶ A :=
  AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.down • a
      map_zero' := zero_zsmul a
      map_add' := fun z w ↦ add_zsmul a z.down w.down }

private def constantElement {A : AddCommGrpCat.{u}} (a : A) :
    𝟙_ (Sheaf J AddCommGrpCat.{u}) ⟶ (constantSheaf J AddCommGrpCat.{u}).obj A :=
  Functor.LaxMonoidal.ε (constantSheaf J AddCommGrpCat.{u}) ≫
    (constantSheaf J AddCommGrpCat.{u}).map (coefficientVector a)

private theorem constantElement_fac {A : AddCommGrpCat.{u}} (a : A) :
    Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
      (constantElement J a).hom =
    (Functor.const Cᵒᵖ).map (coefficientVector a) ≫
      toSheafify J ((Functor.const Cᵒᵖ).obj A) := by
  have hc : Functor.LaxMonoidal.ε
      (Functor.const Cᵒᵖ : AddCommGrpCat.{u} ⥤ _) = 𝟙 _ := by
    ext U
    rfl
  change _ ≫ ((Functor.LaxMonoidal.ε (presheafToSheaf J AddCommGrpCat.{u}) ≫
      (presheafToSheaf J AddCommGrpCat.{u}).map
        (Functor.LaxMonoidal.ε (Functor.const Cᵒᵖ))) ≫
      (presheafToSheaf J AddCommGrpCat.{u}).map
        ((Functor.const Cᵒᵖ).map (coefficientVector a))).hom = _
  rw [hc, CategoryTheory.Functor.map_id, Category.comp_id]
  change _ ≫ (sheafToPresheaf J AddCommGrpCat.{u}).map (_ ≫ _) = _
  have hε : Functor.LaxMonoidal.ε (sheafToPresheaf J AddCommGrpCat.{u}) ≫
      (sheafToPresheaf J AddCommGrpCat.{u}).map
        (Functor.LaxMonoidal.ε (presheafToSheaf J AddCommGrpCat.{u})) =
      (sheafificationAdjunction J AddCommGrpCat.{u}).unit.app _ := by
    rw [← (sheafificationAdjunction J AddCommGrpCat.{u}).unit_app_unit_comp_map_η,
      Category.assoc, ← CategoryTheory.Functor.map_comp,
      Functor.Monoidal.η_ε, CategoryTheory.Functor.map_id]
    rfl
  rw [CategoryTheory.Functor.map_comp, ← Category.assoc, hε]
  exact (toSheafify_naturality (J := J)
    ((Functor.const Cᵒᵖ).map (coefficientVector a))).symm

end ConstantElement

private theorem ab_unit_hom_ext {A : AddCommGrpCat.{u}}
    {f g : 𝟙_ AddCommGrpCat.{u} ⟶ A}
    (h : f.hom (ULift.up 1) = g.hom (ULift.up 1)) : f = g := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  have hz : z = z.down • (ULift.up 1 : ULift.{u} ℤ) := by
    apply ULift.ext
    simp
  rw [hz, map_zsmul, map_zsmul]
  exact congrArg (fun x : A ↦ z.down • x) h

-- Specify the raw ring instance directly: searching for it unfolds sheafification.
private theorem point_scalar_section (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (a : A)
    (d : Profinite.continuousCoefficientRingObj A ⟶ Profinite.continuousCoefficientRingObj A)
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (b : (Profinite.continuousCoefficientRingObj A).obj.obj S)
      (s : S.unop), ((d.hom.app S) b).down s = a * b.down s) :
    constantElement (coherentTopology Profinite.{u})
        (show AddCommGrpCat.of (ULift.{u + 1} A) from ULift.up a) ≫
      (pointIso A).hom ≫ constantContinuousMap A =
        (MonObj.one : 𝟙_ _ ⟶ Profinite.continuousCoefficientRingObj A) ≫ d := by
  change constantElement (coherentTopology Profinite.{u})
      (show AddCommGrpCat.of (ULift.{u + 1} A) from ULift.up a) ≫
      ((pointConstantAbIso A).hom ≫
        (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (constantToContinuous A)) = _
  rw [pointConstantAbIso_scalar]
  apply Sheaf.unit_hom_ext
  change Functor.LaxMonoidal.ε
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      ((constantElement (coherentTopology Profinite.{u})
        (show AddCommGrpCat.of (ULift.{u + 1} A) from ULift.up a)).hom ≫
          (FiniteConstantModel.scalarToContinuous A).hom) =
    Functor.LaxMonoidal.ε
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
      ((MonObj.one : 𝟙_ _ ⟶ Profinite.continuousCoefficientRingObj A).hom ≫ d.hom)
  rw [← Category.assoc, constantElement_fac, Category.assoc]
  have hscalar := ((sheafificationAdjunction (coherentTopology Profinite.{u})
      Ab.{u + 1}).homEquiv _ (Profinite.continuousCoefficientRingObj A)).apply_symm_apply
        (FiniteConstantModel.constantFunctions A)
  rw [Adjunction.homEquiv_unit] at hscalar
  change toSheafify (coherentTopology Profinite.{u}) _ ≫
    (FiniteConstantModel.scalarToContinuous A).hom = _ at hscalar
  rw [hscalar, ← Category.assoc]
  let : MonObj (Profinite.continuousCoefficientRingObj A).obj :=
    (Profinite.continuousCoefficientRingPresheaf A).monObjCompForget₂
  have hunit : Functor.LaxMonoidal.ε
      (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) ≫
        (MonObj.one : 𝟙_ _ ⟶ Profinite.continuousCoefficientRingObj A).hom =
      (MonObj.one : 𝟙_ _ ⟶ (Profinite.continuousCoefficientRingObj A).obj) :=
    Sheaf.ε_comp_map_one (Profinite.continuousCoefficientRingObj A)
  rw [hunit]
  apply NatTrans.ext
  funext S
  apply ab_unit_hom_ext
  apply ULift.ext
  apply ContinuousMap.ext
  intro s
  simp only [NatTrans.comp_app, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply]
  erw [hd]
  simp only [Functor.const_map_app]
  have hvec :
      (coefficientVector (show AddCommGrpCat.of (ULift.{u + 1} A) from ULift.up a)).hom
        (ULift.up 1) = (ULift.up a : ULift.{u + 1} A) := one_zsmul _
  erw [hvec]
  have hone : ((MonObj.one : 𝟙_ _ ⟶
      (Profinite.continuousCoefficientRingObj A).obj).app S).hom (ULift.up 1) =
      (1 : ULift.{u + 1} C(S.unop, A)) := by
    change ((1 : ℤ) : ULift.{u + 1} C(S.unop, A)) = 1
    exact Int.cast_one
  erw [hone]
  change a = a * 1
  exact (mul_one a).symm

private theorem point_uniformizer_section
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
        Padic.coefficientExtensionUniformizer l E * b.down s) :
    constantElement (coherentTopology Profinite.{u})
        (show AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
          from ULift.up (Padic.coefficientExtensionUniformizer l E)) ≫
      (pointIso (Padic.coefficientExtensionIntegers l E)).hom ≫
      scalarPointMap l E ≫ (IntegralConstantModel.pointComparison l E).inv.hom =
        (MonObj.one : 𝟙_ _ ⟶ DerivedNakayama.integerRing l E) ≫ d.asHom.hom := by
  rw [scalarPointMap_absolute]
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact point_scalar_section (Padic.coefficientExtensionIntegers l E)
    (Padic.coefficientExtensionUniformizer l E) d.asHom.hom hd

private theorem scheme_constantElement (A : Type u) [CommRing A]
    (a : AddCommGrpCat.of (ULift.{u + 1} A)) :
    constantElement (Scheme.ProEt.topology X) a ≫ (schemeIso X A).hom =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map
          (constantElement (coherentTopology Profinite.{u}) a ≫ (pointIso A).hom) := by
  dsimp only [constantElement, schemeIso, Iso.trans_hom, Iso.app_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [(constantSchemeIso X).hom.naturality_assoc]
  rw [← Category.assoc,
    NatTrans.IsMonoidal.unit (τ := (constantSchemeIso X).hom)]
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map,
    CategoryTheory.Functor.map_comp, Category.assoc]

attribute [local irreducible] IntegralModelsStacks.schemeIso

private theorem canonical_quotient_comparison (A : Type u) [CommRing A]
    (I : Ideal A) :
    let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
    let B := ULift.{u + 1} A
    let K : Ideal B := Ideal.map
      (ULift.ringEquiv : B ≃+* A).symm.toRingHom I
    ∃ f : ConstantCompletion.finite J B K 0 ≅
        smallRing X (condensedRingObj (discreteObj (A ⧸ I)) X),
      ConstantCompletion.quotient J B K 0 ≫ f.hom =
        (smallIso X A).hom ≫ smallMap X
          ((upperStarFromPoint X).map (discreteMap (Ideal.Quotient.mk I))) := by
  dsimp only
  let J := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let B := ULift.{u + 1} A
  let K : Ideal B := Ideal.map (ULift.ringEquiv : B ≃+* A).symm.toRingHom I
  let q : (A ⧸ I) ≃+* (B ⧸ K) :=
    Ideal.quotientEquiv I K (ULift.ringEquiv : B ≃+* A).symm rfl
  let t : (B ⧸ K ^ (0 + 1)) ≃+* ULift.{u + 1} (A ⧸ I) :=
    (Ideal.quotientEquiv _ K (RingEquiv.refl B) (by simp)).trans
      (q.symm.trans ULift.ringEquiv.symm)
  let f := (constantSheaf J CommRingCat.{u + 1}).mapIso t.toCommRingCatIso ≪≫
    smallIso X (A ⧸ I)
  refine ⟨f, ?_⟩
  change (constantSheaf J CommRingCat.{u + 1}).map
      (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (0 + 1)))) ≫
      ((constantSheaf J CommRingCat.{u + 1}).map t.toCommRingCatIso.hom ≫ _) = _
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  have ht : (CommRingCat.ofHom (Ideal.Quotient.mk (K ^ (0 + 1)))) ≫
      t.toCommRingCatIso.hom =
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    change t (Ideal.Quotient.mk _ b) = _
    change ULift.up (q.symm ((Ideal.quotientEquiv _ K (RingEquiv.refl B) (by simp))
      (Ideal.Quotient.mk _ b))) = _
    rw [Ideal.quotientEquiv_mk, Ideal.quotientEquiv_symm_mk]
    rfl
  rw [ht]
  exact smallIso_naturality X (Ideal.Quotient.mk I)

private theorem smallConstantIso_terminal (B : CommRingCat.{u + 1}) :
    (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ).obj B)).app
          (op (AsSmall.up.obj (proEtTerminal X))) ≫
      ((smallConstantIso X).hom.app B).hom.app
        (op (AsSmall.up.obj (proEtTerminal X))) =
      (toSheafify (Scheme.ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj B)).app (op (proEtTerminal X)) := by
  let e := AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)
  let J := Scheme.ProEt.topology X
  let K := Scheme.coefficientProEtaleModelTopology.{u, u} X
  let hT := proEtIsTerminal (proEtTerminal X)
  have : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
      X.ProEt).IsEquivalence := e.isEquivalence_inverse
  have : e.inverse.IsDenseSubsite K J := by
    change Functor.IsDenseSubsite
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
        X.ProEt).inducedTopology J) J AsSmall.down
    infer_instance
  let q := e.sheafCongr J K CommRingCat.{u + 1}
  let i : q.inverse ⋙ (sheafSections J CommRingCat.{u + 1}).obj (op (proEtTerminal X)) ≅
      (sheafSections K CommRingCat.{u + 1}).obj
        (op (e.functor.obj (proEtTerminal X))) :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
      dsimp
      rw [Category.comp_id, Category.id_comp]
      rfl)
  let a₁ := ((constantSheafAdj J CommRingCat.{u + 1} hT).comp q.toAdjunction).ofNatIsoRight i
  let a₂ := constantSheafAdj K CommRingCat.{u + 1} (hT.isTerminalObj e.functor)
  have h := Adjunction.unit_leftAdjointUniq_hom_app a₂ a₁ B
  change _ ≫ ((smallConstantIso X).hom.app B).hom.app
    (op (AsSmall.up.obj (proEtTerminal X))) = _ at h
  dsimp only [a₁, a₂, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerRight_app, Adjunction.comp_unit_app, constantSheafAdj,
    constantPresheafAdj_unit_app, Category.id_comp, Category.comp_id] at h
  change (toSheafify K _).app (op (e.functor.obj (proEtTerminal X))) ≫
      ((smallConstantIso X).hom.app B).hom.app
        (op (AsSmall.up.obj (proEtTerminal X))) =
    ((toSheafify J _).app (op (proEtTerminal X)) ≫
      ((constantSheaf J CommRingCat.{u + 1}).obj B).obj.map
        (𝟙 (op (proEtTerminal X)))) ≫ 𝟙 _ at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id] at h
  exact h

private theorem smallConstantIso_fac (B : CommRingCat.{u + 1}) :
    toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ).obj B) ≫
      ((smallConstantIso X).hom.app B).hom =
      Functor.whiskerLeft
        (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op
        (toSheafify (Scheme.ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj B)) := by
  apply NatTrans.ext
  funext U
  let t := op (AsSmall.up.obj (proEtTerminal X))
  let f : t ⟶ U := (show U.unop ⟶ AsSmall.up.obj (proEtTerminal X) from
    ⟨(proEtIsTerminal (proEtTerminal X)).from
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).obj U.unop)⟩).op
  have hsmall := (toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
    ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ).obj B)).naturality f
  have hi := ((smallConstantIso X).hom.app B).hom.naturality f
  have hbig := (toSheafify (Scheme.ProEt.topology X)
    ((Functor.const X.ProEtᵒᵖ).obj B)).naturality
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.map f)
  dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at hsmall hbig
  erw [Category.id_comp] at hsmall hbig
  change _ ≫ _ = _
  erw [hsmall, Category.assoc, hi, ← Category.assoc, smallConstantIso_terminal]
  exact hbig.symm

private theorem smallIso_constant_section (A : Type u) [CommRing A]
    (a : ULift.{u + 1} A) (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) :
    (ConstantCompletion.algebraSection (smallIso X A).hom a).val U =
      (schemeIso X A).hom.hom.app
        ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.obj U)
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app
            ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
              X.ProEt).op.obj U) a) := by
  let := schemeIso_mon X A
  have h := ConcreteCategory.congr_hom
    (congr_app (smallConstantIso_fac X (CommRingCat.of (ULift.{u + 1} A))) U) a
  change (ringIso X A).hom.hom.app _
    (((smallConstantIso X).hom.app (CommRingCat.of (ULift.{u + 1} A))).hom.app U
      ((toSheafify (Scheme.coefficientProEtaleModelTopology.{u, u} X)
        ((Functor.const (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U a)) = _
  dsimp only [NatTrans.comp_app, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply] at h
  exact (congrArg (fun b ↦ (ringIso X A).hom.hom.app
    ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.obj U) b)
      h).trans (AdmissibleScalarRealization.constantRingMap_normalization A X _
        (schemeIso X A).hom _ a)

private theorem smallIso_section_element (A : Type u) [CommRing A]
    (a : ULift.{u + 1} A) (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) :
    (ConstantCompletion.algebraSection (smallIso X A).hom a).val U =
      ((Functor.LaxMonoidal.ε
        (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (constantElement (Scheme.ProEt.topology X)
          (show AddCommGrpCat.of (ULift.{u + 1} A) from a) ≫
          (schemeIso X A).hom).hom).app
            ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤
              X.ProEt).op.obj U)) (ULift.up 1) := by
  rw [smallIso_constant_section X A a U]
  change _ = ((Functor.LaxMonoidal.ε
      (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
        (constantElement (Scheme.ProEt.topology X)
          (show AddCommGrpCat.of (ULift.{u + 1} A) from a)).hom) ≫
          (schemeIso X A).hom.hom).app _ (ULift.up 1)
  rw [constantElement_fac]
  change _ = (schemeIso X A).hom.hom.app _
    ((toSheafify (Scheme.ProEt.topology X)
      ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))).app _
        ((1 : ℤ) • a))
  rw [one_zsmul]

private theorem scalarOnModules_underlying
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : AdicCompletion.Modules l E X) :
    ((DerivedNakayama.scalarOnModules l E X d).app M).hom =
      (λ_ M.X).inv ≫
        (Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
          (upperStarFromPoint X).map
            ((MonObj.one : 𝟙_ _ ⟶ DerivedNakayama.integerRing l E) ≫ d.asHom.hom)) ▷ M.X ≫
          Mod.act (A := condensedRingObj (DerivedNakayama.integerRing l E) X) M.X := by
  let dX : End (Mod.regular (condensedRingObj (DerivedNakayama.integerRing l E) X)) :=
    .of ((DerivedNakayama.regularPullbackIso l E X).inv ≫
      (DerivedNakayama.pullback l E X).map d.asHom ≫
        (DerivedNakayama.regularPullbackIso l E X).hom)
  have hX : dX.asHom.hom = (upperStarFromPoint X).map d.asHom.hom := by
    change 𝟙 _ ≫ (upperStarFromPoint X).map d.asHom.hom ≫ 𝟙 _ = _
    simp only [Category.id_comp, Category.comp_id]
  change ((λ_ M).inv ≫ dX.asHom ▷ M ≫ (λ_ M).hom).hom = _
  rw [internal_scalar_underlying (Scheme.ProEt.topology X)
    (condensedRingObj (DerivedNakayama.integerRing l E) X) dX M, hX]
  have hunit :
      (MonObj.one : 𝟙_ _ ⟶ condensedRingObj (DerivedNakayama.integerRing l E) X) =
      Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
        (upperStarFromPoint X).map
          (MonObj.one : 𝟙_ _ ⟶ DerivedNakayama.integerRing l E) := rfl
  rw [hunit, Category.assoc, ← CategoryTheory.Functor.map_comp]

section RestrictionAction
universe v w
variable {C : Type v} [Category.{w} C] [MonoidalCategory C]
    {R S T : C} [MonObj R] [MonObj S] [MonObj T]

private theorem restricted_action (φ : R ⟶ S) [IsMonHom φ]
    (ψ : S ⟶ T) [IsMonHom ψ] (c : 𝟙_ C ⟶ R) (b : 𝟙_ C ⟶ T)
    (h : c ≫ φ ≫ ψ = b) (M : Mod C T) :
    let N := (Mod.comap φ).obj ((Mod.comap ψ).obj M)
    (λ_ M.X).inv ≫ b ▷ M.X ≫ Mod.act (A := T) M.X =
      (λ_ N.X).inv ≫ c ▷ N.X ≫ @Mod.act _ _ _ R _ N.X N.mod := by
  dsimp only
  change (λ_ M.X).inv ≫ b ▷ M.X ≫ Mod.act (A := T) M.X =
    (λ_ M.X).inv ≫ c ▷ M.X ≫ φ ▷ M.X ≫ ψ ▷ M.X ≫ Mod.act (A := T) M.X
  rw [← h]
  simp only [comp_whiskerRight, Category.assoc]
end RestrictionAction

attribute [local irreducible] IntegralModelsStacks.scalarPointMap
  IntegralModelsStacks.scalarMap

private theorem uniformizer_section
    (d : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (hd : ∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
      (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
        Padic.coefficientExtensionUniformizer l E * b.down s) :
    (constantElement (Scheme.ProEt.topology X)
      (show AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        from ULift.up (Padic.coefficientExtensionUniformizer l E)) ≫
      (schemeIso X (Padic.coefficientExtensionIntegers l E)).hom) ≫
      scalarMap l E X ≫
        coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X =
    Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map
        ((MonObj.one : 𝟙_ _ ⟶ DerivedNakayama.integerRing l E) ≫ d.asHom.hom) := by
  rw [scheme_constantElement X]
  unfold IntegralModelsStacks.scalarMap coefficientMap
  simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k ↦ Functor.LaxMonoidal.ε (upperStarFromPoint X) ≫
      (upperStarFromPoint X).map k) (point_uniformizer_section l E d hd)

private local instance smallModulesSectionSMul
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ) :
    SMul (R.obj.obj
      ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.obj U))
      (((smallModules X R).obj N).val.obj U) :=
  inferInstanceAs (SMul ((smallRing X R).obj.obj U)
    (((smallModules X R).obj N).val.obj U))

private theorem smallModules_scalar_map
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R) (f : End N)
    (c : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R)
    (hf : f.asHom.hom = (λ_ N.X).inv ≫ c ▷ N.X ≫ @Mod.act _ _ _ R _ N.X N.mod)
    (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ)
    (m : ((smallModules X R).obj N).val.obj U) :
    ((smallModules X R).map f.asHom).val.app U m =
      (show (smallRing X R).obj.obj U from
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          c.hom).app
            ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.obj U))
              (ULift.up 1)) • m := by
  change f.asHom.hom.hom.app _ m = _
  rw [hf]
  exact internal_action_sections (Scheme.ProEt.topology X) R c N _ m

-- Keep the module-action calculation generic, before specializing the coefficient rings.
private theorem restricted_scalar_sections
    {R S T : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [MonObj T]
    (φ : R ⟶ S) [IsMonHom φ] (ψ : S ⟶ T) [IsMonHom ψ]
    (c : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ R)
    (b : 𝟙_ (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ⟶ T)
    (h : c ≫ φ ≫ ψ = b) (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) T)
    (f : End M)
    (hf : f.asHom.hom = (λ_ M.X).inv ≫ b ▷ M.X ≫ @Mod.act _ _ _ T _ M.X M.mod)
    (U : (Scheme.coefficientProEtaleSiteModel.{u, u} X)ᵒᵖ)
    (m : ((Mod.comap ψ ⋙ Mod.comap φ ⋙ smallModules X R).obj M).val.obj U) :
    ((Mod.comap ψ ⋙ Mod.comap φ ⋙ smallModules X R).map f.asHom).val.app U m =
      (show (smallRing X R).obj.obj U from
        ((Functor.LaxMonoidal.ε (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ≫
          c.hom).app
            ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).op.obj U))
              (ULift.up 1)) • m := by
  let N := (Mod.comap φ).obj ((Mod.comap ψ).obj M)
  exact smallModules_scalar_map X R N ((Mod.comap ψ ⋙ Mod.comap φ).mapEnd M f) c
    (hf.trans (restricted_action φ ψ c b h M)) U m

section OrdinaryScalar
universe v
variable {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{v})
local instance ordinaryUniformizerScalarComparisonInst1
    : MonoidalCategory (ConstantCompletion.Mod O) :=
  SheafOfModules.monoidalCategory O

private theorem ordinary_scalar_characterization (M : ConstantCompletion.Mod O)
    (s : (O.obj ⋙ forget CommRingCat).sections) (f : End M)
    (hf : ∀ (U : Cᵒᵖ) (m : M.val.obj U), f.asHom.val.app U m = s.val U • m) :
    f.asHom ≫ (ρ_ M).inv = (ρ_ M).inv ≫ M ◁ (ringedKoszulScalar O s).asHom := by
  apply (cancel_mono (ρ_ M).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let I := SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
  have hr (x : M.val.obj U) (a : O.obj.obj U) :
      (ρ_ M).hom.val.app U (CochainPullback.moduleTmul M I U x a) = a • x :=
    RingedDerivedNative.pureTensor_rightUnitor.{v, v, v} J O M U a x
  have hunit : (ρ_ M).inv.val.app U m =
      CochainPullback.moduleTmul M I U m (1 : O.obj.obj U) := by
    have h := congrArg (fun g ↦ g.val.app U
      (CochainPullback.moduleTmul M I U m (1 : O.obj.obj U))) (ρ_ M).hom_inv_id
    simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ModuleCat.comp_apply, SheafOfModules.id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] at h
    rw [hr, one_smul] at h
    exact h
  change f.asHom.val.app U m = (ρ_ M).hom.val.app U
    ((M ◁ (ringedKoszulScalar O s).asHom).val.app U ((ρ_ M).inv.val.app U m))
  rw [hunit]
  have hmap := CochainPullback.moduleTmul_map (𝟙 M) (ringedKoszulScalar O s).asHom
    U m (1 : O.obj.obj U)
  rw [id_tensorHom] at hmap
  erw [hmap, hr]
  have hs := congrArg (fun t ↦ t.val U)
    ((SheafOfModules.unitHomEquiv _).apply_symm_apply
      (show (SheafOfModules.unit
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)).sections from
        ⟨s.val, s.property⟩))
  change (ringedKoszulScalar O s).asHom.val.app U (1 : O.obj.obj U) = s.val U at hs
  erw [hs]
  simpa only [SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using hf U m
end OrdinaryScalar

/-- The canonical constant coefficient and quotient comparisons identify the action of
one uniformizer on every ordinary module. This statement involves a single scalar and
ordinary module objects; it makes no claim about regularity, ideals, powers, complexes,
Koszul complexes or totalization.

Source: integral-models proof (1), constant coefficient comparison; Stacks Project,
algebraization.tex, Lemma derived-completion-koszul (0A0E), rank-one scalar action.
(auxiliary; not a blueprint node).

Proof: use the monoidal constant-sheaf/inverse-image comparison on the integer ring
and its first quotient. Reconstruct section rings and restrict along AsSmall.down.
Naturality for the quotient gives the displayed square. On the point, extensionality
on continuous functions identifies d with multiplication by the chosen uniformizer.
The pointComparison transports the identical continuous coefficient presentations.
The constant coefficient map sends the sheafification-unit section of the uniformizer
to its constant continuous function; the monoidal inverse-image comparison preserves
this equation. For any module M, precompose the left-unitor expression defining
scalarOnModules with the relative tensor projection. It becomes the module action
of that constant section, by the unit and action identities. Both scalar restrictions
leave the underlying additive map unchanged. The section-module equivalence identifies
the internal action with the actual section action. Finally, the right unitor on
ordinary module sheaves identifies this same action with tensoring by the endomorphism
of the rank-one module associated to the section. This proves the equation for every
M, without a flatness or boundedness hypothesis. All these maps are defined by the
same unit, action and quotient maps, including for the empty scheme and zero modules.
-/
theorem ordinary_uniformizer_scalar_comparison :
    ∃ e : IntegralConstantCompletion.constantRing l E X ≅ ring l E X,
    ∃ f : IntegralConstantCompletion.finiteRing l E X 0 ≅
        smallRing X (condensedRingObj
          (discreteObj (Padic.coefficientExtensionRing l E 1)) X),
      (IntegralConstantCompletion.quotientMap l E X false 0 ≫ f.hom =
        e.hom ≫ residue l E X) ∧
      ∀ (d : End (Mod.regular (DerivedNakayama.integerRing l E))),
        (∀ (S : Profinite.{u}ᵒᵖ) (b : (DerivedNakayama.integerRing l E).obj.obj S)
          (s : S.unop), ((d.asHom.hom.hom.app S) b).down s =
            Padic.coefficientExtensionUniformizer l E * b.down s) →
        ∀ M : AdicCompletion.Modules l E X,
          (modules l E X).map ((DerivedNakayama.scalarOnModules l E X d).app M) ≫
              (ρ_ ((modules l E X).obj M)).inv =
            (ρ_ ((modules l E X).obj M)).inv ≫ (modules l E X).obj M ◁
              (ringedKoszulScalar (ring l E X) (ConstantCompletion.algebraSection e.hom
                (ULift.up (Padic.coefficientExtensionUniformizer l E)))).asHom := by
  let A := Padic.coefficientExtensionIntegers l E
  let I := Padic.coefficientExtensionIdeal l E 1
  have hI : Ideal.map (ULift.ringEquiv : ULift.{u + 1} A ≃+* A).symm.toRingHom I =
      IntegralConstantCompletion.ideal l E := by
    simp only [I, Padic.coefficientExtensionIdeal, pow_one,
      IntegralConstantCompletion.ideal, Ideal.map_span, Set.image_singleton]
    rfl
  have hq := canonical_quotient_comparison X A I
  dsimp only at hq
  rw [hI] at hq
  obtain ⟨f, hf⟩ := hq
  refine ⟨smallIso X A, f, hf, ?_⟩
  intro d hd M
  apply ordinary_scalar_characterization (ring l E X) ((modules l E X).obj M)
    (ConstantCompletion.algebraSection (smallIso X A).hom
      (ULift.up (Padic.coefficientExtensionUniformizer l E)))
    (.of ((modules l E X).map ((DerivedNakayama.scalarOnModules l E X d).app M)))
  intro U m
  rw [smallIso_section_element X A
    (ULift.up (Padic.coefficientExtensionUniformizer l E)) U]
  unfold modules at m ⊢
  exact restricted_scalar_sections X (scalarMap l E X)
    (coefficientMap (IntegralConstantModel.pointComparison l E).inv.hom X)
    (constantElement (Scheme.ProEt.topology X)
      (show AddCommGrpCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))
        from ULift.up (Padic.coefficientExtensionUniformizer l E)) ≫
      (schemeIso X A).hom) _ (uniformizer_section l E X d hd) M
    (.of ((DerivedNakayama.scalarOnModules l E X d).app M))
    (scalarOnModules_underlying l E X d M) U m

end AlgebraicGeometry.ProEtale.InternalCompletionTransport
