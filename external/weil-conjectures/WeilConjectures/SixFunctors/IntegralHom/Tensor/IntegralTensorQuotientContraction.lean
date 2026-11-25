/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralHom.Reduction.IntegralHomReductionModels
public import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import all WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerUnrestrictedSupplement
import all WeilConjectures.Algebra.Homology.ScalarHomCancellation.ScalarHomTensorCancellation
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Ordinary tensor contraction for coefficient quotients

Source: Stacks Project, Modules on Sites, Tag 03CZ, and Cohomology on Sites,
Tag 07A4; the coefficient calculation in the integral Verdier proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.IntegralHom

open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace QuotientContraction

variable (X : Scheme.{u})
  (R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (c : R ⟶ S)

private noncomputable abbrev forgetRing
    (A : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A

private noncomputable abbrev restriction :=
  SheafOfModules.restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)

private noncomputable abbrev coefficient : Modules.{u, u} X R :=
  (restriction X R S c).obj (SheafOfModules.unit (forgetRing X S))

attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall

private noncomputable local instance fixedSmall : EssentiallySmall.{u+1} X.ProEt :=
  WeilConjectures.integralReductionSiteEssentiallySmall.{u,u} X

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients

attribute [local irreducible] SheafOfModules.monoidalCategory

private noncomputable def rawIso (M : Modules.{u, u} X R) :
    (PresheafOfModules.restrictScalars.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c).hom).obj
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M) ≅
      (coefficient X R S c).val ⊗ M.val :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro U V f
    ext z
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp only [map_add, hz, hw]
    | tmul s x =>
      exact (Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap c M f) s x))

private noncomputable def coefficientIso (M : Modules.{u, u} X R) :
    (restriction X R S c).obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M) ≅
      ((ordinaryTensor.{u, u} X R).obj (coefficient X R S c)).obj M :=
  (SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M)).symm ≪≫
    (PresheafOfModules.sheafification.{u + 1} (𝟙 (forgetRing X R).obj)).mapIso
      (rawIso X R S c M) ≪≫
    (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
      (R := R) (coefficient X R S c) M).symm

-- Compare the scalar and module sheafifications explicitly.
private theorem coefficientIso_pure (M : Modules.{u, u} X R) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (coefficientIso X R S c M).hom.val.app U
      ((toSheafify (Scheme.ProEt.topology X)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).presheaf).app U
          (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      pair.{u, u} X R (coefficient X R S c) M U s x := by
  let A := forgetRing X R
  let B := forgetRing X S
  let α := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map c
  let P := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M
  let a := PresheafOfModules.sheafification.{u + 1} (𝟙 A.obj)
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 A.obj)
  let e := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyIso α P
  have he : e.hom.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    have h := SheafOfModules.ScalarHomCancellation.cancellationRestrictSheafifyHom_toSheaf
      α P
    exact congrArg (fun f ↦ f.hom.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) h
  have hei : e.inv.val.app U
      ((toSheafify (Scheme.ProEt.topology X) P.presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x)) =
      (adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x) := by
    rw [← he]
    exact congrArg (fun f ↦ f.val.app U
      ((adj.unit.app ((PresheafOfModules.restrictScalars.{u + 1} α.hom).obj P)).app U
        (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))) e.hom_inv_id
  change (SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
    (R := R) (coefficient X R S c) M).inv.val.app U
    ((a.map (rawIso X R S c M).hom).val.app U (e.inv.val.app U _)) = _
  rw [hei]
  have hn := congrArg (fun f ↦ f.app U
    (s ⊗ₜ[R.obj.obj U, (c.hom.app U).hom] x))
    (adj.unit.naturality (rawIso X R S c M).hom)
  exact congrArg ((SheafOfModules.tensorObjIsoSheafification.{u, u + 1, u + 1}
    (R := R) (coefficient X R S c) M).inv.val.app U) hn.symm

private theorem transportedMap_pure
    (F : Modules.{u, u} X R ⥤ Modules.{u, u} X S)
    (hobj : ∀ M, F.obj M = SheafOfModules.changeOfRings c M)
    (hmap : ∀ {M N} (f : M ⟶ N), F.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom c M f ≫ eqToHom (hobj N).symm)
    {M N : Modules.{u, u} X R} (f : M ⟶ N) (U : X.ProEtᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (F.map f).val.app U
      ((eqToHom (hobj M).symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection c M U s x)) =
      (eqToHom (hobj N).symm).val.app U
        (SheafOfModules.UnrestrictedTowerProof.tensorSection c N U s (f.val.app U x)) := by
  rw [hmap]
  have hc (z : (SheafOfModules.changeOfRings c M).val.obj U) :
      (eqToHom (hobj M)).val.app U ((eqToHom (hobj M).symm).val.app U z) = z :=
    ConcreteCategory.congr_hom
      (congrArg (fun k ↦ k.val.app U) (eqToHom_trans (hobj M).symm (hobj M))) z
  change (eqToHom (hobj N).symm).val.app U
      ((SheafOfModules.changeOfRingsHom c M f).val.app U
        ((eqToHom (hobj M)).val.app U ((eqToHom (hobj M).symm).val.app U _))) = _
  rw [hc]
  exact congrArg ((eqToHom (hobj N).symm).val.app U)
    (SheafOfModules.UnrestrictedTowerProof.map_tensorSection c M f U s x)

section Levels

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private noncomputable abbrev base := completedIntegralCommRingSheafUnrestricted l E X
private noncomputable abbrev level (n : ℕ) := integralCoefficientCommRingSheaf l E X n
private noncomputable abbrev projection (n : ℕ) :=
  completedIntegralCommRingProjectionUnrestricted l E X n
private noncomputable abbrev coeff (n : ℕ) :=
  coefficient X (base X l E) (level X l E n) (projection X l E n)

attribute [local irreducible] scalarReductionExistence
  completedIntegralCoefficientSheafUnrestricted constantSheaf
attribute [local implicit_reducible] scalarReductionExtension
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted

private noncomputable def levelIso (n : ℕ) (M : scalarReductionSource l E X) :
    (sfReductionRestricted l E X n).obj M ≅
      ((ordinaryTensor.{u, u} X (base X l E)).obj (coeff X l E n)).obj M :=
  (scalarReductionRestriction l E X n).mapIso
    (eqToIso ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose M)) ≪≫
    coefficientIso X (base X l E) (level X l E n) (projection X l E n) M

private theorem levelIso_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).hom.val.app U (sfReductionTensor l E X n M U s x) =
      pair.{u, u} X (base X l E) (coeff X l E n) M U s x := by
  let h := (scalarReductionExistence.{u, u} l E X n).choose_spec.choose M
  change (coefficientIso X (base X l E) (level X l E n)
    (projection X l E n) M).hom.val.app U
      (((eqToHom h.symm ≫ eqToHom h).val.app U) _) = _
  simp only [eqToHom_trans, eqToHom_refl]
  exact coefficientIso_pure X (base X l E) (level X l E n) (projection X l E n) M U s x

private theorem levelIso_inv_pure (n : ℕ) (M : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    (levelIso X l E n M).inv.val.app U
      (pair.{u, u} X (base X l E) (coeff X l E n) M U s x) =
      sfReductionTensor l E X n M U s x := by
  rw [← levelIso_pure X l E n M U s x]
  exact congrArg (fun f ↦ f.val.app U (sfReductionTensor l E X n M U s x))
    (levelIso X l E n M).hom_inv_id

private theorem reductionMap_pure (n : ℕ) {M N : scalarReductionSource l E X}
    (f : M ⟶ N) (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U) (x : M.val.obj U) :
    ((sfReductionRestricted l E X n).map f).val.app U
      (sfReductionTensor l E X n M U s x) =
      sfReductionTensor l E X n N U s (f.val.app U x) := by
  exact transportedMap_pure X (base X l E) (level X l E n) (projection X l E n)
    (scalarReductionExtension l E X n)
    ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose)
    ((scalarReductionExistence.{u, u} l E X n).choose_spec.choose_spec.choose) f U s x

private theorem levelIso_naturality (n : ℕ) {M N : scalarReductionSource l E X}
    (f : M ⟶ N) :
    (sfReductionRestricted l E X n).map f ≫ (levelIso X l E n N).hom =
      (levelIso X l E n M).hom ≫
        ((ordinaryTensor.{u, u} X (base X l E)).obj (coeff X l E n)).map f := by
  apply WeilConjectures.sfReductionTensor_hom_ext l E X n M
  intro U s x
  change (levelIso X l E n N).hom.val.app U
    (((sfReductionRestricted l E X n).map f).val.app U _) = _
  rw [reductionMap_pure, levelIso_pure]
  change _ = (((ordinaryTensor.{u, u} X (base X l E)).obj (coeff X l E n)).map f).val.app U
    ((levelIso X l E n M).hom.val.app U _)
  rw [levelIso_pure]
  exact (CategoryTheory.CochainPullback.moduleTmul_map
    (R := base X l E) (𝟙 (coeff X l E n)) f U s x).symm.trans (by
      simp only [tensorHom_def, id_whiskerRight, Category.id_comp]; rfl)

open CategoryTheory.CochainPullback
attribute [local instance] SheafOfModules.symmetricCategory

private noncomputable def commute (C P Q : Modules.{u, u} X (base X l E)) :
    P ⊗ (C ⊗ Q) ⟶ C ⊗ (P ⊗ Q) :=
  (α_ P C Q).inv ≫ ((β_ P C).hom ⊗ₘ 𝟙 Q) ≫ (α_ C P Q).hom

private theorem commute_pure (C P Q : Modules.{u, u} X (base X l E))
    (U : X.ProEtᵒᵖ) (s : C.val.obj U) (x : P.val.obj U) (y : Q.val.obj U) :
    (commute X l E C P Q).val.app U
      (pair.{u, u} X (base X l E) P (C ⊗ Q) U x
        (pair.{u, u} X (base X l E) C Q U s y)) =
      pair.{u, u} X (base X l E) C (P ⊗ Q) U s
        (pair.{u, u} X (base X l E) P Q U x y) := by
  have ha := moduleTmul_associator (R := base X l E) P C Q U x s y
  have hai : (α_ P C Q).inv.val.app U
      (moduleTmul P (C ⊗ Q) U x (moduleTmul C Q U s y)) =
      moduleTmul (P ⊗ C) Q U (moduleTmul P C U x s) y := by
    rw [← ha]
    exact congrArg (fun f ↦ f.val.app U
      (moduleTmul (P ⊗ C) Q U (moduleTmul P C U x s) y)) (α_ P C Q).hom_inv_id
  change (α_ C P Q).hom.val.app U
    (((β_ P C).hom ⊗ₘ 𝟙 Q).val.app U
      ((α_ P C Q).inv.val.app U
        (moduleTmul P (C ⊗ Q) U x (moduleTmul C Q U s y)))) = _
  rw [hai, moduleTmul_map (R := base X l E) (β_ P C).hom (𝟙 Q) U,
    moduleTmul_braiding (R := base X l E) P C U x s]
  exact moduleTmul_associator C P Q U s x y

private theorem commute_naturality
    {C C' P P' Q Q' : Modules.{u, u} X (base X l E)}
    (h : C ⟶ C') (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ (h ⊗ₘ g)) ≫ commute X l E C' P' Q' =
      commute X l E C P Q ≫ (h ⊗ₘ (f ⊗ₘ g)) := by
  dsimp only [commute]
  rw [associator_inv_naturality_assoc]
  have hb : ((f ⊗ₘ h) ⊗ₘ g) ≫ ((β_ P' C').hom ⊗ₘ 𝟙 Q') =
      ((β_ P C).hom ⊗ₘ 𝟙 Q) ≫ ((h ⊗ₘ f) ⊗ₘ g) := by
    simp only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      BraidedCategory.braiding_naturality]
  rw [← Category.assoc (((f ⊗ₘ h) ⊗ₘ g)), hb]
  simp only [Category.assoc, associator_naturality]

private noncomputable def moduleContraction (n : ℕ)
    (P Q : scalarReductionSource l E X) :
    P ⊗ (sfReductionRestricted l E X n).obj Q ⟶
      (sfReductionRestricted l E X n).obj (P ⊗ Q) :=
  (𝟙 P ⊗ₘ (levelIso X l E n Q).hom) ≫
    commute X l E (coeff X l E n) P Q ≫ (levelIso X l E n (P ⊗ Q)).inv

private theorem moduleContraction_pure (n : ℕ) (P Q : scalarReductionSource l E X)
    (U : X.ProEtᵒᵖ) (s : (level X l E n).obj.obj U)
    (x : P.val.obj U) (y : Q.val.obj U) :
    (moduleContraction X l E n P Q).val.app U
      (pair.{u, u} X (base X l E) P ((sfReductionRestricted l E X n).obj Q)
        U x (sfReductionTensor l E X n Q U s y)) =
      sfReductionTensor l E X n (P ⊗ Q) U s
        (pair.{u, u} X (base X l E) P Q U x y) := by
  change (levelIso X l E n (P ⊗ Q)).inv.val.app U
    ((commute X l E (coeff X l E n) P Q).val.app U
      ((𝟙 P ⊗ₘ (levelIso X l E n Q).hom).val.app U _)) = _
  have ht := moduleTmul_map (R := base X l E) (𝟙 P) (levelIso X l E n Q).hom U x
    (show ((sfReductionRestricted l E X n).obj Q).val.obj U from
      sfReductionTensor l E X n Q U s y)
  have hm := congrArg (fun z ↦ (levelIso X l E n (P ⊗ Q)).inv.val.app U
    ((commute X l E (coeff X l E n) P Q).val.app U z)) ht
  refine hm.trans ?_
  change (levelIso X l E n (P ⊗ Q)).inv.val.app U
    ((commute X l E (coeff X l E n) P Q).val.app U
      (pair.{u, u} X (base X l E) P (coeff X l E n ⊗ Q) U x
        ((levelIso X l E n Q).hom.val.app U
          (sfReductionTensor l E X n Q U s y)))) = _
  rw [levelIso_pure, commute_pure, levelIso_inv_pure]

private theorem moduleContraction_naturality (n : ℕ)
    {P P' Q Q' : scalarReductionSource l E X} (f : P ⟶ P') (g : Q ⟶ Q') :
    (f ⊗ₘ (sfReductionRestricted l E X n).map g) ≫
        moduleContraction X l E n P' Q' =
      moduleContraction X l E n P Q ≫ (sfReductionRestricted l E X n).map (f ⊗ₘ g) := by
  dsimp only [moduleContraction]
  have he := levelIso_naturality X l E n g
  have ht := levelIso_naturality X l E n (f ⊗ₘ g)
  have hti : (𝟙 (coeff X l E n) ⊗ₘ (f ⊗ₘ g)) ≫
      (levelIso X l E n (P' ⊗ Q')).inv =
      (levelIso X l E n (P ⊗ Q)).inv ≫
        (sfReductionRestricted l E X n).map (f ⊗ₘ g) := by
    apply (cancel_epi (levelIso X l E n (P ⊗ Q)).hom).mp
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
      Category.comp_id, curriedTensor_obj_map, ← id_tensorHom] using
      congrArg (fun h ↦ h ≫ (levelIso X l E n (P' ⊗ Q')).inv) ht.symm
  have hfirst : (f ⊗ₘ (sfReductionRestricted l E X n).map g) ≫
      (𝟙 P' ⊗ₘ (levelIso X l E n Q').hom) =
      (𝟙 P ⊗ₘ (levelIso X l E n Q).hom) ≫
        (f ⊗ₘ (𝟙 (coeff X l E n) ⊗ₘ g)) := by
    simpa only [tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp,
      curriedTensor_obj_map, ← id_tensorHom] using
      congrArg (fun h ↦ f ⊗ₘ h) he
  rw [← Category.assoc, ← Category.assoc, hfirst]
  simp only [Category.assoc]
  rw [← Category.assoc (f ⊗ₘ _), commute_naturality]
  simp only [Category.assoc]
  rw [hti]

private noncomputable def coeffStep (n : ℕ) :
    coeff X l E (n + 1) ⟶ coeff X l E n where
  val :=
    { app := fun U ↦ ModuleCat.ofHom
        (X := (coeff X l E (n + 1)).val.obj U)
        (Y := (coeff X l E n).val.obj U)
        { toFun := (unrestrictedCoefficientStep.{u, u} l E X n).hom.app U
          map_add' := map_add _
          map_smul' := fun r s ↦ by
            change (level X l E (n + 1)).obj.obj U at s
            change (unrestrictedCoefficientStep.{u, u} l E X n).hom.app U
                ((projection X l E (n + 1)).hom.app U r * s) =
              (projection X l E n).hom.app U r *
                (unrestrictedCoefficientStep.{u, u} l E X n).hom.app U s
            rw [map_mul]
            have h := congrArg (fun k ↦ k.hom.app U)
              (unrestrictedCoefficientStep_comp.{u, u} l E X n)
            exact congrArg (fun z ↦ z *
              (unrestrictedCoefficientStep.{u, u} l E X n).hom.app U s)
                (ConcreteCategory.congr_hom h r) }
      naturality := fun {U V} f ↦ by
        ext s
        exact ConcreteCategory.congr_hom
          ((unrestrictedCoefficientStep.{u, u} l E X n).hom.naturality f) s }

private theorem levelIso_transition (n : ℕ) (M : scalarReductionSource l E X) :
    (sfReductionTransition l E X n).app M ≫ (levelIso X l E n M).hom =
      (levelIso X l E (n + 1) M).hom ≫ (coeffStep X l E n ⊗ₘ 𝟙 M) := by
  apply WeilConjectures.sfReductionTensor_hom_ext l E X (n + 1) M
  intro U s x
  change (levelIso X l E n M).hom.val.app U
    (((sfReductionTransition l E X n).app M).val.app U _) =
      (coeffStep X l E n ⊗ₘ 𝟙 M).val.app U
        ((levelIso X l E (n + 1) M).hom.val.app U _)
  rw [show ((sfReductionTransition l E X n).app M).val.app U
      (sfReductionTensor l E X (n + 1) M U s x) =
        sfReductionTensor l E X n M U
          ((integralCoefficientSheafTransition l E X n).hom.app U s) x from
    (sfReductionTransition_existsUnique l E X n).exists.choose_spec M U s x]
  rw [levelIso_pure, levelIso_pure]
  erw [moduleTmul_map (R := base X l E) (coeffStep X l E n) (𝟙 M) U s x]
  rfl

private theorem moduleContraction_transition (n : ℕ)
    (P Q : scalarReductionSource l E X) :
    (𝟙 P ⊗ₘ (sfReductionTransition l E X n).app Q) ≫
        moduleContraction X l E n P Q =
      moduleContraction X l E (n + 1) P Q ≫
        (sfReductionTransition l E X n).app (P ⊗ Q) := by
  apply (cancel_mono (levelIso X l E n (P ⊗ Q)).hom).mp
  simp only [moduleContraction, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [levelIso_transition]
  simp only [Iso.inv_hom_id_assoc]
  have hfirst : (𝟙 P ⊗ₘ (sfReductionTransition l E X n).app Q) ≫
      (𝟙 P ⊗ₘ (levelIso X l E n Q).hom) =
      (𝟙 P ⊗ₘ (levelIso X l E (n + 1) Q).hom) ≫
        (𝟙 P ⊗ₘ (coeffStep X l E n ⊗ₘ 𝟙 Q)) := by
    simpa only [tensorHom_comp_tensorHom, Category.id_comp] using
      congrArg (fun h ↦ 𝟙 P ⊗ₘ h) (levelIso_transition X l E n Q)
  rw [← Category.assoc, hfirst, Category.assoc]
  have hc := commute_naturality X l E (coeffStep X l E n) (𝟙 P) (𝟙 Q)
  simpa only [id_tensorHom_id, Category.assoc] using
    congrArg (fun h ↦ (𝟙 P ⊗ₘ (levelIso X l E (n + 1) Q).hom) ≫ h) hc

end Levels

section Total

variable {A : Type*} [Category A] [Abelian A] [MonoidalCategory A]
  [MonoidalPreadditive A] [HasCoproducts.{0} A]
  (L : A ⥤ A) [L.Additive]
  (e : ∀ P Q : A, P ⊗ L.obj Q ⟶ L.obj (P ⊗ Q))

private noncomputable def mixedComponent (P Q : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctor P ((L.mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor A)).X n ⟶
      L.obj ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X n) :=
  HomologicalComplex.mapBifunctorDesc (fun a b h ↦ e (P.X a) (Q.X b) ≫
    L.map (CochainComplex.ιMapBifunctor P Q (curriedTensor A) a b n h))

private theorem mixedComponent_comm
    (he : ∀ {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q'),
      (f ⊗ₘ L.map g) ≫ e P' Q' = e P Q ≫ L.map (f ⊗ₘ g))
    (P Q : CochainComplex A ℤ) (n m : ℤ) :
    mixedComponent L e P Q n ≫
        L.map ((CochainComplex.mapBifunctor P Q (curriedTensor A)).d n m) =
      (CochainComplex.mapBifunctor P ((L.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor A)).d n m ≫ mixedComponent L e P Q m := by
  by_cases hnm : (ComplexShape.up ℤ).Rel n m
  · change n + 1 = m at hnm
    subst m
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro a b hab
    change a + b = n at hab
    simp only [mixedComponent, HomologicalComplex.ι_mapBifunctorDesc_assoc,
      HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add, Preadditive.add_comp,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    simp only [L.map_add, Preadditive.comp_add, Category.assoc]
    rw [← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₁,
      ← L.map_comp, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq P Q _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P Q _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₁_eq P
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) _ _
        (show (ComplexShape.up ℤ).Rel a (a + 1) from rfl) b (n + 1)
        (by change a + 1 + b = n + 1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq P
        ((L.mapHomologicalComplex (.up ℤ)).obj Q) _ _ a
        (show (ComplexShape.up ℤ).Rel b (b + 1) from rfl) (n + 1)
        (by change a + (b + 1) = n + 1; omega)]
    simp only [ComplexShape.ε₁_def, ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ,
      one_smul, Functor.map_units_smul, Functor.map_comp, Linear.comp_units_smul,
      Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
    simp only [curriedTensor_map_app, curriedTensor_obj_map,
      Functor.mapHomologicalComplex_obj_d, ← tensorHom_id, ← id_tensorHom]
    dsimp only [Functor.mapHomologicalComplex, curriedTensor_obj_obj]
    apply congrArg₂ (· + ·)
    · simpa only [L.map_id, Category.assoc] using
        congrArg (fun f ↦ f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            (a + 1) b (n + 1) (by omega))) (he (P.d a (a + 1)) (𝟙 (Q.X b))).symm
    · simpa only [L.map_id, Category.assoc, Linear.units_smul_comp,
        Linear.comp_units_smul] using
        congrArg (fun f ↦ a.negOnePow • (f ≫ L.map
          (CochainComplex.ιMapBifunctor P Q (curriedTensor A)
            a (b + 1) (n + 1) (by omega)))) (he (𝟙 (P.X a)) (Q.d b (b + 1))).symm
  · rw [HomologicalComplex.shape _ n m hnm, HomologicalComplex.shape _ n m hnm,
      L.map_zero, comp_zero, zero_comp]

private noncomputable def mixedTotal
    (he : ∀ {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q'),
      (f ⊗ₘ L.map g) ≫ e P' Q' = e P Q ≫ L.map (f ⊗ₘ g))
    (P Q : CochainComplex A ℤ) :
    CochainComplex.mapBifunctor P ((L.mapHomologicalComplex (.up ℤ)).obj Q)
        (curriedTensor A) ⟶
      (L.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P Q (curriedTensor A)) where
  f := mixedComponent L e P Q
  comm' n m _ := mixedComponent_comm L e he P Q n m

private theorem mixedTotal_transition
    (he : ∀ {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q'),
      (f ⊗ₘ L.map g) ≫ e P' Q' = e P Q ≫ L.map (f ⊗ₘ g))
    (M : A ⥤ A) [M.Additive]
    (e' : ∀ P Q : A, P ⊗ M.obj Q ⟶ M.obj (P ⊗ Q))
    (he' : ∀ {P P' Q Q' : A} (f : P ⟶ P') (g : Q ⟶ Q'),
      (f ⊗ₘ M.map g) ≫ e' P' Q' = e' P Q ≫ M.map (f ⊗ₘ g))
    (θ : L ⟶ M)
    (hθ : ∀ P Q, (𝟙 P ⊗ₘ θ.app Q) ≫ e' P Q = e P Q ≫ θ.app (P ⊗ Q))
    (P Q : CochainComplex A ℤ) :
    HomologicalComplex.mapBifunctorMap (𝟙 P)
        ((NatTrans.mapHomologicalComplex θ (.up ℤ)).app Q) (curriedTensor A) (.up ℤ) ≫
        mixedTotal M e' he' P Q =
      mixedTotal L e he P Q ≫
        (NatTrans.mapHomologicalComplex θ (.up ℤ)).app
          (CochainComplex.mapBifunctor P Q (curriedTensor A)) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j h
  simp only [HomologicalComplex.comp_f, mixedTotal,
    HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, mixedComponent,
    NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f,
    curriedTensor_map_app, id_whiskerRight,
    curriedTensor_obj_map, HomologicalComplex.ι_mapBifunctorDesc]
  dsimp only [Functor.mapHomologicalComplex]
  simp only [Category.assoc, ← id_tensorHom]
  erw [Category.id_comp]
  change (𝟙 (P.X i) ⊗ₘ θ.app (Q.X j)) ≫
      (e' (P.X i) (Q.X j) ≫ M.map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor A) i j k h)) =
    e (P.X i) (Q.X j) ≫ L.map
        (CochainComplex.ιMapBifunctor P Q (curriedTensor A) i j k h) ≫
      θ.app ((CochainComplex.mapBifunctor P Q (curriedTensor A)).X k)
  rw [← Category.assoc, hθ, Category.assoc, ← θ.naturality]

end Total

end QuotientContraction

attribute [-instance] tensorLocalization abSheafify abLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall

attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local irreducible] SheafOfModules.monoidalCategory

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})

/-- Ordinary total tensor admits the scalar-first contraction for every quotient.

Source: Stacks 03CZ, lemma-adjointness-tensor-restrict, and 07A4,
lemma-pullback-tensor-product; the coefficient-unit calculation in
thm-coef-integral-verdier.proof.md.

Proof: in bidegree (i,j) use the balanced map
x tensor (s tensor y) ↦ s tensor (x tensor y). It is linear over the completed
coefficient ring and commutes with restriction maps. Sheafify the balanced maps
and sum over i+j=k. Both differentials act on x and y only; s is in degree zero,
so the two signed total differentials commute with these maps. This constructs
b for arbitrary complexes, with the displayed formula. For the last equation,
precompose with every total summand and both sheafification units. Both routes
send x tensor (s tensor y) to q(s) tensor (x tensor y), by the defining pure-tensor
formula of sfReductionTransition. Tensor induction, sheafification adjunction,
and coproduct extensionality give equality. No flatness or derived category
occurs, and exponent one, zero complexes, and the empty site cause no exception.
(blueprint: lem-sf-integral-ordinary-tensor-quotient-contraction). -/
theorem ordinaryTensorQuotient_contractions :
    let R := completedIntegralCommRingSheafUnrestricted l E X
    let F := fun n : ℕ ↦ (sfReductionRestricted l E X n).mapHomologicalComplex (.up ℤ)
    let T := totalTensor.{u, u} X R
    ∃ b : ∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ),
        (T.obj P).obj ((F n).obj Q) ⟶ (F n).obj ((T.obj P).obj Q),
      (∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ)
          (i j : ℤ) (U : X.ProEtᵒᵖ)
          (s : (integralCoefficientCommRingSheaf l E X n).obj.obj U)
          (x : (P.X i).val.obj U) (y : (Q.X j).val.obj U),
        ((b P Q n).f (i + j)).val.app U
            (totalPair.{u, u} X R P ((F n).obj Q) i j U x
              (sfReductionTensor l E X n (Q.X j) U s y)) =
          sfReductionTensor l E X n (((T.obj P).obj Q).X (i + j)) U s
            (totalPair.{u, u} X R P Q i j U x y)) ∧
      ∀ (P Q : CochainComplex (scalarReductionSource l E X) ℤ) (n : ℕ),
        (T.obj P).map
            ((NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app Q) ≫
            b P Q n =
          b P Q (n + 1) ≫
            (NatTrans.mapHomologicalComplex (sfReductionTransition l E X n) (.up ℤ)).app
              ((T.obj P).obj Q) := by
  let R := completedIntegralCommRingSheafUnrestricted l E X
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{u} _
  let : MonoidalCategory (scalarReductionSource.{u, u} l E X) :=
    SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  let : HasColimitsOfSize.{0, 0} (scalarReductionSource.{u, u} l E X) :=
    countableColimits.{u, u} X R
  let := ordinaryTensorZero.{u, u} X R
  let : ∀ M : Modules.{u, u} X R,
      ((ordinaryTensor.{u, u} X R).obj M).PreservesZeroMorphisms :=
    fun M ↦ ordinaryTensorObjZero.{u, u} X R M
  let L := fun n ↦ sfReductionRestricted l E X n
  let e := fun n ↦ QuotientContraction.moduleContraction X l E n
  have he (n : ℕ) {P P' Q Q' : scalarReductionSource l E X}
      (f : P ⟶ P') (g : Q ⟶ Q') :
      (f ⊗ₘ (L n).map g) ≫ e n P' Q' = e n P Q ≫ (L n).map (f ⊗ₘ g) :=
    QuotientContraction.moduleContraction_naturality X l E n f g
  refine ⟨fun P Q n ↦ QuotientContraction.mixedTotal (L n) (e n) (he n) P Q, ?_, ?_⟩
  · intro P Q n i j U s x y
    change (((CochainComplex.ιMapBifunctor P
        (((L n).mapHomologicalComplex (.up ℤ)).obj Q) (ordinaryTensor.{u, u} X R)
        i j (i + j) rfl) ≫
      QuotientContraction.mixedComponent (L n) (e n) P Q (i + j)).val.app U)
        (pair.{u, u} X R (P.X i) ((L n).obj (Q.X j)) U x
          (sfReductionTensor l E X n (Q.X j) U s y)) = _
    rw [QuotientContraction.mixedComponent, HomologicalComplex.ι_mapBifunctorDesc]
    change (((L n).map
      (CochainComplex.ιMapBifunctor P Q (ordinaryTensor.{u, u} X R) i j (i + j) rfl)).val.app U)
        ((e n (P.X i) (Q.X j)).val.app U
          (pair.{u, u} X R (P.X i) ((L n).obj (Q.X j)) U x
            (sfReductionTensor l E X n (Q.X j) U s y))) = _
    erw [QuotientContraction.moduleContraction_pure,
      QuotientContraction.reductionMap_pure]
    rfl
  · intro P Q n
    exact QuotientContraction.mixedTotal_transition (L (n + 1)) (e (n + 1)) (he (n + 1))
      (L n) (e n) (he n) (sfReductionTransition l E X n)
      (QuotientContraction.moduleContraction_transition X l E n) P Q

end WeilConjectures.IntegralHom
