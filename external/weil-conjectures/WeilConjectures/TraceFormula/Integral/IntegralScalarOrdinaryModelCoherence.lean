/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedLineTensor.CompletedScalarOrdinaryCoherence
public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.TraceFormula.Integral.IntegralScalarOrdinaryModelComparison
import all WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructible
import all WeilConjectures.TraceFormula.Supporting.FiniteFreeCompletedScalarComparison
import all WeilConjectures.SmoothPurity.Scalar.ScalarExtensionComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Coherence of the two ordinary scalar models

Source: Stacks Tags 06YY and 0941; the finite-free tensor normalization.
(blueprint: lem-trf-integral-scalar-ordinary-model-coherence).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [-instance] scalarReductionSourceDerived scalarReductionTargetDerived
attribute [-instance] integralOperationsSiteSmall
attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local instance 50000] hasSheafCompose_of_preservesLimitsOfSize
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
  PrincipalKoszulStrictReplacement.abSheafify
  PrincipalKoszulStrictReplacement.abLocallyBijective
  PrincipalKoszulStrictReplacement.siteSmall
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
  integralOperationsCommHasDerivedCategory
  SheafOfModules.cochainModulesMonoidal SheafOfModules.cochainModulesSymmetric
  SheafOfModules.cochainModulesPreadditive

private local instance (W : Scheme.{u}) : EssentiallySmall.{u+1} W.ProEt :=
  essentiallySmallSelf.{0, u, u+1} _

private local instance (W : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology W) AddCommGrpCat.{u+1} :=
  integralCoefficientAbSheafify.{u, u} W

private local instance (W : Scheme.{u}) :
    (Scheme.ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u+1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

attribute [local irreducible] HasDerivedCategory.standard
  completedScalarChangeData
  integralOrdinaryScalar completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingSheafUnrestricted

private theorem scalarTensor_ext
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{u})
    (N : integralTowerModules l E X) (P : integralTowerModules l L X)
    (f g : (integralOrdinaryScalar l E L ι X).obj N ⟶ P)
    (h : ∀ U s x, f.val.app U (integralOrdinaryTensorSection l E L ι X N U s x) =
      g.val.app U (integralOrdinaryTensorSection l E L ι X N U s x)) : f = g := by
  apply tensorSection_ext (integralCompletedScalarMap l E L ι X)
    (integralOrdinaryScalar l E L ι X) (scalar_obj l E L ι X) N P f g
  intro U x
  rw [tensorSection_eq]
  exact h U 1 x

private theorem scalarModelComparison_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u})
    (t₀ : integralOrdinaryScalar l E E (AlgHom.id ℚ_[l] E) X ≅
      completedOrdinaryScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) X)
    (ht₀ : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l E X).obj.obj U)
      (x : N.val.obj U),
      (t₀.hom.app N).val.app U
          (integralOrdinaryTensorSection l E E (AlgHom.id ℚ_[l] E) X N U s x) =
        completedScalarTensorSection.{u, u} l E E (AlgHom.id ℚ_[l] E) X N U s x)
    (e : integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) X ≅
      completedDerivedScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) X)
    (he : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      e.hom.app (DerivedCategory.Q.obj P) ≫
          completedScalarCounit.{u, u} l E E (AlgHom.id ℚ_[l] E) X P =
        (integralOrdinaryScalar l E E (AlgHom.id ℚ_[l] E) X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              t₀ (.up ℤ)).hom.app P)) :
    e.hom ≫ (CompletedLineTensor.ordinaryUnit l E X).hom =
      (integralOrdinaryDerivedScalarUnit l E X).hom := by
  let t := NatIso.mapHomologicalComplex
    t₀ (.up ℤ)
  have hchain (P : CochainComplex (integralTowerModules l E X) ℤ) :
      t.hom.app P ≫ (completedScalarIdentityMultiplication.{u, u} l E X).hom.app P =
        (NatIso.mapHomologicalComplex (integralOrdinaryScalarUnit l E X) (.up ℤ)).hom.app P := by
    ext i : 1
    dsimp only [t, NatIso.mapHomologicalComplex_hom_app_f,
      HomologicalComplex.comp_f, completedOrdinaryScalarComplex]
    apply scalarTensor_ext l E E (AlgHom.id ℚ_[l] E) X
    intro U s x
    change (((completedScalarIdentityMultiplication.{u, u} l E X).hom.app P).f i).val.app U
        ((t₀.hom.app
          (P.X i)).val.app U
            (integralOrdinaryTensorSection l E E (AlgHom.id ℚ_[l] E) X (P.X i) U s x)) =
      ((integralOrdinaryScalarUnit l E X).hom.app (P.X i)).val.app U
        (integralOrdinaryTensorSection l E E (AlgHom.id ℚ_[l] E) X (P.X i) U s x)
    rw [ht₀]
    exact ((completedScalarIdentityMultiplication_existsUnique l E X).exists.choose_spec
      P i U s x).trans
      ((integralOrdinaryScalarUnit_existsUnique l E X).exists.choose_spec (P.X i) U s x).symm
  let Q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  apply Localization.natTrans_ext Q W
  intro P
  change e.hom.app (DerivedCategory.Q.obj P.obj) ≫
    (CompletedLineTensor.ordinaryUnit l E X).hom.app (DerivedCategory.Q.obj P.obj) = _
  change _ = (integralOrdinaryDerivedScalarUnit l E X).hom.app
    (DerivedCategory.Q.obj P.obj)
  have hunit := (CompletedLineTensor.ordinaryUnit_existsUnique l E X).exists.choose_spec P
  change (CompletedLineTensor.ordinaryUnit l E X).hom.app _ = _ at hunit
  rw [hunit]
  rw [← Category.assoc, he, Category.assoc, ← Functor.map_comp, hchain]
  let A := integralTowerModules l E X
  have hid : (Functor.mapDerivedCategoryIdIso A).hom.app (DerivedCategory.Q.obj P.obj) =
      (𝟭 A).mapDerivedCategoryFactors.hom.app P.obj := by
    have h := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj A
      ((HomotopyCategory.quotient A (.up ℤ)).obj P.obj)
    rw [Functor.mapDerivedCategoryFactorsh_hom_app] at h
    have h₁ : (DerivedCategory.quotientCompQhIso A).hom.app P.obj = 𝟙 _ := rfl
    have h₂ : (DerivedCategory.quotientCompQhIso A).inv.app
        (((𝟭 A).mapHomologicalComplex (.up ℤ)).obj P.obj) = 𝟙 _ := rfl
    have h₃ : ((𝟭 A).mapHomotopyCategoryFactors (.up ℤ)).inv.app P.obj = 𝟙 _ := rfl
    rw [h₁, h₂, h₃] at h
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
      Category.comp_id, Category.comp_id] at h
    exact h
  dsimp only [integralOrdinaryDerivedScalarUnit, Iso.trans_hom, NatTrans.comp_app]
  rw [hid]
  exact (Functor.mapDerivedCategoryNatIso_fac (integralOrdinaryScalarUnit l E X) P.obj).symm

private theorem scalarModelSheaf_associator
    (l : ℕ) [Fact l.Prime]
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (X : Scheme.{u})
    (tEL : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (htEL : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (tEL.hom.app N).val.app U
          (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection.{u, u} l E L ι X N U s x)
    (tLM : integralOrdinaryScalar l L M j X ≅
      completedOrdinaryScalarExtension.{u, u} l L M j X)
    (htLM : ∀ (N : integralTowerModules l L X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l M X).obj.obj U)
      (x : N.val.obj U),
      (tLM.hom.app N).val.app U
          (integralOrdinaryTensorSection l L M j X N U s x) =
        completedScalarTensorSection.{u, u} l L M j X N U s x)
    (tEM : integralOrdinaryScalar l E M (j.comp ι) X ≅
      completedOrdinaryScalarExtension.{u, u} l E M (j.comp ι) X)
    (htEM : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l M X).obj.obj U)
      (x : N.val.obj U),
      (tEM.hom.app N).val.app U
          (integralOrdinaryTensorSection l E M (j.comp ι) X N U s x) =
        completedScalarTensorSection.{u, u} l E M (j.comp ι) X N U s x)
    :
    Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι X)
        tLM ≪≫
      Functor.isoWhiskerRight tEL
        (completedOrdinaryScalarExtension.{u, u} l L M j X) ≪≫
      (CompletedLineTensor.associatorData l E X L ι M j).sheaf =
    integralOrdinaryScalarComp l E L ι X M j ≪≫
      tEM := by
  let a := Functor.isoWhiskerLeft (integralOrdinaryScalar l E L ι X)
      tLM ≪≫
    Functor.isoWhiskerRight tEL
      (completedOrdinaryScalarExtension.{u, u} l L M j X) ≪≫
    (CompletedLineTensor.associatorData l E X L ι M j).sheaf
  let t := tEM
  have h : a ≪≫ t.symm = integralOrdinaryScalarComp l E L ι X M j := by
    apply (integralOrdinaryScalarComp_existsUnique l E L ι X M j).unique
    · intro N U c b x
      have ht (z : N.val.obj U)
          (d : (completedIntegralCommRingSheafUnrestricted l M X).obj.obj U) :
          (t.inv.app N).val.app U
              (completedScalarTensorSection.{u, u} l E M (j.comp ι) X N U d z) =
            integralOrdinaryTensorSection l E M (j.comp ι) X N U d z := by
        have hh := htEM N U d z
        have hh' := congrArg ((t.inv.app N).val.app U) hh
        change ((t.hom.app N ≫ t.inv.app N).val.app U)
          (integralOrdinaryTensorSection l E M (j.comp ι) X N U d z) = _ at hh'
        simpa only [Iso.hom_inv_id_app, SheafOfModules.id_val,
          PresheafOfModules.id_app, ModuleCat.id_apply] using hh'.symm
      change (t.inv.app N).val.app U
        (((CompletedLineTensor.associatorData l E X L ι M j).sheaf.hom.app N).val.app U
          (((completedOrdinaryScalarExtension.{u, u} l L M j X).map
            (tEL.hom.app N)).val.app U
            ((tLM.hom.app
              ((integralOrdinaryScalar l E L ι X).obj N)).val.app U
                (integralOrdinaryTensorSection l L M j X _ U c
                  (integralOrdinaryTensorSection l E L ι X N U b x))))) = _
      rw [htLM, completedScalarTensorSection_naturality, htEL]
      have hnorm := (CompletedLineTensor.associatorData_existsUnique l E X L ι M j)
        |>.exists.choose_spec.1 N U b c x
      change ((CompletedLineTensor.associatorData l E X L ι M j).sheaf.hom.app N).val.app U
        (completedScalarTensorSection.{u, u} l L M j X _ U c
          (completedScalarTensorSection.{u, u} l E L ι X N U b x)) = _ at hnorm
      rw [hnorm]
      rw [ht, scalarMap_eq_completed]
    · exact (integralOrdinaryScalarComp_existsUnique l E L ι X M j).exists.choose_spec
  have hh := congrArg (fun z ↦ z ≪≫ t) h
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using hh

private theorem scalarModelComparison_associator
    (l : ℕ) [Fact l.Prime]
    (E L M : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    [Field M] [Algebra ℚ_[l] M] [FiniteDimensional ℚ_[l] M]
    (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M) (X : Scheme.{u})
    (tEL : integralOrdinaryScalar l E L ι X ≅
      completedOrdinaryScalarExtension.{u, u} l E L ι X)
    (htEL : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l L X).obj.obj U)
      (x : N.val.obj U),
      (tEL.hom.app N).val.app U
          (integralOrdinaryTensorSection l E L ι X N U s x) =
        completedScalarTensorSection.{u, u} l E L ι X N U s x)
    (tLM : integralOrdinaryScalar l L M j X ≅
      completedOrdinaryScalarExtension.{u, u} l L M j X)
    (htLM : ∀ (N : integralTowerModules l L X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l M X).obj.obj U)
      (x : N.val.obj U),
      (tLM.hom.app N).val.app U
          (integralOrdinaryTensorSection l L M j X N U s x) =
        completedScalarTensorSection.{u, u} l L M j X N U s x)
    (tEM : integralOrdinaryScalar l E M (j.comp ι) X ≅
      completedOrdinaryScalarExtension.{u, u} l E M (j.comp ι) X)
    (htEM : ∀ (N : integralTowerModules l E X) (U : X.ProEtᵒᵖ)
      (s : (completedIntegralCommRingSheafUnrestricted l M X).obj.obj U)
      (x : N.val.obj U),
      (tEM.hom.app N).val.app U
          (integralOrdinaryTensorSection l E M (j.comp ι) X N U s x) =
        completedScalarTensorSection.{u, u} l E M (j.comp ι) X N U s x)
    (eEL : integralOrdinaryDerivedScalar l E L ι X ≅
      completedDerivedScalarExtension.{u, u} l E L ι X)
    (eLM : integralOrdinaryDerivedScalar l L M j X ≅
      completedDerivedScalarExtension.{u, u} l L M j X)
    (eEM : integralOrdinaryDerivedScalar l E M (j.comp ι) X ≅
      completedDerivedScalarExtension.{u, u} l E M (j.comp ι) X)
    (heEL : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      eEL.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E L ι X P =
        (integralOrdinaryScalar l E L ι X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex tEL
              (.up ℤ)).hom.app P))
    (heLM : ∀ P : CochainComplex (integralTowerModules l L X) ℤ,
      eLM.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l L M j X P =
        (integralOrdinaryScalar l L M j X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex tLM
              (.up ℤ)).hom.app P))
    (heEM : ∀ P : CochainComplex (integralTowerModules l E X) ℤ,
      eEM.hom.app (DerivedCategory.Q.obj P) ≫ completedScalarCounit.{u, u} l E M (j.comp ι) X P =
        (integralOrdinaryScalar l E M (j.comp ι) X).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex tEM
              (.up ℤ)).hom.app P)) :
    Functor.isoWhiskerLeft (integralOrdinaryDerivedScalar l E L ι X) eLM ≪≫
      Functor.isoWhiskerRight eEL (completedDerivedScalarExtension.{u, u} l L M j X) ≪≫
      (CompletedLineTensor.associatorData l E X L ι M j).derived =
    integralOrdinaryDerivedScalarComp l E L ι X M j ≪≫ eEM := by
  let Fa := integralOrdinaryScalar l E L ι X
  let Fb := integralOrdinaryScalar l L M j X
  let Fc := integralOrdinaryScalar l E M (j.comp ι) X
  let Cb := completedDerivedScalarExtension.{u, u} l L M j X
  let ta := NatIso.mapHomologicalComplex tEL (.up ℤ)
  let tb := NatIso.mapHomologicalComplex tLM (.up ℤ)
  let tc := NatIso.mapHomologicalComplex tEM (.up ℤ)
  let ac := CompletedLineTensor.scalarAssociatorComplex l E X L ι M j
    (CompletedLineTensor.associatorData l E X L ι M j).sheaf
  let ao := Functor.mapHomologicalComplexCompIso
    (integralOrdinaryScalarComp l E L ι X M j) (.up ℤ)
  let ad := (CompletedLineTensor.associatorData l E X L ι M j).derived
  let od := integralOrdinaryDerivedScalarComp l E L ι X M j
  have hchain (P : CochainComplex (integralTowerModules l E X) ℤ) :
      tb.hom.app ((Fa.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (completedOrdinaryScalarComplex.{u, u} l L M j X).map (ta.hom.app P) ≫
        ac.hom.app P = ao.hom.app P ≫ tc.hom.app P := by
    ext i : 1
    have h := congrArg (fun z ↦ z.hom.app (P.X i))
      (scalarModelSheaf_associator l E L M ι j X tEL htEL tLM htLM tEM htEM)
    change tLM.hom.app
        ((integralOrdinaryScalar l E L ι X).obj (P.X i)) ≫
      (completedOrdinaryScalarExtension.{u, u} l L M j X).map
        (tEL.hom.app (P.X i)) ≫
      (CompletedLineTensor.associatorData l E X L ι M j).sheaf.hom.app (P.X i) =
      (integralOrdinaryScalarComp l E L ι X M j).hom.app (P.X i) ≫
        tEM.hom.app (P.X i)
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] using h
  have hfac (P : CochainComplex (integralTowerModules l E X) ℤ) :
      od.hom.app (DerivedCategory.Q.obj P) ≫ Fc.mapDerivedCategoryFactors.hom.app P =
        Fb.mapDerivedCategory.map (Fa.mapDerivedCategoryFactors.hom.app P) ≫
          Fb.mapDerivedCategoryFactors.hom.app ((Fa.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map (ao.hom.app P) := by
    change ((Functor.mapDerivedCategoryCompIso Fa Fb).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso
        (integralOrdinaryScalarComp l E L ι X M j)).hom.app _) ≫ _ = _
    rw [Category.assoc, Functor.mapDerivedCategoryNatIso_fac]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso Fa Fb).inv.app
      (DerivedCategory.Q.obj P))).mp
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simp only [Category.assoc]
    rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
    rfl
  let Q := integralOperationsGoodLocalization l E X
  let W := (HomologicalComplex.quasiIso (integralTowerModules l E X) (.up ℤ)).inverseImage
    (integralOperationsGoodComplex l E X).ι
  let : Q.IsLocalization W := integralOperationsGoodLocalization_isLocalization l E X
  apply Iso.ext
  apply Localization.natTrans_ext Q W
  intro P
  dsimp only [Q, integralOperationsGoodLocalization, Functor.comp_obj]
  have hciso : IsIso (completedScalarCounit.{u, u} l E M (j.comp ι) X P.obj) := by
    rw [← completedScalarCochainModel_counit]
    exact (completedScalarCochainModel.{u, u} l E M (j.comp ι) X).computes P.obj P.property.1
  let := hciso
  apply (cancel_mono (completedScalarCounit.{u, u} l E M (j.comp ι) X P.obj)).mp
  change (eLM.hom.app _ ≫ Cb.map (eEL.hom.app _) ≫ ad.hom.app _) ≫ _ =
    (od.hom.app _ ≫ eEM.hom.app _) ≫ _
  have hnew := (CompletedLineTensor.associatorData_existsUnique l E X L ι M j)
    |>.exists.choose_spec.2 P
  have hnat : Cb.map (DerivedCategory.Q.map (ta.hom.app P.obj)) ≫
        completedScalarCounit.{u, u} l L M j X
          ((completedOrdinaryScalarComplex.{u, u} l E L ι X).obj P.obj) =
      completedScalarCounit.{u, u} l L M j X ((Fa.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map
          ((completedOrdinaryScalarComplex.{u, u} l L M j X).map (ta.hom.app P.obj)) := by
    simpa only [Cb, completedScalarCounit, completedOrdinaryScalarComplex, cast_eq] using
      homotopyCounit_naturality
        (completedOrdinaryScalarExtension.{u, u} l L M j X)
        (completedDerivedScalarExtension.{u, u} l L M j X)
        ((completedScalarChangeData.{u, u} l L M j X).choose_spec.choose_spec.choose_spec
          |>.choose_spec.2.2.choose_spec.choose) (ta.hom.app P.obj)
  change Cb.map (completedScalarCounit.{u, u} l E L ι X P.obj) ≫
    completedScalarCounit.{u, u} l L M j X
      ((completedOrdinaryScalarComplex.{u, u} l E L ι X).obj P.obj) ≫
    DerivedCategory.Q.map (ac.hom.app P.obj) =
    ad.hom.app (DerivedCategory.Q.obj P.obj) ≫
      completedScalarCounit.{u, u} l E M (j.comp ι) X P.obj at hnew
  dsimp only [integralOrdinaryDerivedScalar] at eEL eLM eEM heEL heLM heEM
  calc
    _ = eLM.hom.app _ ≫ Cb.map
        (eEL.hom.app _ ≫ completedScalarCounit.{u, u} l E L ι X P.obj) ≫
        completedScalarCounit.{u, u} l L M j X
          ((completedOrdinaryScalarComplex.{u, u} l E L ι X).obj P.obj) ≫
        DerivedCategory.Q.map (ac.hom.app P.obj) := by
      dsimp only [integralOperationsGoodComplex, ObjectProperty.ι_obj]
      simp only [Category.assoc, ← hnew, Functor.map_comp]
    _ = eLM.hom.app _ ≫ Cb.map (Fa.mapDerivedCategoryFactors.hom.app P.obj) ≫
        Cb.map (DerivedCategory.Q.map (ta.hom.app P.obj)) ≫
        completedScalarCounit.{u, u} l L M j X
          ((completedOrdinaryScalarComplex.{u, u} l E L ι X).obj P.obj) ≫
        DerivedCategory.Q.map (ac.hom.app P.obj) := by
      rw [heEL]
      simp only [Functor.map_comp, Category.assoc, Fa, ta, Functor.comp_obj]
    _ = Fb.mapDerivedCategory.map (Fa.mapDerivedCategoryFactors.hom.app P.obj) ≫
        (eLM.hom.app _ ≫ completedScalarCounit.{u, u} l L M j X
          ((Fa.mapHomologicalComplex (.up ℤ)).obj P.obj)) ≫
        DerivedCategory.Q.map
          ((completedOrdinaryScalarComplex.{u, u} l L M j X).map (ta.hom.app P.obj)) ≫
        DerivedCategory.Q.map (ac.hom.app P.obj) := by
      rw [← eLM.hom.naturality_assoc]
      simp only [Category.assoc, reassoc_of% hnat, Fb, Functor.comp_obj]
    _ = Fb.mapDerivedCategory.map (Fa.mapDerivedCategoryFactors.hom.app P.obj) ≫
        Fb.mapDerivedCategoryFactors.hom.app ((Fa.mapHomologicalComplex (.up ℤ)).obj P.obj) ≫
        DerivedCategory.Q.map (ao.hom.app P.obj ≫ tc.hom.app P.obj) := by
      dsimp only [Functor.comp_obj]
      erw [heLM]
      simp only [Category.assoc, ← Functor.map_comp]
      rw [hchain]
    _ = (od.hom.app _ ≫ eEM.hom.app _) ≫
        completedScalarCounit.{u, u} l E M (j.comp ι) X P.obj := by
      rw [Category.assoc, heEM]
      dsimp only [Fc, tc] at hfac
      rw [reassoc_of% (hfac P.obj)]
      simp only [Functor.map_comp, tc]

/-- The counit-normalized comparison of the ordinary scalar models preserves their
specified completion maps, units and associators.
Source: Stacks 06YY, 0941 and the finite-free tensor normalization.

Proof: the ordinary sheaf models are identified by the identity on pure tensors.
The universal left-derived comparison lifts this identification while preserving
its cochain counit. Both completion comparisons have the same strict quotient
augmentation, including zero shifted coordinate, so uniqueness identifies them.
On tensors the units send s tensor x to sx, and both associators send c tensor
(b tensor x) to c*j(b) tensor x. Tensor generation and uniqueness give the sheaf
equations. On a good complex, the universal counits identify the derived units
and associators with these termwise maps. Their naturality and the factorization
comparisons for exact derived functors preserve the equations. The last counit
is invertible on the K-flat representative, so it can be cancelled. Localization
then gives the equations of natural transformations on all derived objects.
Identity embeddings, equal fields and zero objects satisfy the same formulas.
(blueprint: lem-trf-integral-scalar-ordinary-model-coherence). -/
theorem integralScalarOrdinaryModelCoherence (l : ℕ) [Fact l.Prime] :
    (∀ (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
      (X : Scheme.{u}),
      ∃ e : integralOrdinaryDerivedScalar l E E (AlgHom.id ℚ_[l] E) X ≅
          completedDerivedScalarExtension.{u, u} l E E (AlgHom.id ℚ_[l] E) X,
        (e.hom ≫ completedScalarComparison.{u, u} l E E (AlgHom.id ℚ_[l] E) X =
          scalarCompletion l E E (AlgHom.id ℚ_[l] E) X) ∧
        (e.hom ≫ (CompletedLineTensor.ordinaryUnit l E X).hom =
          (integralOrdinaryDerivedScalarUnit l E X).hom)) ∧
    (∀ (E L M : Type u) [Field E] [Algebra ℚ_[l] E]
      [FiniteDimensional ℚ_[l] E] [Field L] [Algebra ℚ_[l] L]
      [FiniteDimensional ℚ_[l] L] [Field M] [Algebra ℚ_[l] M]
      [FiniteDimensional ℚ_[l] M] (ι : E →ₐ[ℚ_[l]] L) (j : L →ₐ[ℚ_[l]] M)
      (X : Scheme.{u}),
      ∃ (eEL : integralOrdinaryDerivedScalar l E L ι X ≅
            completedDerivedScalarExtension.{u, u} l E L ι X)
        (eLM : integralOrdinaryDerivedScalar l L M j X ≅
            completedDerivedScalarExtension.{u, u} l L M j X)
        (eEM : integralOrdinaryDerivedScalar l E M (j.comp ι) X ≅
            completedDerivedScalarExtension.{u, u} l E M (j.comp ι) X),
        (eEL.hom ≫ completedScalarComparison.{u, u} l E L ι X =
          scalarCompletion l E L ι X) ∧
        (eLM.hom ≫ completedScalarComparison.{u, u} l L M j X =
          scalarCompletion l L M j X) ∧
        (eEM.hom ≫ completedScalarComparison.{u, u} l E M (j.comp ι) X =
          scalarCompletion l E M (j.comp ι) X) ∧
        (Functor.isoWhiskerLeft (integralOrdinaryDerivedScalar l E L ι X) eLM ≪≫
          Functor.isoWhiskerRight eEL (completedDerivedScalarExtension.{u, u} l L M j X) ≪≫
          (CompletedLineTensor.associatorData l E X L ι M j).derived =
          integralOrdinaryDerivedScalarComp l E L ι X M j ≪≫ eEM)) := by
  constructor
  · intro E _ _ _ X
    obtain ⟨t, e, ht, he, hχ⟩ :=
      integralScalarOrdinaryModelComparison l E E (AlgHom.id ℚ_[l] E) X
    exact ⟨e, hχ, scalarModelComparison_unit l E X t ht e he⟩
  · intro E L M _ _ _ _ _ _ _ _ _ ι j X
    obtain ⟨tEL, eEL, htEL, heEL, hχEL⟩ :=
      integralScalarOrdinaryModelComparison l E L ι X
    obtain ⟨tLM, eLM, htLM, heLM, hχLM⟩ :=
      integralScalarOrdinaryModelComparison l L M j X
    obtain ⟨tEM, eEM, htEM, heEM, hχEM⟩ :=
      integralScalarOrdinaryModelComparison l E M (j.comp ι) X
    exact ⟨eEL, eLM, eEM, hχEL, hχLM, hχEM,
      scalarModelComparison_associator l E L M ι j X
        tEL htEL tLM htLM tEM htEM eEL eLM eEM heEL heLM heEM⟩

end WeilConjectures
