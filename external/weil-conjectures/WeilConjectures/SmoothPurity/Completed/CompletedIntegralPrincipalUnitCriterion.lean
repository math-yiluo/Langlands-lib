/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.DerivedCompleteUnrestricted
public import WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Data.Nat.Prime.Infinite

/-! # The principal quotient unit for completed integral coefficients

Source: Stacks Project, Tags 093M, 099B and 0A0E; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-principal-unit-criterion).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace WeilConjectures

set_option synthInstance.maxSize 4096
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem regularTensorIso_eq
    {A : Type*} [Category A] [EssentiallySmall.{u} A]
    {J : GrothendieckTopology A}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    (R : Sheaf J CommRingCat.{u})
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.IndependentExtensionTensor.regularTensorIso M = λ_ M := by
  apply Iso.ext
  dsimp only [SheafOfModules.IndependentExtensionTensor.regularTensorIso,
    SheafOfModules.tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, tensorIso_inv, Iso.app_inv, asIso_inv]
  simp only [Functor.Monoidal.μIso_hom, Functor.Monoidal.map_leftUnitor,
    Category.assoc]
  let F := PresheafOfModules.sheafification
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)
  let e := asIso (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).counit
  change (e.app (SheafOfModules.unit _) ⊗ᵢ e.app M).inv ≫
    Functor.LaxMonoidal.μ F (𝟙_ _) M.val ≫
    Functor.OplaxMonoidal.δ F (𝟙_ _) M.val ≫
    (SheafOfModules.sheafificationObjUnitIso R).hom ▷ F.obj M.val ≫
    (λ_ (F.obj M.val)).hom ≫ (e.app M).hom = _
  rw [Functor.Monoidal.μ_δ_assoc]
  simp only [SheafOfModules.sheafificationObjUnitIso, tensorIso_inv, tensorHom_def',
    Category.assoc, ← leftUnitor_naturality]
  change (𝟙_ _) ◁ (e.app M).inv ≫
    (e.app (SheafOfModules.unit _)).inv ▷ F.obj M.val ≫
    (e.app (SheafOfModules.unit _)).hom ▷ F.obj M.val ≫
    (𝟙_ _) ◁ (e.app M).hom ≫ (λ_ M).hom = _
  simp only [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight,
    Category.id_comp, ← whiskerLeft_comp_assoc, whiskerLeft_id]

private theorem extension_unit_comparison
    {A : Type*} [Category A] [EssentiallySmall.{u} A]
    {J : GrothendieckTopology A}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S)
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    ∃ e : (SheafOfModules.RegularQuotientCone.restriction φ).obj
        (SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J S)) ⊗ M ≅
        (SheafOfModules.RegularQuotientCone.restriction φ).obj
          (SheafOfModules.changeOfRings φ M),
      ∀ (U : Aᵒᵖ) (x : M.val.obj U),
        (((λ_ M).inv ≫ SheafOfModules.RegularQuotientCone.ringMap φ ▷ M ≫ e.hom).val.app U) x =
          (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
            ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
  obtain ⟨s, hs⟩ :=
    SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M
  refine ⟨s, ?_⟩
  intro U x
  rw [← regularTensorIso_eq R M]
  change s.hom.val.app U
    ((SheafOfModules.RegularQuotientCone.ringMap φ ▷ M).val.app U
      ((SheafOfModules.IndependentExtensionTensor.regularTensorIso M).inv.val.app U x)) = _
  rw [SheafOfModules.IndependentExtensionTensor.regularTensorIso_inv_apply]
  rw [SheafOfModules.IndependentExtensionTensor.tensorPresheafUnit_whiskerRight_apply]
  have h1 : (SheafOfModules.RegularQuotientCone.ringMap φ).val.app U (1 : R.obj.obj U) =
      (show ((SheafOfModules.RegularQuotientCone.restriction φ).obj
        (SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J S))).val.obj U
        from (1 : S.obj.obj U)) := by
    change (φ.hom.app U).hom 1 * 1 = 1
    rw [map_one, one_mul]
  rw [h1]
  exact hs U 1 x

section GeneralQuotient

variable {S : Type v} [Category S] [EssentiallySmall.{u} S]
  {J : GrothendieckTopology S}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
  (a : (SheafOfModules.unit
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)

private local instance quotientWeakSheafify : HasWeakSheafify J AddCommGrpCat.{u} :=
  HasSheafify.isRightAdjoint

local notation "A" => SheafOfModules.RegularQuotientCone.Modules R

private local instance quotientFiniteBiproducts : HasFiniteBiproducts A :=
  Abelian.hasFiniteBiproducts

private local instance quotientBinaryBiproducts : HasBinaryBiproducts A :=
  hasBinaryBiproducts_of_finite_biproducts A

private local instance (priority := 1100) quotientCountableProducts : HasCountableProducts A where
  out D := SheafOfModules.hasLimitsOfShape.{u} (D := Discrete D)
    (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R)

-- Fix the degreewise product instance before constructing Roos cones.
private local instance (priority := 1100) quotientComplexProducts
    (H : ℕ → CochainComplex A ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{u} (D := Discrete ℕ)
      (R := SheafOfModules.derivedChangeRingIndependentCoefficients J R))).has_limit
        (Discrete.functor H)

private theorem single_tensor_quotient_component
    (P : CochainComplex A ℤ) (n : ℕ) (i : ℤ) :
    (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫
        (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A)
          (principalQuotient R a n) P).hom.f i =
      (λ_ (P.X i)).inv ≫
        cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)) ▷ P.X i := by
  apply (cancel_mono
    ((CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A)
      (principalQuotient R a n) P).inv.f i)).1
  simp only [Category.assoc, ← HomologicalComplex.comp_f, Iso.hom_inv_id,
    Category.comp_id]
  simp only [PrincipalQuotientCompletion.quotientMap, koszulRepresentativeQuotient,
    HomologicalComplex.comp_f, koszulTensorUnitInclusion, koszulTensorUnitComponent,
    koszulTensorFunctor, Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f, Category.assoc]
  erw [HomologicalComplex.ι_mapBifunctorMap]
  simp only [CochainComplex.singleFunctor,
    HomologicalComplex.single_map_f_self,
    HomologicalComplex.id_f, curriedTensor_map_app, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id_assoc]
  dsimp only [curriedTensor_obj_map]
  simp only [whiskerLeft_id]
  rfl

private theorem quotient_map_epi
    (P : CochainComplex A ℤ) (n : ℕ) (i : ℤ) :
    Epi ((PrincipalQuotientCompletion.quotientMap R a P n).f i) := by
  have h := single_tensor_quotient_component R a P n i
  let := SheafOfModules.symmetricCategory R
  have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R (P.X i)
  have : PreservesColimitsOfSize.{0, 0} (tensorLeft (P.X i)) :=
    preservesColimitsOfSize_shrink _
  have : PreservesColimitsOfSize.{0, 0} (tensorRight (P.X i)) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
  have : Epi ((tensorRight (P.X i)).map
      (cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)))) :=
    Functor.map_epi _ _
  have he : Epi ((λ_ (P.X i)).inv ≫
      cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)) ▷ P.X i) := by
    exact epi_comp _ ((tensorRight (P.X i)).map _)
  rw [← h] at he
  let := he
  exact (epi_comp_iff_of_isIso _ _).1 he

private theorem quotient_transition
    (P : CochainComplex A ℤ) (n : ℕ) :
    PrincipalQuotientCompletion.quotientMap R a P (n + 1) ≫
        (((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor.map
          (homOfLE (Nat.le_succ n)).op) =
      PrincipalQuotientCompletion.quotientMap R a P n := by
  change koszulRepresentativeQuotient R P a (n + 1) ≫
    (koszulTensorFunctor R P).map
      ((principalReductionTower R a).map (homOfLE (Nat.le_succ n)).op) = _
  dsimp only [principalReductionTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  simp only [koszulRepresentativeQuotient, principalReductionTransition,
    Category.assoc, ← Functor.map_comp, cokernel.π_desc]
  rfl

private theorem quotient_tower_comparison
    (P : CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (hlevel : ∀ n i, ∃ e :
      (((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor.obj (op n)).X i ≅
        (T.obj (op n)).X i,
      (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫ e.hom =
        (γ.app (op n)).f i) :
    ∃ e : ((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor ≅
        T,
      ∀ n, PrincipalQuotientCompletion.quotientMap R a P n ≫ e.hom.app (op n) =
        γ.app (op n) := by
  classical
  let e (n : ℕ) (i : ℤ) := (hlevel n i).choose
  have he (n : ℕ) (i : ℤ) := (hlevel n i).choose_spec
  let c (n : ℕ) :
      (((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor.obj (op n)) ≅
        T.obj (op n) :=
    HomologicalComplex.Hom.isoOfComponents (e n) (by
      intro i j hij
      let := quotient_map_epi R a P n i
      apply (cancel_epi ((PrincipalQuotientCompletion.quotientMap R a P n).f i)).1
      rw [← Category.assoc, he]
      erw [(PrincipalQuotientCompletion.quotientMap R a P n).comm_assoc i j,
        he, HomologicalComplex.Hom.comm]
      rfl)
  have hc (n : ℕ) : PrincipalQuotientCompletion.quotientMap R a P n ≫
      (c n).hom = γ.app (op n) := by
    ext i : 1
    exact he n i
  let f : ((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor ⟶
      T :=
    NatTrans.ofOpSequence (fun n ↦ (c n).hom) (by
      intro n
      ext i : 1
      let := quotient_map_epi R a P (n + 1) i
      apply (cancel_epi
        ((PrincipalQuotientCompletion.quotientMap R a P (n + 1)).f i)).1
      change ((PrincipalQuotientCompletion.quotientMap R a P (n + 1)) ≫ _ ≫ _).f i =
        ((PrincipalQuotientCompletion.quotientMap R a P (n + 1)) ≫ _ ≫ _).f i
      rw [← Category.assoc, quotient_transition R a, hc,
        ← Category.assoc, hc]
      exact congrArg (fun k ↦ k.f i)
        ((γ.naturality (homOfLE (Nat.le_succ n)).op).symm.trans
          (Category.id_comp _)).symm)
  have : ∀ n, IsIso (f.app n) := fun n ↦ by
    change IsIso (c n.unop).hom
    infer_instance
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact ⟨asIso f, hc⟩

private theorem quotient_roos_comparison
    [HasDerivedCategory.{w} A] (C : PrincipalQuotientCompletion.Model R a)
    (P : CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (γ : (Functor.const ℕᵒᵖ).obj P ⟶ T)
    (e : ((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor ≅ T)
    (he : ∀ n, PrincipalQuotientCompletion.quotientMap R a P n ≫ e.hom.app (op n) =
      γ.app (op n))
    (δ : P ⟶ integralOperationsRoos T)
    (hδ : ∀ p : ℤ, δ.f (p + 1) ≫ (roosχ (koszulTowerComplex R T) p).hom =
      biprod.lift (0 : P.X (p + 1) ⟶ (roosP (koszulTowerComplex R T)).X p)
        ((Pi.lift (fun n : ℕ ↦ γ.app (op n)) :
          P ⟶ roosP (koszulTowerComplex R T)).f (p + 1))) :
    ∃ e : (PrincipalQuotientCompletion.quotientRoos R a).obj P ≅
        integralOperationsRoos T,
      C.augmentation P ≫ e.hom = δ := by
  classical
  let et : (PrincipalQuotientCompletion.quotientTower R a).obj P ≅
      koszulTowerComplex R T :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i ↦ NatIso.ofComponents
        (fun n ↦ (HomologicalComplex.eval A (.up ℤ) i).mapIso (e.app n))
        (by
          intro n m f
          exact congrArg (fun k ↦ k.f i) (e.hom.naturality f)))
      (by
        intro i j hij
        apply NatTrans.ext
        funext n
        exact (e.hom.app n).comm i j)
  let s := roosF.mapIso et
  refine ⟨s, ?_⟩
  have hp : PrincipalQuotientCompletion.quotientProduct R a P ≫ roosPmap et.hom =
      Pi.lift (fun n : ℕ ↦ γ.app (op n)) := by
    apply Pi.hom_ext
    intro n
    dsimp only [PrincipalQuotientCompletion.quotientProduct, roosPmap]
    erw [Category.assoc, Pi.map_π, Pi.lift_comp_π_assoc, Pi.lift_comp_π]
    exact he n
  ext i : 1
  obtain ⟨p, rfl⟩ : ∃ p : ℤ, i = p + 1 := ⟨i - 1, by omega⟩
  apply (cancel_mono (roosχ (koszulTowerComplex R T) p).hom).1
  change ((C.augmentation P).f (p + 1) ≫ (roosF.map et.hom).f (p + 1)) ≫ _ = _
  erw [Category.assoc, roosF_map_χ, ← Category.assoc, C.coordinates]
  erw [hδ]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.map_fst, biprod.lift_fst_assoc,
      biprod.lift_fst, zero_comp]
  · simp only [Category.assoc, biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd]
    exact congrArg (fun k ↦ k.f (p + 1)) hp

private theorem roos_zero_of_condition
    (P : CochainComplex A ℤ) (T : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (α : P ⟶ ∏ᶜ (fun n : ℕ ↦ T.obj (op n)))
    (h : CochainComplex.HomComplex.δ (-1) 0
        (0 : CochainComplex.HomComplex.Cochain P (∏ᶜ (fun n : ℕ ↦ T.obj (op n))) (-1)) +
      CochainComplex.HomComplex.Cochain.ofHom
        (α ≫ towerTransitionEndomorphism (integralOperationsTowerStep T)) = 0) :
    α ≫ roosU (koszulTowerComplex R T) = 0 := by
  have h0 : α ≫ towerTransitionEndomorphism (integralOperationsTowerStep T) = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    simp only [CochainComplex.HomComplex.δ_zero, zero_add] at h
    have hi := congrArg (fun z ↦ z.v i i (add_zero i)) h
    simpa only [CochainComplex.HomComplex.Cochain.ofHom_v,
      CochainComplex.HomComplex.Cochain.zero_v, HomologicalComplex.comp_f,
      HomologicalComplex.zero_f] using hi
  exact h0

end GeneralQuotient

section QuotientComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})

private local instance integralSiteSmall : EssentiallySmall.{max u (t + 1)} Y.ProEt :=
  essentiallySmallSelf _
private local instance integralAbSheafify :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify Y
private local instance integralAbWeakSheafify :
    HasWeakSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
    AddCommGrpCat.{max u (t + 1)} := HasSheafify.isRightAdjoint
private local instance integralAbLocallyBijective :
    (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective Y

local notation "R" => completedIntegralCommRingSheafUnrestricted l E Y
local notation "a" => PrincipalKoszulStrictReplacement.uniformizer l E Y
local notation "A" => integralTowerModules l E Y

private local instance integralFiniteBiproducts : HasFiniteBiproducts A :=
  Abelian.hasFiniteBiproducts

private local instance integralBinaryBiproducts : HasBinaryBiproducts A :=
  hasBinaryBiproducts_of_finite_biproducts A

private local instance (priority := 1100) integralCountableProducts : HasCountableProducts A where
  out D := SheafOfModules.hasLimitsOfShape.{max u (t + 1)} (D := Discrete D)
    («R» := completedIntegralCoefficientSheafUnrestricted l E Y)

private local instance (priority := 1100) integralComplexProducts
    (H : ℕ → CochainComplex A ℤ) : HasProduct H :=
  (@HomologicalComplex.instHasLimitsOfShape _ ℤ (Discrete ℕ) _ _ (.up ℤ) _
    (SheafOfModules.hasLimitsOfShape.{max u (t + 1)} (D := Discrete ℕ)
      («R» := completedIntegralCoefficientSheafUnrestricted l E Y))).has_limit
        (Discrete.functor H)

private theorem quotient_level_comparison
    (P : CochainComplex A ℤ) (n : ℕ) (i : ℤ) :
    ∃ e : (((PrincipalQuotientCompletion.quotientTower R a).obj P).asFunctor.obj (op n)).X i ≅
        (((IntegralOnSlice.tower l E Y none).obj P).obj (op n)).X i,
      (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫ e.hom =
        (((IntegralOnSlice.augmentation l E Y none).app P).app (op n)).f i := by
  classical
  have hq := (PrincipalKoszulStrictReplacement.completed_exact l E Y n).2
  let := hq
  let φ := IntegralOnSlice.projection l E Y none n
  let V := SheafOfModules.RegularQuotientCone.restriction.{t + 1, t, max u (t + 1)} φ
  obtain ⟨s, hs⟩ := extension_unit_comparison φ (P.X i)
  let b := (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor A)
    (principalQuotient R a n) P)
  let ec := (HomologicalComplex.eval A (.up ℤ) i).mapIso b
  let eq := (tensorRight (P.X i)).mapIso
    (asIso (PrincipalKoszulStrictReplacement.quotientComparison l E Y n))
  let er := V.mapIso (eqToIso (IntegralOnSlice.reduction_obj l E Y none n (P.X i))).symm
  let e := ec ≪≫ eq ≪≫ s ≪≫ er
  refine ⟨e, ?_⟩
  change (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫
    ec.hom ≫ eq.hom ≫ s.hom ≫ er.hom = _
  have hb := single_tensor_quotient_component R a P n i
  change (PrincipalQuotientCompletion.quotientMap R a P n).f i ≫ ec.hom = _ at hb
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hb]
  have hπ : cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)) ≫
      PrincipalKoszulStrictReplacement.quotientComparison l E Y n =
        PrincipalKoszulStrictReplacement.projection l E Y n := cokernel.π_desc _ _ _
  change ((λ_ (P.X i)).inv ≫
      cokernel.π (endoPow (globalSectionMultiplication R a) (n + 1)) ▷ P.X i) ≫
        (PrincipalKoszulStrictReplacement.quotientComparison l E Y n ▷ P.X i) ≫
          s.hom ≫ er.hom = _
  rw [Category.assoc, ← comp_whiskerRight_assoc, hπ]
  have hprojection : PrincipalKoszulStrictReplacement.projection l E Y n =
      SheafOfModules.RegularQuotientCone.ringMap φ := by
    ext U
    rfl
  rw [hprojection]
  apply (cancel_mono er.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  ext U x
  have hu := (IntegralOnSlice.augmentation_existsUnique l E Y none).exists.choose_spec
    P n i U x
  change _ = IntegralOnSlice.generator l E Y none n (P.X i) U 1 x at hu
  change _ = (er.inv.val.app U)
    (((((IntegralOnSlice.augmentation l E Y none).app P).app (op n)).f i).val.app U x)
  change (((((IntegralOnSlice.augmentation l E Y none).app P).app (op n)).f i).val.app U x) =
    IntegralOnSlice.generator l E Y none n (P.X i) U 1 x at hu
  erw [hu]
  change _ = (eqToHom (IntegralOnSlice.reduction_obj l E Y none n (P.X i))).val.app U
    (IntegralOnSlice.generator l E Y none n (P.X i) U 1 x)
  simp only [IntegralOnSlice.generator, ← CategoryTheory.comp_apply,
    ← PresheafOfModules.comp_app, ← SheafOfModules.comp_val, eqToHom_trans,
    eqToHom_refl, SheafOfModules.id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  exact hs U x

private theorem integral_product_zero (P : CochainComplex A ℤ) :
    IntegralOnSlice.productAugmentation l E Y none P ≫
      roosU (koszulTowerComplex R ((IntegralOnSlice.tower l E Y none).obj P)) = 0 := by
  exact roos_zero_of_condition R P ((IntegralOnSlice.tower l E Y none).obj P)
    (IntegralOnSlice.productAugmentation l E Y none P)
    (IntegralOnSlice.roosUnit_condition l E Y none P)

private theorem integral_unit_computes (P : (IntegralOnSlice.Good l E Y none).FullSubcategory) :
    (IntegralOnSlice.completionUnit l E Y none).app (DerivedCategory.Q.obj P.obj) ≫
      (IntegralOnSlice.completionComparison l E Y none).hom.app P =
        DerivedCategory.Q.map (IntegralOnSlice.roosUnit l E Y none P.obj) := by
  exact (IntegralOnSlice.completionUnit_existsUnique l E Y none).exists.choose_spec P

end QuotientComparison

attribute [local irreducible] IntegralOnSlice.completion IntegralOnSlice.completionComparison
  IntegralOnSlice.completionUnit PrincipalQuotientCompletion.quotientRoos

/-- Every normalized principal quotient completion computes the same complete locus.

Source: Stacks Project, Tags 093M, 099B and 0A0E; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-principal-unit-criterion).

Proof: pass to the canonical small model of the pro-etale site in the coefficient
universe. Restriction is an exact equivalence of module categories, preserves all
products, and transports the uniformizer and its multiplication map. The completed
quotient comparison identifies the cokernel of its (n+1)-st power with the actual
constant residue sheaf; it identifies the quotient maps and all transitions, not
just the objects. On a flat K-flat representative tensor this presentation with the
representative. Exact countable products carry the resulting levelwise quasi-isomorphisms
to the signed Roos cones, with their zero shifted coordinate augmentations. Apply the
regular quotient completion unit criterion on the small model. Its normalized Roos
triangle condition is precisely the defining condition of IsDerivedComplete, after
transport along the resolution map and the representative isomorphism. The auxiliary
finite-field datum is absent from every ring and map in this calculation. The criterion
makes the specified unit invertible exactly on that locus and makes its output complete.
The universal left-derived property compares any supplied Model with this quotient
construction, preserving its counit and unit on K-flat representatives; localization
extends both equations to all objects. This proves the assertion for the supplied Model.
The argument includes the zero complex and the empty scheme and needs no
boundedness or constructibility assumption. -/
theorem completedIntegralPrincipalUnitCriterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (integralTowerHasDerivedCategory l E Y)
      (PrincipalKoszulStrictReplacement.uniformizer l E Y)) :
    ∀ K : DerivedCategory (integralTowerModules l E Y),
      IsDerivedCompleteUnrestricted l E Y K ↔ IsIso (C.unit.app K) := by
  classical
  intro K
  let := integralFiniteBiproducts l E Y
  let := integralBinaryBiproducts l E Y
  let := integralCountableProducts l E Y
  have (H : ℕ → CochainComplex (integralTowerModules l E Y) ℤ) : HasProduct H :=
    integralComplexProducts l E Y H
  let := IntegralOnSlice.goodLocalization l E Y none
  let := Localization.essSurj (IntegralOnSlice.qGood l E Y none)
    ((HomologicalComplex.quasiIso (IntegralOnSlice.Mod l E Y none) (.up ℤ)).inverseImage
      (IntegralOnSlice.Good l E Y none).ι)
  let P := (IntegralOnSlice.qGood l E Y none).objPreimage K
  let e : (DerivedCategory.Q (C := integralTowerModules l E Y)).obj P.obj ≅ K :=
    (IntegralOnSlice.qGood l E Y none).objObjPreimageIso K
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨d, hd, _⟩ := PrincipalKoszulStrictReplacement.coefficient_datum l E
  have h := (roosIntrinsicCompletenessEquivalence p l (by omega) E Y d hd K P e).out 1 5
  change IsDerivedCompleteUnrestricted l E Y K ↔
    IsIso ((IntegralOnSlice.completionUnit l E Y none).app K) at h
  rw [h]
  obtain ⟨et, het⟩ := quotient_tower_comparison
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (PrincipalKoszulStrictReplacement.uniformizer l E Y) P.obj _
    ((IntegralOnSlice.augmentation l E Y none).app P.obj)
    (quotient_level_comparison l E Y P.obj)
  obtain ⟨s, hs⟩ := quotient_roos_comparison
    (completedIntegralCommRingSheafUnrestricted l E Y)
    (PrincipalKoszulStrictReplacement.uniformizer l E Y) C P.obj _ _ et het
    (IntegralOnSlice.roosUnit l E Y none P.obj)
    (fun p ↦ roosLift_χ
      (X := koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E Y)
        ((IntegralOnSlice.tower l E Y none).obj P.obj))
      (IntegralOnSlice.productAugmentation l E Y none P.obj)
      (integral_product_zero l E Y P.obj) p)
  -- Naturality transports invertibility from this flat K-flat representative.
  rw [← NatTrans.isIso_app_iff_of_iso (IntegralOnSlice.completionUnit l E Y none) e,
    ← NatTrans.isIso_app_iff_of_iso C.unit e]
  have := C.computes P.obj P.property.1
  let Q := DerivedCategory.Q (C := integralTowerModules l E Y)
  have hu := integral_unit_computes l E Y P
  have hc := (Category.assoc (C.unit.app (Q.obj P.obj))
    (C.counit.app P.obj) (Q.map s.hom)).symm.trans
      ((congrArg (fun f ↦ f ≫ Q.map s.hom) (C.unit_computes P.obj)).trans
        ((Q.map_comp (C.augmentation P.obj) s.hom).symm.trans (congrArg Q.map hs)))
  rw [← isIso_comp_right_iff _
    ((IntegralOnSlice.completionComparison l E Y none).hom.app P), hu,
    ← isIso_comp_right_iff _ (C.counit.app P.obj ≫ Q.map s.hom), hc]

end WeilConjectures
