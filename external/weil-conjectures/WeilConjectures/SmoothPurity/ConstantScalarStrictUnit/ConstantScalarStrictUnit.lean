/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionUniverses
public import WeilConjectures.SmoothPurity.Integral.Reduction.IntegralReductionTowerCanonical
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

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

/-! # The normalized strict scalar unit of the regular completed coefficient complex

Source: Bhatt--Scholze, Definition 3.5.2 and Lemma 6.8.2(1), and the agent-written
regular-module and strict-cone calculation extracted from blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit).

Positive exponent m is indexed by n = m-1. The recorded interface is retained;
site objects have universe t+1, morphisms t, and coefficients max u (t+1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 512
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe d t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.ConstantScalarStrictUnit

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (Y : Scheme.{t})

/-- The single regular complex R_E[0]. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev regularComplex :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).obj
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- Its degree-zero identification. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev regularZeroIso :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y))

/-- A section in degree zero. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def regularSection (V : Y.ProEt)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V)) :
    ((regularComplex l E Y).X 0).val.obj (op V) :=
  (regularZeroIso l E Y).inv.val.app (op V) r

/-- The finite regular single complex. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev finiteRegularComplex (n : ℕ) :=
  (CochainComplex.singleFunctor (integralOperationsFiniteModules l E Y n) 0).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- Its degree-zero identification. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
abbrev finiteZeroIso (n : ℕ) :=
  HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

/-- The linear limit projection, given by the section one of its restricted target.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def projectionModule (n : ℕ) :
    SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y) ⟶
      (scalarReductionRestriction l E Y n).obj
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n)) :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk
      (fun U ↦ (1 : (integralCoefficientSheaf l E Y n).obj.obj U))
      (fun {_ _} f ↦ map_one ((integralCoefficientSheaf l E Y n).obj.map f).hom))

/-- The same projection as a single-complex map with restriction transport.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def projectionComplex (n : ℕ) :
    regularComplex l E Y ⟶
      ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).obj
        (finiteRegularComplex l E Y n) :=
  (CochainComplex.singleFunctor (integralTowerModules l E Y) 0).map
      (projectionModule l E Y n) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (scalarReductionRestriction l E Y n) (ComplexShape.up ℤ) 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E Y n))

variable (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L)

/-- The strict scalar tower's termwise 1-s. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def boundary :=
  towerTransitionEndomorphism
    (K := fun n ↦ ((integralScalarTowerFunctor l E L ι Y).obj
      (regularComplex l E Y)).obj (op n))
    (integralOperationsTowerStep
      ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)))

/-- A degree-zero quotient coordinate of the strict first component.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def coordinate
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) (n : ℕ) :=
  η.f 0 ≫ (CochainComplex.mappingCocone.fst (boundary l E Y L ι)).f 0 ≫
    (Pi.π (fun m ↦ ((integralScalarTowerFunctor l E L ι Y).obj
      (regularComplex l E Y)).obj (op m)) n).f 0

/-- Full section normalization. The API orders tensors z tensor r.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def quotientCoordinates
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ (n : ℕ) (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)),
    (coordinate l E Y L ι η n).val.app (op V) (regularSection l L Y V s) =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s)
        (regularSection l E Y V 1)

/-- The equivalent unit-only normalization. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def unitCoordinates
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ (n : ℕ) (V : Y.ProEt),
    (coordinate l E Y L ι η n).val.app (op V) (regularSection l L Y V 1) =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V) 1
        (regularSection l E Y V 1)

/-- Vanishing of the graded shifted component. Source: blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit). -/
def zeroSecondComponent
    (η : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y)) : Prop :=
  ∀ i : ℤ, η.f i ≫
    (CochainComplex.mappingCocone.snd (boundary l E Y L ι)).v i (i - 1) (by omega) = 0

/-- Multiplication, inverse and reduction formulas for the finite tensors.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def finiteMultiplication : Prop :=
    (∃ u : ∀ n : ℕ,
      (integralScalarFiniteComplex l E L ι Y n).obj (regularComplex l E Y) ≅
        finiteRegularComplex l L Y n,
      (∀ (n : ℕ) (V : Y.ProEt)
        (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj (op V))
        (z : (integralCoefficientSheaf l L Y n).obj.obj (op V)),
        (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
          (integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V r)) =
          @Mul.mul ((integralCoefficientCommRingSheaf l L Y n).obj.obj (op V)) _
            ((integralScalarRho l E L ι Y n).hom.app (op V) r) z) ∧
      (∀ (n : ℕ) (V : Y.ProEt)
        (z : (integralCoefficientSheaf l L Y n).obj.obj (op V)),
        (((finiteZeroIso l L Y n).inv ≫ (u n).inv.f 0).val.app (op V)) z =
          integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V 1)) ∧
      (∀ (n : ℕ) (V : Y.ProEt)
        (x : (((integralScalarFiniteComplex l E L ι Y (n + 1)).obj
          (regularComplex l E Y)).X 0).val.obj (op V)),
        (((u n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app (op V))
          (((((integralScalarTransition l E L ι Y n).app
            (regularComplex l E Y)).f 0).val.app (op V)) x) =
        (integralCoefficientSheafTransition l L Y n).hom.app (op V)
          ((((u (n + 1)).hom.f 0 ≫ (finiteZeroIso l L Y (n + 1)).hom).val.app (op V)) x)))

/-- The canonical derived tensor comparison is invertible on the regular complex.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def finiteDerivedComputation : Prop :=
    (∀ n : ℕ, IsIso
      (((integralScalarReductionWitness l E L ι Y n).choose_spec.choose_spec
        |>.choose_spec.choose_spec.2.2).choose_spec.choose.app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (regularComplex l E Y))))

/-- Identity-extension reduction units are precisely the limit projections.
Source: blueprint order 1869 (blueprint: lem-weil-constant-scalar-strict-unit). -/
def reductionUnits : Prop :=
    (∀ n : ℕ, ∃ v : unrestrictedTowerFiniteComplex l E Y n (regularComplex l E Y) ≅
        finiteRegularComplex l E Y n,
      (∀ (V : Y.ProEt) (z : (integralCoefficientSheaf l E Y n).obj.obj (op V)),
        (((finiteZeroIso l E Y n).inv ≫ v.inv.f 0).val.app (op V)) z =
          unrestrictedTowerTensorSection l E Y n ((regularComplex l E Y).X 0) (op V)
            z (regularSection l E Y V 1)) ∧
      unrestrictedTowerUnit l E Y (regularComplex l E Y) n ≫
        ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map v.hom =
          projectionComplex l E Y n ∧
      (∀ hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
        (R := completedIntegralCommRingSheafUnrestricted l E Y)
        (𝟙 (regularComplex l E Y)),
        canonicalIntegralReductionTowerMap l E Y (𝟙 (regularComplex l E Y)) hq n ≫
          DerivedCategory.Q.map
            (((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map v.hom) =
          DerivedCategory.Q.map (projectionComplex l E Y n)))

attribute [local irreducible] limit

section TensorHelpers
universe a b r
open scoped ChangeOfRings
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
private abbrev ring (R : Sheaf J CommRingCat.{r}) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R
private def rawTensor (M : SheafOfModules.{r} (ring R)) (U : Cᵒᵖ)
    (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.changeOfRings φ M).val.obj U :=
  (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app U
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
private theorem rawTensor_smul
    (M : SheafOfModules.{r} (ring R)) (U : Cᵒᵖ)
    (a s : S.obj.obj U) (x : M.val.obj U) :
    rawTensor φ M U (a * s) x = a • rawTensor φ M U s x := by
  exact (((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).unit.app
    (SheafOfModules.changeOfRingsPresheaf φ M)).app U).hom.map_smul a
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)
private def regularChangeSectionIso (U : Cᵒᵖ) :
    (SheafOfModules.changeOfRingsPresheaf φ (SheafOfModules.unit (ring R))).obj U ≅
      (SheafOfModules.unit (ring S)).val.obj U := by
  let := (φ.hom.app U).hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid (R.obj.obj U) (S.obj.obj U)
    (S.obj.obj U)).toModuleIso

private theorem regularChangeSection_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (regularChangeSectionIso φ U).hom
      (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = φ.hom.app U x * s := rfl

private def regularChangePresheafIso :
    SheafOfModules.changeOfRingsPresheaf φ (SheafOfModules.unit (ring R)) ≅
      (SheafOfModules.unit (ring S)).val :=
  PresheafOfModules.isoMk (regularChangeSectionIso φ) (by
    intro U V f
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (regularChangeSectionIso φ V).hom
        ((SheafOfModules.changeOfRingsPresheaf φ _).map f
          ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      S.obj.map f ((regularChangeSectionIso φ U).hom
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
    rw [show (SheafOfModules.changeOfRingsPresheaf φ _).map f
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) = _ from
      (SheafOfModules.exists_changeOfRingsMap φ _ f).choose_spec 1 x]
    simp only [map_one, regularChangeSection_tmul, mul_one]
    change φ.hom.app V (R.obj.map f x) * 1 = S.obj.map f (φ.hom.app U x)
    rw [mul_one]
    exact ConcreteCategory.congr_hom (φ.hom.naturality f) x)

private def regularChangeIso :
    SheafOfModules.changeOfRings φ (SheafOfModules.unit (ring R)) ≅
      SheafOfModules.unit (ring S) :=
  (PresheafOfModules.sheafification (𝟙 (ring S).obj)).mapIso
      (regularChangePresheafIso φ) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).counit).app
      (SheafOfModules.unit (ring S))

private theorem regularChangeIso_tmul (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (regularChangeIso φ).hom.val.app U
      (rawTensor φ (SheafOfModules.unit (ring R)) U s x) = φ.hom.app U x * s := by
  let adj := CategoryTheory.sheafificationAdjunction J AddCommGrpCat.{r}
  let g := (PresheafOfModules.toPresheaf _).map (regularChangePresheafIso φ).hom
  have h := (adj.homEquiv _ ((SheafOfModules.toSheaf (ring S)).obj
    (SheafOfModules.unit (ring S)))).apply_symm_apply g
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_unit] at h
  have hc := PresheafOfModules.toSheaf_map_sheafificationAdjunction_counit_app
    (𝟙 (ring S).obj) (SheafOfModules.unit (ring S))
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).counit.app
    (SheafOfModules.unit (ring S))).val.app U
    (((PresheafOfModules.sheafification (𝟙 (ring S).obj)).map
      (regularChangePresheafIso φ).hom).val.app U
        (rawTensor φ (SheafOfModules.unit (ring R)) U s x)) = _
  change ((SheafOfModules.toSheaf _).map
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (ring S).obj)).counit.app
      (SheafOfModules.unit (ring S)))).hom.app U _ = _
  rw [hc]
  exact congrArg (fun f ↦ (f.app U).hom
    (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) h

private theorem rawTensor_map {M N : SheafOfModules.{r} (ring R)}
    (a : M ⟶ N) (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom φ M a).val.app U (rawTensor φ M U s x) =
      rawTensor φ N U s (a.val.app U x) := by
  let k : SheafOfModules.changeOfRingsPresheaf φ M ⟶
      SheafOfModules.changeOfRingsPresheaf φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (a.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M a }
  let z : (SheafOfModules.changeOfRingsPresheaf φ M).presheaf.obj U :=
    s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x
  have hn := toSheafify_naturality J ((PresheafOfModules.toPresheaf _).map k)
  have h := congrArg (fun η ↦ (η.app U).hom z) hn
  change (toSheafify J (SheafOfModules.changeOfRingsPresheaf φ N).presheaf).app U
    ((ModuleCat.extendScalars (φ.hom.app U).hom).map (a.val.app U) z) = _ at h
  dsimp only [z] at h
  erw [ModuleCat.ExtendScalars.map_tmul] at h
  exact h.symm

private theorem identified_map
    (F : SheafOfModules.{r} (ring R) ⥤ SheafOfModules.{r} (ring S))
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N), F.map a = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M a ≫ eqToHom (h N).symm)
    {M N : SheafOfModules.{r} (ring R)} (a : M ⟶ N) :
    eqToHom (h M).symm ≫ F.map a =
      SheafOfModules.changeOfRingsHom φ M a ≫ eqToHom (h N).symm := by
  rw [hm, ← Category.assoc, eqToHom_trans]
  simp only [eqToHom_refl, Category.id_comp]

private theorem identified_tensor_map
    (F : SheafOfModules.{r} (ring R) ⥤ SheafOfModules.{r} (ring S))
    (h : ∀ M, F.obj M = SheafOfModules.changeOfRings φ M)
    (hm : ∀ {M N} (a : M ⟶ N), F.map a = eqToHom (h M) ≫
      SheafOfModules.changeOfRingsHom φ M a ≫ eqToHom (h N).symm)
    {M N : SheafOfModules.{r} (ring R)} (a : M ⟶ N)
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : M.val.obj U) :
    (F.map a).val.app U ((eqToHom (h M).symm).val.app U (rawTensor φ M U s x)) =
      (eqToHom (h N).symm).val.app U (rawTensor φ N U s (a.val.app U x)) := by
  exact (congrArg (fun f ↦ f.val.app U (rawTensor φ M U s x))
    (identified_map φ F h hm a)).trans
      (congrArg (fun z ↦ (eqToHom (h N).symm).val.app U z)
        (rawTensor_map φ a U s x))

private theorem transported_regular_tmul
    (M : SheafOfModules.{r} (ring S))
    (e : M ≅ SheafOfModules.changeOfRings φ (SheafOfModules.unit (ring R)))
    (U : Cᵒᵖ) (s : S.obj.obj U) (x : R.obj.obj U) :
    (e ≪≫ regularChangeIso φ).hom.val.app U
      (e.inv.val.app U (rawTensor φ (SheafOfModules.unit (ring R)) U s x)) =
        φ.hom.app U x * s := by
  have he := congrArg (fun f ↦ f.val.app U
    (rawTensor φ (SheafOfModules.unit (ring R)) U s x)) e.inv_hom_id
  exact (congrArg (fun z ↦ (regularChangeIso φ).hom.val.app U z) he).trans
    (regularChangeIso_tmul φ U s x)

attribute [local irreducible] regularChangeIso

end TensorHelpers

section ConeHelpers
universe a b
variable {A : Type a} [Category.{b} A] [Preadditive A] [HasBinaryBiproducts A]
  {K M N : CochainComplex A ℤ} (f : M ⟶ N)
private theorem cone_component_ext (η θ : K ⟶ CochainComplex.mappingCocone f) (i : ℤ)
    (hf : η.f i ≫ (CochainComplex.mappingCocone.fst f).f i =
      θ.f i ≫ (CochainComplex.mappingCocone.fst f).f i)
    (hη : η.f i ≫ (CochainComplex.mappingCocone.snd f).v i (i - 1) (by omega) = 0)
    (hθ : θ.f i ≫ (CochainComplex.mappingCocone.snd f).v i (i - 1) (by omega) = 0) :
    η.f i = θ.f i := by
  have hid := CochainComplex.mappingCocone.id_X f i (i - 1) (by omega)
  have he := congrArg (η.f i ≫ ·) hid
  have ht := congrArg (θ.f i ≫ ·) hid
  simp only [Preadditive.comp_add, ← Category.assoc, hη, hθ, Limits.zero_comp,
    add_zero, Category.comp_id] at he ht
  exact he.symm.trans ((congrArg (· ≫ _) hf).trans ht)
end ConeHelpers

attribute [local implicit_reducible] integralScalarTensorSection

private def finiteModuleIso (n : ℕ) :
    (integralScalarReduction l E L ι Y n).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≅
      SheafOfModules.unit (integralCoefficientSheaf l L Y n) :=
  (integralScalarReductionIso l E L ι Y n).app _ ≪≫
    regularChangeIso (integralScalarRho l E L ι Y n)

private def finiteComplexIso (n : ℕ) :
    (integralScalarFiniteComplex l E L ι Y n).obj (regularComplex l E Y) ≅
      finiteRegularComplex l L Y n :=
  (HomologicalComplex.singleMapHomologicalComplex
    (integralScalarReduction l E L ι Y n) (.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor (integralOperationsFiniteModules l L Y n) 0).mapIso
      (finiteModuleIso l E Y L ι n)

private theorem finiteModuleIso_tmul (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    (finiteModuleIso l E Y L ι n).hom.val.app U
      (integralScalarTensorSection l E L ι Y n
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) U s r) =
      (integralScalarRho l E L ι Y n).hom.app U r * s := by
  exact transported_regular_tmul (integralScalarRho l E L ι Y n) _
    ((integralScalarReductionIso l E L ι Y n).app _) U s r

attribute [local irreducible] finiteModuleIso

private theorem scalar_map_tmul (n : ℕ) {M N : integralTowerModules l E Y}
    (a : M ⟶ N) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) (x : M.val.obj U) :
    ((integralScalarReduction l E L ι Y n).map a).val.app U
        (integralScalarTensorSection l E L ι Y n M U s x) =
      integralScalarTensorSection l E L ι Y n N U s (a.val.app U x) := by
  let e := integralScalarReductionIso l E L ι Y n
  let z := rawTensor (integralScalarRho l E L ι Y n) M U s x
  have h := congrArg (fun f ↦ (f.val.app U) z) (e.inv.naturality a).symm
  exact h.trans (congrArg (fun z ↦ ((e.inv.app N).val.app U) z)
    (rawTensor_map (integralScalarRho l E L ι Y n) a U s x))

private theorem finiteComplexIso_zero (n : ℕ) :
    (finiteComplexIso l E Y L ι n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom =
      (integralScalarReduction l E L ι Y n).map (regularZeroIso l E Y).hom ≫
        (finiteModuleIso l E Y L ι n).hom := by
  simp only [finiteComplexIso, Iso.trans_hom, Iso.app_hom, CochainComplex.singleFunctor,
    HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.mapIso_hom]
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, finiteZeroIso, regularZeroIso, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

private theorem finiteComplexIso_tmul (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    ((finiteComplexIso l E Y L ι n).hom.f 0 ≫ (finiteZeroIso l L Y n).hom).val.app U
      (integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) U s
        ((regularZeroIso l E Y).inv.val.app U r)) =
      (integralScalarRho l E L ι Y n).hom.app U r * s := by
  rw [finiteComplexIso_zero]
  have ht := scalar_map_tmul l E Y L ι n (regularZeroIso l E Y).hom U s
    ((regularZeroIso l E Y).inv.val.app U r)
  have hr := congrArg (fun f ↦ f.val.app U r) (regularZeroIso l E Y).inv_hom_id
  exact (congrArg (fun z ↦ (finiteModuleIso l E Y L ι n).hom.val.app U z) ht).trans
    ((congrArg (fun z ↦ (finiteModuleIso l E Y L ι n).hom.val.app U
      (integralScalarTensorSection l E L ι Y n _ U s z)) hr).trans
        (finiteModuleIso_tmul l E Y L ι n U s r))

private theorem finiteComplexIso_inv (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U) :
    ((finiteZeroIso l L Y n).inv ≫ (finiteComplexIso l E Y L ι n).inv.f 0).val.app U s =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) U s
        ((regularZeroIso l E Y).inv.val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U)) := by
  let e := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso (finiteComplexIso l E Y L ι n) ≪≫
    finiteZeroIso l L Y n
  let x := integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) U s
    ((regularZeroIso l E Y).inv.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U))
  have hx : e.hom.val.app U x = s := by
    change (((finiteComplexIso l E Y L ι n).hom.f 0 ≫
      (finiteZeroIso l L Y n).hom).val.app U) _ = s
    simpa only [map_one, one_mul] using (finiteComplexIso_tmul l E Y L ι n U s 1)
  change e.inv.val.app U s = x
  exact (congrArg (fun z ↦ e.inv.val.app U z) hx.symm).trans
    (congrArg (fun f ↦ f.val.app U x) e.hom_inv_id)

attribute [local irreducible] finiteComplexIso

private theorem scalarTensor_smul (n : ℕ) (M : integralTowerModules l E Y)
    (U : Y.ProEtᵒᵖ) (a s : (integralCoefficientCommRingSheaf l L Y n).obj.obj U)
    (x : M.val.obj U) :
    integralScalarTensorSection l E L ι Y n M U (a * s) x =
      a • integralScalarTensorSection l E L ι Y n M U s x := by
  change (((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U)
    (rawTensor (integralScalarRho l E L ι Y n) M U (a * s) x) = _
  exact (congrArg
    (fun z ↦ (((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U) z)
    (rawTensor_smul (integralScalarRho l E L ι Y n) M U a s x)).trans
      ((((integralScalarReductionIso l E L ι Y n).inv.app M).val.app U).hom.map_smul _ _)

private theorem regularSection_smul (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)) :
    regularSection l L Y V s = s • regularSection l L Y V 1 := by
  simpa only [regularSection, smul_eq_mul, mul_one] using
    ((regularZeroIso l L Y).inv.val.app (op V)).hom.map_smul s
      (show (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted l L Y)).val.obj (op V) from
          (1 : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)))

attribute [local implicit_reducible] scalarReductionExtension
  unrestrictedTowerTensorSection unrestrictedIntegralTensorSection
  unrestrictedIntegralReductionFunctor
attribute [local irreducible] scalarReductionExistence
  unrestrictedIntegralReductionExistence

private def reductionTransport (n : ℕ) (M : integralTowerModules l E Y) :
    (scalarReductionExtension l E Y n).obj M ≅
      SheafOfModules.changeOfRings.{t, t + 1, max u (t + 1)}
        (completedIntegralCommRingProjectionUnrestricted l E Y n) M :=
  eqToIso ((scalarReductionExistence l E Y n).choose_spec.choose M)

private theorem reduction_map_tmul (n : ℕ) {M N : integralTowerModules l E Y}
    (a : M ⟶ N) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) (x : M.val.obj U) :
    ((scalarReductionExtension l E Y n).map a).val.app U
        (unrestrictedTowerTensorSection l E Y n M U s x) =
      unrestrictedTowerTensorSection l E Y n N U s (a.val.app U x) := by
  exact identified_tensor_map (completedIntegralCommRingProjectionUnrestricted l E Y n)
    (scalarReductionExtension l E Y n)
    (scalarReductionExistence l E Y n).choose_spec.choose
    (scalarReductionExistence l E Y n).choose_spec.choose_spec.choose a U s x

private def reductionModuleIso (n : ℕ) :
    (scalarReductionExtension l E Y n).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E Y n) :=
  reductionTransport l E Y n _ ≪≫
    regularChangeIso (completedIntegralCommRingProjectionUnrestricted l E Y n)

private def reductionComplexIso (n : ℕ) :
    unrestrictedTowerFiniteComplex l E Y n (regularComplex l E Y) ≅
      finiteRegularComplex l E Y n :=
  (HomologicalComplex.singleMapHomologicalComplex
    (scalarReductionExtension l E Y n) (.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor (integralOperationsFiniteModules l E Y n) 0).mapIso
      (reductionModuleIso l E Y n)

private theorem reductionModuleIso_tmul (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    (reductionModuleIso l E Y n).hom.val.app U
      (unrestrictedTowerTensorSection l E Y n
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E Y)) U s r) =
      (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r * s := by
  exact transported_regular_tmul
    (completedIntegralCommRingProjectionUnrestricted l E Y n) _
    (reductionTransport l E Y n _) U s r

private theorem reductionComplexIso_zero (n : ℕ) :
    (reductionComplexIso l E Y n).hom.f 0 ≫ (finiteZeroIso l E Y n).hom =
      (scalarReductionExtension l E Y n).map (regularZeroIso l E Y).hom ≫
        (reductionModuleIso l E Y n).hom := by
  simp only [reductionComplexIso, Iso.trans_hom, Iso.app_hom, CochainComplex.singleFunctor,
    HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Functor.mapIso_hom]
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, finiteZeroIso, regularZeroIso, Iso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

private theorem reductionComplexIso_tmul (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    ((reductionComplexIso l E Y n).hom.f 0 ≫ (finiteZeroIso l E Y n).hom).val.app U
      (unrestrictedTowerTensorSection l E Y n ((regularComplex l E Y).X 0) U s
        ((regularZeroIso l E Y).inv.val.app U r)) =
      (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r * s := by
  rw [reductionComplexIso_zero]
  have ht := reduction_map_tmul l E Y n (regularZeroIso l E Y).hom U s
    ((regularZeroIso l E Y).inv.val.app U r)
  have hr := congrArg (fun f ↦ f.val.app U r) (regularZeroIso l E Y).inv_hom_id
  exact (congrArg (fun z ↦ (reductionModuleIso l E Y n).hom.val.app U z) ht).trans
    ((congrArg (fun z ↦ (reductionModuleIso l E Y n).hom.val.app U
      (unrestrictedTowerTensorSection l E Y n _ U s z)) hr).trans
        (reductionModuleIso_tmul l E Y n U s r))

private theorem reductionComplexIso_inv (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (integralCoefficientCommRingSheaf l E Y n).obj.obj U) :
    ((finiteZeroIso l E Y n).inv ≫ (reductionComplexIso l E Y n).inv.f 0).val.app U s =
      unrestrictedTowerTensorSection l E Y n ((regularComplex l E Y).X 0) U s
        ((regularZeroIso l E Y).inv.val.app U
          (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U)) := by
  let e := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso (reductionComplexIso l E Y n) ≪≫
    finiteZeroIso l E Y n
  let x := unrestrictedTowerTensorSection l E Y n ((regularComplex l E Y).X 0) U s
    ((regularZeroIso l E Y).inv.val.app U
      (1 : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U))
  have hx : e.hom.val.app U x = s := by
    change (((reductionComplexIso l E Y n).hom.f 0 ≫
      (finiteZeroIso l E Y n).hom).val.app U) _ = s
    simpa only [map_one, one_mul] using (reductionComplexIso_tmul l E Y n U s 1)
  change e.inv.val.app U s = x
  exact (congrArg (fun z ↦ e.inv.val.app U z) hx.symm).trans
    (congrArg (fun f ↦ f.val.app U x) e.hom_inv_id)

attribute [local irreducible] reductionComplexIso

private theorem projectionModule_apply (n : ℕ) (U : Y.ProEtᵒᵖ)
    (r : (completedIntegralCoefficientSheafUnrestricted l E Y).obj.obj U) :
    (projectionModule l E Y n).val.app U r =
      (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r := by
  change (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r * 1 = _
  exact mul_one _

private theorem projectionComplex_zero (n : ℕ) :
    (projectionComplex l E Y n).f 0 ≫
        (scalarReductionRestriction l E Y n).map (finiteZeroIso l E Y n).hom =
      (regularZeroIso l E Y).hom ≫ projectionModule l E Y n := by
  simp only [projectionComplex, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    CochainComplex.singleFunctor]
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, regularZeroIso, finiteZeroIso, Iso.inv_hom_id_assoc,
    ← Functor.map_comp, Iso.inv_hom_id]
  rw [(scalarReductionRestriction l E Y n).map_id, Category.comp_id]

private theorem reductionComplexIso_unit (n : ℕ) :
    unrestrictedTowerUnit l E Y (regularComplex l E Y) n ≫
        ((scalarReductionRestriction l E Y n).mapHomologicalComplex (.up ℤ)).map
          (reductionComplexIso l E Y n).hom = projectionComplex l E Y n := by
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_mono ((scalarReductionRestriction l E Y n).map
    (finiteZeroIso l E Y n).hom)).1
  rw [projectionComplex_zero]
  apply (cancel_epi (regularZeroIso l E Y).inv).1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change ((reductionComplexIso l E Y n).hom.f 0 ≫
    (finiteZeroIso l E Y n).hom).val.app U
      (((unrestrictedTowerUnit l E Y (regularComplex l E Y) n).f 0).val.app U
        ((regularZeroIso l E Y).inv.val.app U r)) = _
  have hu := unrestrictedTowerUnit_condition l E Y (regularComplex l E Y) n 0 U
    ((regularZeroIso l E Y).inv.val.app U r)
  have ht := reductionComplexIso_tmul l E Y n U 1 r
  have hr := congrArg (fun f ↦ f.val.app U r) (regularZeroIso l E Y).inv_hom_id
  calc
    _ = (completedIntegralCommRingProjectionUnrestricted l E Y n).hom.app U r :=
      (congrArg (fun z ↦ ((reductionComplexIso l E Y n).hom.f 0 ≫
        (finiteZeroIso l E Y n).hom).val.app U z) hu).trans (by simpa only [mul_one] using ht)
    _ = (projectionModule l E Y n).val.app U
        ((regularZeroIso l E Y).hom.val.app U ((regularZeroIso l E Y).inv.val.app U r)) :=
      (projectionModule_apply l E Y n U r).symm.trans
        (congrArg (fun z ↦ (projectionModule l E Y n).val.app U z) hr.symm)

private def strictCoordinate (n : ℕ) :
    regularComplex l L Y ⟶ ((integralScalarTowerFunctor l E L ι Y).obj
      (regularComplex l E Y)).obj (op n) :=
  projectionComplex l L Y n ≫
    ((scalarReductionRestriction l L Y n).mapHomologicalComplex (.up ℤ)).map
      (finiteComplexIso l E Y L ι n).inv

private theorem strictCoordinate_apply (n : ℕ) (V : Y.ProEt)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj (op V)) :
    ((strictCoordinate l E Y L ι n).f 0).val.app (op V) (regularSection l L Y V s) =
      integralScalarTensorSection l E L ι Y n ((regularComplex l E Y).X 0) (op V)
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s)
        (regularSection l E Y V 1) := by
  have hp := congrArg (fun f ↦ f.val.app (op V)
    (regularSection l L Y V s)) (projectionComplex_zero l L Y n)
  have hr := congrArg (fun f ↦ f.val.app (op V) s) (regularZeroIso l L Y).inv_hom_id
  have hz : ((projectionComplex l L Y n).f 0).val.app (op V)
      (regularSection l L Y V s) = (finiteZeroIso l L Y n).inv.val.app (op V)
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s) := by
    let eU := (PresheafOfModules.evaluation _ (op V)).mapIso
      ((SheafOfModules.forget _).mapIso (finiteZeroIso l L Y n))
    apply eU.toLinearEquiv.injective
    exact hp.trans ((congrArg (fun z ↦ (projectionModule l L Y n).val.app (op V) z) hr).trans
      ((projectionModule_apply l L Y n (op V) s).trans
        (congrArg (fun f ↦ f.val.app (op V)
          ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s))
          (finiteZeroIso l L Y n).inv_hom_id).symm))
  exact (congrArg (fun z ↦ (finiteComplexIso l E Y L ι n).inv.f 0 |>.val.app (op V) z)
    hz).trans (finiteComplexIso_inv l E Y L ι n (op V) _)

private theorem coefficientProjection_transition (n : ℕ) (U : Y.ProEtᵒᵖ)
    (s : (completedIntegralCoefficientSheafUnrestricted l L Y).obj.obj U) :
    (integralCoefficientSheafTransition l L Y n).hom.app U
      ((completedIntegralCommRingProjectionUnrestricted l L Y (n + 1)).hom.app U s) =
        (completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app U s := by
  have h := congrArg (fun f ↦ f.hom.app U)
    (limit.w (integralCoefficientSheafSystem l L Y) (homOfLE (Nat.le_succ n)).op)
  have h' : (limit.π (integralCoefficientSheafSystem l L Y) (op (n + 1))).hom.app U ≫
      (integralCoefficientSheafTransition l L Y n).hom.app U =
        (limit.π (integralCoefficientSheafSystem l L Y) (op n)).hom.app U := by
    simpa only [integralCoefficientSheafSystem, Functor.ofOpSequence_map_homOfLE_succ,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] using h
  have he := ConcreteCategory.congr_hom h' s
  change (integralCoefficientSheafTransition l L Y n).hom.app U
    ((limit.π (integralCoefficientSheafSystem l L Y) (op (n + 1))).hom.app U s) =
      (limit.π (integralCoefficientSheafSystem l L Y) (op n)).hom.app U s
  exact he

private theorem strictCoordinate_compatible (n : ℕ) :
    strictCoordinate l E Y L ι (n + 1) ≫ integralOperationsTowerStep
        ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)) n =
      strictCoordinate l E Y L ι n := by
  apply HomologicalComplex.from_single_hom_ext
  apply (cancel_epi (regularZeroIso l L Y).inv).1
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  have h₁ := strictCoordinate_apply l E Y L ι (n + 1) U.unop s
  have h₀ := strictCoordinate_apply l E Y L ι n U.unop s
  have ht := (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
    (regularComplex l E Y) 0 U
    ((completedIntegralCommRingProjectionUnrestricted l L Y (n + 1)).hom.app U s)
    (regularSection l E Y U.unop 1)
  change (((integralOperationsTowerStep
    ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)) n).f 0).val.app U)
    (((strictCoordinate l E Y L ι (n + 1)).f 0).val.app U
      (regularSection l L Y U.unop s)) = _
  have hs : integralOperationsTowerStep
      ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)) n =
        (integralScalarTransition l E L ι Y n).app (regularComplex l E Y) := by
    exact congrArg (fun f ↦ f.app (regularComplex l E Y))
      (Functor.ofOpSequence_map_homOfLE_succ (integralScalarTransition l E L ι Y) n)
  rw [hs]
  exact (congrArg (fun z ↦ (((integralScalarTransition l E L ι Y n).app
    (regularComplex l E Y)).f 0).val.app U z) h₁).trans
      (ht.trans ((congrArg (fun z ↦ integralScalarTensorSection l E L ι Y n
        ((regularComplex l E Y).X 0) U z (regularSection l E Y U.unop 1))
          (coefficientProjection_transition l Y L n U s)).trans h₀.symm))

private def strictFirst : regularComplex l L Y ⟶ ∏ᶜ (fun n ↦
    ((integralScalarTowerFunctor l E L ι Y).obj (regularComplex l E Y)).obj (op n)) :=
  Pi.lift (strictCoordinate l E Y L ι)

private theorem strictFirst_boundary : strictFirst l E Y L ι ≫ boundary l E Y L ι = 0 := by
  apply Pi.hom_ext
  intro n
  simp only [strictFirst, boundary, towerTransitionEndomorphism, Preadditive.comp_sub,
    Category.comp_id, Preadditive.sub_comp, towerProductShift,
    Category.assoc, Pi.lift_comp_π, Pi.lift_comp_π_assoc, Limits.zero_comp]
  exact sub_eq_zero.mpr (strictCoordinate_compatible l E Y L ι n).symm

private def strictUnit : regularComplex l L Y ⟶
    (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y) :=
  CochainComplex.mappingCocone.lift (boundary l E Y L ι) (strictFirst l E Y L ι) 0
    (by rw [strictFirst_boundary]; simp)

private theorem strictUnit_coordinates :
    quotientCoordinates l E Y L ι (strictUnit l E Y L ι) := by
  intro n V s
  have h : coordinate l E Y L ι (strictUnit l E Y L ι) n =
      (strictCoordinate l E Y L ι n).f 0 := by
    change ((strictUnit l E Y L ι ≫
      CochainComplex.mappingCocone.fst (boundary l E Y L ι)) ≫ Pi.π _ n).f 0 = _
    rw [strictUnit, CochainComplex.mappingCocone.lift_fst, strictFirst, Pi.lift_comp_π]
  exact (congrArg (fun f ↦ f.val.app (op V) (regularSection l L Y V s)) h).trans
    (strictCoordinate_apply l E Y L ι n V s)

private theorem strictUnit_second :
    zeroSecondComponent l E Y L ι (strictUnit l E Y L ι) := by
  intro i
  simp only [strictUnit, CochainComplex.mappingCocone.lift_f_snd_v,
    CochainComplex.HomComplex.Cochain.zero_v]

private theorem strictUnit_unique
    (η θ : regularComplex l L Y ⟶
      (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y))
    (hη : quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η)
    (hθ : quotientCoordinates l E Y L ι θ ∧ zeroSecondComponent l E Y L ι θ) : η = θ := by
  have hfirst : η ≫ CochainComplex.mappingCocone.fst (boundary l E Y L ι) =
      θ ≫ CochainComplex.mappingCocone.fst (boundary l E Y L ι) := by
    apply Pi.hom_ext
    intro n
    apply HomologicalComplex.from_single_hom_ext
    apply (cancel_epi (regularZeroIso l L Y).inv).1
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact (hη.1 n U.unop s).trans (hθ.1 n U.unop s).symm
  apply HomologicalComplex.from_single_hom_ext
  exact cone_component_ext (boundary l E Y L ι) η θ 0
    (congrArg (fun f ↦ f.f 0) hfirst) (hη.2 0) (hθ.2 0)

/-- The regular single complex is good. Source: the K-flat and flat-term calculation
in the proof plan for `lem-weil-constant-scalar-strict-unit`.
(blueprint: lem-weil-constant-scalar-strict-unit). -/
private theorem regular_scalar_strict_unit_good :
    integralOperationsGoodComplex l E Y (regularComplex l E Y) := by
  let R := completedIntegralCommRingSheafUnrestricted l E Y
  let A := integralTowerModules l E Y
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  constructor
  · intro F hF i
    exact (quasiIsoAt_iff_exactAt'
      (HomologicalComplex.rightUnitor F).hom i (hF i)).1 inferInstance
  · intro i
    apply (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm
    by_cases hi : i = 0
    · subst i
      exact (exactFunctor _ _).prop_of_iso
        ((MonoidalCategory.curriedTensor A).flip.mapIso (regularZeroIso l E Y)).symm
        (ObjectProperty.prop_unit ObjectProperty.flat).2
    · have hz : IsZero ((regularComplex l E Y).X i) :=
        HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
      have ht : IsZero (MonoidalCategory.tensorRight ((regularComplex l E Y).X i)) := by
        rw [Functor.isZero_iff]
        intro M
        exact (MonoidalCategory.tensorLeft M).map_isZero hz
      have := Functor.preservesLimitsOfSize_of_isZero.{0, 0} _ ht
      have := Functor.preservesColimitsOfSize_of_isZero.{0, 0} _ ht
      change PreservesFiniteLimits _ ∧ PreservesFiniteColimits _
      exact ⟨inferInstance, inferInstance⟩

/-- Finite scalar multiplication and transition formulas for the regular complex.
Source: the sectionwise tensor calculation in the proof plan for
`lem-weil-constant-scalar-strict-unit`.
(blueprint: lem-weil-constant-scalar-strict-unit). -/
private theorem regular_scalar_strict_unit_finite_multiplication :
    finiteMultiplication l E Y L ι := by
  refine ⟨finiteComplexIso l E Y L ι, ?_, ?_, ?_⟩
  · intro n V r z
    exact finiteComplexIso_tmul l E Y L ι n (op V) z r
  · intro n V z
    exact finiteComplexIso_inv l E Y L ι n (op V) z
  · intro n V x
    let e := (HomologicalComplex.eval _ (.up ℤ) 0).mapIso
      (finiteComplexIso l E Y L ι (n + 1)) ≪≫ finiteZeroIso l L Y (n + 1)
    let eU := (PresheafOfModules.evaluation _ (op V)).mapIso
      ((SheafOfModules.forget _).mapIso e)
    obtain ⟨z, rfl⟩ := eU.toLinearEquiv.symm.surjective x
    change _ = (integralCoefficientSheafTransition l L Y n).hom.app (op V)
      (e.hom.val.app (op V) (e.inv.val.app (op V) z))
    rw [show e.hom.val.app (op V) (e.inv.val.app (op V) z) = z from
      congrArg (fun f ↦ f.val.app (op V) z) e.inv_hom_id]
    change (((finiteComplexIso l E Y L ι n).hom.f 0 ≫
      (finiteZeroIso l L Y n).hom).val.app (op V))
      ((((integralScalarTransition l E L ι Y n).app (regularComplex l E Y)).f 0).val.app
        (op V) (((finiteZeroIso l L Y (n + 1)).inv ≫
      (finiteComplexIso l E Y L ι (n + 1)).inv.f 0).val.app (op V) z)) = _
    rw [finiteComplexIso_inv]
    have ht := (integralScalarTransition_existsUnique l E L ι Y n).exists.choose_spec
      (regularComplex l E Y) 0 (op V) z (regularSection l E Y V 1)
    exact (congrArg (fun z ↦ (((finiteComplexIso l E Y L ι n).hom.f 0 ≫
      (finiteZeroIso l L Y n).hom).val.app (op V)) z) ht).trans (by
        simpa only [map_one, one_mul, regularSection] using
          finiteComplexIso_tmul l E Y L ι n (op V)
            ((integralCoefficientSheafTransition l L Y n).hom.app (op V) z) 1)

attribute [local irreducible] integralScalarReductionWitness

private theorem regular_scalar_strict_unit_finite_derived :
    finiteDerivedComputation l E Y L ι := by
  intro n
  have hP := (regular_scalar_strict_unit_good l E Y).1
  -- Project the K-flat computation property from the exact witness in the goal.
  -- Reusing that expression avoids elaborating its nested existential types again.
  run_tac
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← g.getType).consumeMData
    unless ty.isAppOfArity ``CategoryTheory.IsIso 5 do
      throwError "expected an IsIso goal"
    let app := ty.getAppArgs[4]!.consumeMData
    unless app.isAppOfArity ``CategoryTheory.NatTrans.app 8 do
      throwError "expected a natural-transformation component"
    let ε := app.getAppArgs[6]!.consumeMData
    unless ε.isAppOfArity ``Exists.choose 3 do
      throwError "expected selected comparison, got {ε.getAppFn}, arity {ε.getAppArgs.size}"
    let hs := Lean.mkAppN
      (Lean.mkConst ``Exists.choose_spec ε.getAppFn.constLevels!) ε.getAppArgs
    let spec := (Lean.mkApp ε.getAppArgs[1]! ε).headBeta.consumeMData
    unless spec.isAppOfArity ``And 2 do
      throwError "expected the derived-comparison specification"
    let hs := Lean.mkApp3 (Lean.mkConst ``And.right)
      spec.getAppArgs[0]! spec.getAppArgs[1]! hs
    let spec := spec.getAppArgs[1]!.consumeMData
    unless spec.isAppOfArity ``And 2 do
      throwError "expected the K-flat computation conjunct"
    let hs := Lean.mkApp3 (Lean.mkConst ``And.right)
      spec.getAppArgs[0]! spec.getAppArgs[1]! hs
    let q := app.getAppArgs[7]!.consumeMData
    unless q.isAppOfArity ``CategoryTheory.Functor.obj 6 do
      throwError "expected a homotopy-category representative"
    let P := q.getAppArgs[5]!
    let hp := Lean.mkFVar (← Lean.Elab.Tactic.getFVarId (Lean.mkIdent `hP))
    g.assign (Lean.mkApp2 hs P hp)
    Lean.Elab.Tactic.replaceMainGoal []

/-- The identity-extension reduction units are the limit projections.
Source: the reduction-tower calculation in the proof plan for
`lem-weil-constant-scalar-strict-unit`.
(blueprint: lem-weil-constant-scalar-strict-unit). -/
private theorem regular_scalar_strict_unit_reduction_units :
    reductionUnits l E Y := by
  intro n
  refine ⟨reductionComplexIso l E Y n, ?_, reductionComplexIso_unit l E Y n, ?_⟩
  · intro V z
    exact reductionComplexIso_inv l E Y n (op V) z
  · intro hq
    unfold canonicalIntegralReductionTowerMap
    rw [Category.assoc, ← (DerivedCategory.Q (C := scalarReductionSource l E Y)).map_comp,
      reductionComplexIso_unit]
    have hi : unrestrictedTowerAugmentationIso l E Y (𝟙 (regularComplex l E Y)) hq =
        Iso.refl _ := by
      apply Iso.ext
      exact (DerivedCategory.Q (C := scalarReductionSource l E Y)).map_id _
    rw [hi, Iso.refl_inv, Category.id_comp]

/-- Existence and uniqueness of the normalized strict scalar unit.
Source: the strict mapping-cocone calculation in the proof plan for
`lem-weil-constant-scalar-strict-unit`.
(blueprint: lem-weil-constant-scalar-strict-unit). -/
private theorem regular_scalar_strict_unit_exists_unique :
    ∃! η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η := by
  refine ⟨strictUnit l E Y L ι,
    ⟨strictUnit_coordinates l E Y L ι, strictUnit_second l E Y L ι⟩, ?_⟩
  intro η hη
  exact strictUnit_unique l E Y L ι η (strictUnit l E Y L ι) hη
    ⟨strictUnit_coordinates l E Y L ι, strictUnit_second l E Y L ι⟩

/-- Full-section and unit-only normalization are equivalent.
Source: the linearity calculation in the proof plan for
`lem-weil-constant-scalar-strict-unit`.
(blueprint: lem-weil-constant-scalar-strict-unit). -/
private theorem regular_scalar_strict_unit_normalization :
    ∀ η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ↔ unitCoordinates l E Y L ι η := by
  intro η
  constructor
  · intro h n V
    simpa only [map_one] using h n V 1
  · intro h n V s
    rw [regularSection_smul, map_smul, h n V]
    change ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s) •
        integralScalarTensorSection l E L ι Y n _ (op V) 1
          (regularSection l E Y V 1) = _
    simpa only [mul_one] using
      (scalarTensor_smul l E Y L ι n ((regularComplex l E Y).X 0) (op V)
        ((completedIntegralCommRingProjectionUnrestricted l L Y n).hom.app (op V) s) 1
        (regularSection l E Y V 1)).symm

/-- The strict-unit assertion, including all multiplication and reduction formulas.
Source: Bhatt--Scholze, Definition 3.5.2 and Lemma 6.8.2(1), background for the
agent-written strict calculation in blueprint order 1869
(blueprint: lem-weil-constant-scalar-strict-unit).

Proof:
1. Sectionwise balancing gives M tensor R_E isomorphic to M, with inverse x to x tensor 1.
The maps commute with restrictions and descend through sheafification. Thus the regular
and zero sheaves are flat (def-pc-flat-sheaf-modules). The direct-sum total tensor with
R_E[0] is the original complex with its original differential
(def-pc-tensor-complex-sheaves), proving K-flatness (def-pc-kflat-complex).
2. Multiplication sends r tensor z to rho_n(r)z and has inverse z to 1 tensor z.
Balancing proves inverse identities before and after sheafification
(def-pur-sheaf-tensor-product, def-weil-presheaf-modules-sheafification). The complexes
are single complexes. The identity K-flat resolution computes derived scalar extension
by def-weil-integral-scalar-extension.
3. Reduction sends rho_(n+1)(r)z to rho_n(r)red(z), proving transition compatibility.
For the identity coefficient extension gamma sends r to r tensor 1, so multiplication
composed with gamma is pi_n. With q=id the c_n formula in
 def-weil-integral-reduction-tower is exactly the localized gamma using
 def-weil-integral-derived-reduction.
4. Set h_n(s)=1 tensor pi_n(s). It is R_L-linear under restriction along pi_n.
Reduction compatibility gives t_n h_(n+1)=h_n, so its product h is killed by 1-shift.
Products are sectionwise; no exactness or surjectivity of products is used.
5. The normalized strict mapping-cocone differential is (dx,(1-s)x-dy).
The pair (h,0) therefore defines a chain map from R_L[0], with all other source
components zero (def-weil-abstract-derived-category).
6. The product coordinates and two graded cone projections determine the map.
Linearity gives h_n(b)=b h_n(1), proving the equivalent unit-only normalization
also when 1=0 (situation-conventions).
-/
theorem regular_scalar_strict_unit (D : FiniteFieldDatum.{d}) (_hl : l ≠ D.p) :
    integralOperationsGoodComplex l E Y (regularComplex l E Y) ∧
    finiteMultiplication l E Y L ι ∧
    finiteDerivedComputation l E Y L ι ∧
    reductionUnits l E Y ∧
    (∃! η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ∧ zeroSecondComponent l E Y L ι η) ∧
    (∀ η : regularComplex l L Y ⟶
        (integralScalarComplexFunctor l E L ι Y).obj (regularComplex l E Y),
      quotientCoordinates l E Y L ι η ↔ unitCoordinates l E Y L ι η) := by
  exact ⟨regular_scalar_strict_unit_good l E Y,
    regular_scalar_strict_unit_finite_multiplication l E Y L ι,
    regular_scalar_strict_unit_finite_derived l E Y L ι,
    regular_scalar_strict_unit_reduction_units l E Y,
    regular_scalar_strict_unit_exists_unique l E Y L ι,
    regular_scalar_strict_unit_normalization l E Y L ι⟩

end WeilConjectures.ConstantScalarStrictUnit
