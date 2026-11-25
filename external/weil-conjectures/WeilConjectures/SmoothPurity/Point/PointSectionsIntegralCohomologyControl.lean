/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsProperties
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.PoincareDuality.Point.PointSectionsDerivedReduction
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessFiniteTorsion
import WeilConjectures.RingTheory.NilpotentTorsionDerivedLimitComplete
import WeilConjectures.RingTheory.DerivedCompleteModuleComplex
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.RingTheory.DerivedCompleteProductsTriangles
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Ideal.Operations
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Cohomological control of integral point sections
Source: Stacks Project, Tags 091W, 093M and 091P;
(blueprint: lem-weil-point-sections-integral-cohomology-control). -/

@[expose] public section
set_option autoImplicit false
universe u v w
open scoped Pointwise
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [-instance] pointReductionModuleDerived

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem exact_derived_preserves_products
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{v} A] [HasDerivedCategory.{w} B]
    [HasCountableProducts A] [CountableAB4Star A]
    [HasCountableProducts B] [CountableAB4Star B]
    [HasCountableProducts (DerivedCategory A)]
    [HasCountableProducts (DerivedCategory B)]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesLimitsOfShape (Discrete ℕ) F] :
    PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory := by
  classical
  have hQA := (derivedCategory_countableProducts_properties A).1
  have hQB := (derivedCategory_countableProducts_properties B).1
  have hQB' (C : ℕ → CochainComplex B ℤ) :
      PreservesLimit (Discrete.functor C) (DerivedCategory.Q (C := B)) :=
    preservesLimit_of_preserves_limit_cone (limit.isLimit _) (hQB ℕ C).some
  let := hQB'
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q (C := B)) :=
    preservesLimitsOfShape_of_discrete _
  have : PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesLimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  have h (K : ℕ → DerivedCategory A) :
      PreservesLimit (Discrete.functor K) F.mapDerivedCategory := by
    let C := fun n ↦ DerivedCategory.Q.objPreimage (K n)
    let e : Discrete.functor C ⋙ DerivedCategory.Q ≅ Discrete.functor K :=
      Discrete.natIso (fun n ↦ DerivedCategory.Q.objObjPreimageIso (K n.as))
    have : PreservesLimit (Discrete.functor C ⋙ DerivedCategory.Q)
        F.mapDerivedCategory :=
      preservesLimit_of_preserves_limit_cone (hQA ℕ C).some
        (isLimitOfPreserves (DerivedCategory.Q ⋙ F.mapDerivedCategory) (limit.isLimit _))
    exact preservesLimit_of_iso_diagram F.mapDerivedCategory e
  let := h
  exact preservesLimitsOfShape_of_discrete _

private theorem exact_map_roos
    {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{v} A]
    [Category* B] [Abelian B] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    [HasProduct (fun n ↦ F.mapDerivedCategory.obj (K n))]
    [PreservesLimit (Discrete.functor K) F.mapDerivedCategory]
    (t : ∀ n, K (n + 1) ⟶ K n) (M : DerivedCategory A)
    (hM : IsDerivedLimit t M) :
    IsDerivedLimit (K := fun n ↦ F.mapDerivedCategory.obj (K n))
      (fun n ↦ F.mapDerivedCategory.map (t n))
      (F.mapDerivedCategory.obj M) := by
  let Φ := F.mapDerivedCategory
  let e := PreservesProduct.iso Φ K
  obtain ⟨p, δ, hT⟩ := hM
  have he (n : ℕ) : e.hom ≫ Pi.π _ n = Φ.map (Pi.π K n) := by simp [e]
  have ht : Φ.map (towerTransitionEndomorphism t) ≫ e.hom =
      e.hom ≫ towerTransitionEndomorphism (fun n ↦ Φ.map (t n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, he, towerTransitionEndomorphism, towerProductShift,
      Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id,
      Pi.lift_comp_π, Functor.map_sub]
    rw [← Category.assoc, he, ← Functor.map_comp]
    rw [← Functor.map_comp, Pi.lift_comp_π, Category.id_comp, Functor.map_comp]
  refine ⟨Φ.map p ≫ e.hom,
    e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M, ?_⟩
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _
    (Φ.map_distinguished _ hT) _
    (CategoryTheory.Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) e.symm e.symm
      (by change (Φ.map p ≫ e.hom) ≫ e.inv = 𝟙 _ ≫ Φ.map p; simp)
      (by
        change towerTransitionEndomorphism (fun n ↦ Φ.map (t n)) ≫ e.inv =
          e.inv ≫ Φ.map (towerTransitionEndomorphism t)
        apply (cancel_mono e.hom).1
        simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
          Iso.inv_hom_id_assoc] using congrArg (fun z ↦ e.inv ≫ z) ht.symm)
      (by
        change (e.inv ≫ Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M) ≫
          (shiftFunctor _ (1 : ℤ)).map (𝟙 _) =
            e.inv ≫ (Φ.map δ ≫ (Φ.commShiftIso (1 : ℤ)).hom.app M)
        simp))

private theorem roos_of_iso
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    (t : ∀ n, K (n + 1) ⟶ K n) {M N : DerivedCategory A}
    (hM : IsDerivedLimit t M) (e : M ≅ N) : IsDerivedLimit t N := by
  obtain ⟨p, δ, hT⟩ := hM
  refine ⟨e.inv ≫ p, δ ≫ (shiftFunctor _ (1 : ℤ)).map e.hom, ?_⟩
  exact CategoryTheory.Pretriangulated.isomorphic_distinguished _ hT _
    (CategoryTheory.Pretriangulated.Triangle.isoMk _ _ e.symm (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp))

private theorem homology_product_zero
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K] (i : ℤ)
    [PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A i)]
    (h : ∀ n, IsZero ((DerivedCategory.homologyFunctor A i).obj (K n))) :
    IsZero ((DerivedCategory.homologyFunctor A i).obj (∏ᶜ K)) := by
  exact (isLimitOfPreserves (DerivedCategory.homologyFunctor A i)
    (limit.isLimit (Discrete.functor K))).isZero_pt
      (Functor.isZero _ (fun n ↦ h n.as))

private theorem bounded_of_roos_triangle
    {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory.{w} A]
    (K : ℕ → DerivedCategory A) [HasProduct K]
    (t : ∀ n, K (n + 1) ⟶ K n) (M : DerivedCategory A)
    (hM : IsDerivedLimit t M) (a b : ℤ)
    (hH : ∀ i : ℤ,
      PreservesLimitsOfShape (Discrete ℕ) (DerivedCategory.homologyFunctor A i))
    (hK : ∀ n i, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor A i).obj (K n))) :
    ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
      IsZero ((DerivedCategory.homologyFunctor A i).obj M) := by
  classical
  refine ⟨Finset.Icc a (b + 1), ?_⟩
  intro i hi
  have hi' : i < a ∨ b + 1 < i := by
    simpa only [Finset.mem_Icc, not_and_or, not_le] using hi
  obtain ⟨p, δ, hT⟩ := hM
  let T := CategoryTheory.Pretriangulated.Triangle.mk p (towerTransitionEndomorphism t) δ
  have h₀ : IsZero ((DerivedCategory.homologyFunctor A (i - 1)).obj (∏ᶜ K)) := by
    have := hH (i - 1)
    exact homology_product_zero K (i - 1) (fun n ↦ hK n (i - 1) (by omega))
  have h₁ : IsZero ((DerivedCategory.homologyFunctor A i).obj (∏ᶜ K)) := by
    have := hH i
    exact homology_product_zero K i (fun n ↦ hK n i (by omega))
  exact (DerivedCategory.HomologySequence.exact₁ T hT (i - 1) i (by omega))
    |>.isZero_of_both_isZero h₀ h₁

private theorem point_source_countableAB4Star
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k] :
    CountableAB4Star (scalarReductionSource.{u, u} l E (Spec (.of k))) := by
  let A := scalarReductionSource.{u, u} l E (Spec (.of k))
  let : HasFiniteBiproducts A := Abelian.hasFiniteBiproducts
  have : (lim (J := Discrete ℕ) (C := A)).PreservesEpimorphisms :=
    { preserves := by
        intro F G f hf
        have h := (ProEt.countableProducts_exact.{u, u, 0} (Spec (.of k))
          (completedIntegralCommRingSheafUnrestricted l E (Spec (.of k)))).2.2
          ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
          (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
        have he : lim.map f = (Pi.isoLimit _).inv ≫
            Limits.Pi.map (fun n ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit _).hom := by
          apply limit.hom_ext
          intro ⟨n⟩
          simp
        rw [he]
        infer_instance }
  have := hasExactLimitsOfShape_of_preservesEpi A (Discrete ℕ)
  exact CountableAB4Star.of_hasExactLimitsOfShape_nat A

private lemma point_module_countableAB4Star {A : Type u} [CommRing A] :
    CountableAB4Star (ModuleCat.{v} A) := by
  let F := forget₂ (ModuleCat.{v} A) AddCommGrpCat.{v}
  let : F.PreservesEpimorphisms := ⟨fun {X Y} f _ ↦ by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact (ModuleCat.epi_iff_surjective f).mp inferInstance⟩
  let := Functor.preservesHomology_of_preservesEpis_and_kernels F
  let := Functor.preservesFiniteColimits_of_preservesHomology F
  exact ⟨fun J ↦ HasExactLimitsOfShape.domain_of_functor (Discrete J) F⟩

private theorem point_sections_bounded (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ)
    (hC : sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C)) :
    ∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u + 1} (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))) i).obj
        (DerivedCategory.Q.obj
          (((pointIntegralSections.{u} l E D.k).mapHomologicalComplex (.up ℤ)).obj C))) := by
  let A := scalarReductionSource.{u, u} l E (Spec (.of D.k))
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let B := ModuleCat.{u + 1} R
  let F := pointIntegralSections.{u} l E D.k
  let S := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))
  have : CountableAB4Star A := point_source_countableAB4Star l E D.k
  have : CountableAB4Star B := point_module_countableAB4Star
  obtain ⟨hPA, hQA, hHA⟩ := derivedCategory_countableProducts_core.{0} A
  let := hPA
  obtain ⟨hPB, hQB, hHB⟩ := derivedCategory_countableProducts_core.{0} B
  let := hPB
  have : PreservesLimitsOfShape (Discrete ℕ) (pointModuleSections D.k S) :=
    (ProEt.countableProducts_exact.{u, u, 0} (Spec (.of D.k)) S).2.1
      ℕ (ProEt.mk (𝟙 _))
  let : CommRing (((sheafCompose (ProEt.topology (Spec (.of D.k)))
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj.obj
        (op (ProEt.mk (𝟙 _)))) :=
    completedIntegralCoefficientCommRingUnrestricted l E (Spec (.of D.k)) _
  have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
      (pointIntegralSectionMap l E D.k)).IsRightAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
      (pointIntegralSectionMap l E D.k)).isRightAdjoint
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    exact comp_preservesLimitsOfShape (pointModuleSections D.k S)
      (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} (pointIntegralSectionMap l E D.k))
  have : PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory :=
    exact_derived_preserves_products F
  let K := DerivedCategory.Q.obj C
  let L := fun n : ℕ ↦ (sfDerivedReductionRestricted l E (Spec (.of D.k)) n).obj K
  obtain ⟨hprod, δ, hT⟩ := hC.1
  let := hprod
  have hL : IsDerivedLimit
      (fun n ↦ (sfDerivedReductionTransition l E (Spec (.of D.k)) n).app K) K :=
    ⟨_, δ, hT⟩
  have hFL := exact_map_roos F L _ K hL
  obtain ⟨a, b, hab, hred⟩ := hC.2
  have hbound : ∀ n i, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor B i).obj (F.mapDerivedCategory.obj (L n))) := by
    intro n i hi
    let G := scalarReductionRestriction.{u, u} l E (Spec (.of D.k)) n
    let X := (scalarReductionDerivedExtension.{u, u} l E (Spec (.of D.k)) n).obj K
    have hz : IsZero ((DerivedCategory.homologyFunctor _ i).obj X) := by
      by_contra h
      have := (hred n).2 h
      simp only [Set.mem_Icc] at this
      omega
    have hzG : IsZero ((DerivedCategory.homologyFunctor A i).obj
        (G.mapDerivedCategory.obj X)) :=
      IsZero.of_iso (G.map_isZero hz) ((G.mapDerivedCategoryHomologyFunctorIso i).symm.app X)
    exact IsZero.of_iso (F.map_isZero hzG)
      ((F.mapDerivedCategoryHomologyFunctorIso i).symm.app (L n))
  obtain ⟨s, hs⟩ := bounded_of_roos_triangle
    (fun n ↦ F.mapDerivedCategory.obj (L n)) _ (F.mapDerivedCategory.obj K)
    hFL a b (hHB ℕ) hbound
  refine ⟨s, fun i hi ↦ ?_⟩
  exact IsZero.of_iso (hs i hi)
    ((DerivedCategory.homologyFunctor B i).mapIso (F.mapDerivedCategoryFactors.app C)).symm

private theorem scalar_zero_iso {R : Type*} [CommRing R]
    {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    {X Y : A} (e : X ≅ Y) (r : R) (h : r • 𝟙 Y = 0) : r • 𝟙 X = 0 := by
  apply (cancel_mono e.hom).mp
  calc
    _ = e.hom ≫ (r • 𝟙 Y) := by
      rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
    _ = 0 ≫ e.hom := by simp [h]

section ScalarNilpotence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E] (k : Type u) [Field k]
private theorem projection_scalar (n : ℕ)
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) :
    ((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k)))))) (pointIntegralSectionMap l E k a) =
    pointConstantSectionMap k (Padic.coefficientExtensionRing l E (n + 1))
      (RingHom.ulift (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))) a) := by
  let U := op (ProEt.mk (𝟙 (Spec (.of k))))
  have h := limit.lift_π (integralConstantCoefficientCone l E (Spec (.of k))) (op n)
  have h' := congrArg (fun f ↦ (f.hom.app U)
    (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E) a)) h
  change _ = _ at h'
  change _ = _
  rw [show ((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      U) (pointIntegralSectionMap l E k a) =
    ((integralConstantQuotientRingMap l E (Spec (.of k)) n).hom.app U)
      (pointConstantSectionMap k (Padic.coefficientExtensionIntegers l E) a) from h']
  let : EssentiallySmall.{u + 1} (Scheme.ProEt (Spec (.of k))) :=
    essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology (Spec (.of k))) CommRingCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite _ _
  let q : CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)) ⟶
      CommRingCat.of (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))) :=
    CommRingCat.ofHom (RingHom.ulift
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1))))
  have hn := toSheafify_naturality (ProEt.topology (Spec (.of k)))
    ((Functor.const (Scheme.ProEt (Spec (.of k)))ᵒᵖ).map q)
  exact congrArg (fun f ↦ (f.app U).hom a) hn.symm

private theorem restricted_sections_nilpotent (n : ℕ)
    (X : DerivedCategory (scalarReductionTarget.{u, u} l E (Spec (.of k)) n))
    (a : ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E))
    (ha : a ∈ Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}) :
    let F := pointIntegralSections l E k
    let G := scalarReductionRestriction.{u, u} l E (Spec (.of k)) n
    ∀ [PreservesFiniteLimits F] [PreservesFiniteColimits F]
      [PreservesFiniteLimits G] [PreservesFiniteColimits G],
    (a ^ (n + 1)) • 𝟙 (F.mapDerivedCategory.obj (G.mapDerivedCategory.obj X)) = 0 := by
  intro F G _ _ _ _
  let P := DerivedCategory.Q.objPreimage X
  let e := F.mapDerivedCategory.mapIso (G.mapDerivedCategory.mapIso
      (DerivedCategory.Q.objObjPreimageIso X).symm) ≪≫
    F.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app P) ≪≫
    F.mapDerivedCategoryFactors.app ((G.mapHomologicalComplex (.up ℤ)).obj P)
  let C := (F.mapHomologicalComplex (.up ℤ)).obj
    ((G.mapHomologicalComplex (.up ℤ)).obj P)
  have hq : RingHom.ulift
      (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)))
      (a ^ (n + 1)) = 0 := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    have hab : a.down = b.down * Padic.coefficientExtensionUniformizer l E :=
      congrArg ULift.down hb.symm
    apply ULift.ext
    change Ideal.Quotient.mk _ (a.down ^ (n + 1)) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Padic.coefficientExtensionIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    rw [hab, mul_pow]
    exact dvd_mul_left _ _
  have hC : (a ^ (n + 1)) • 𝟙 C = 0 := by
    ext i x
    change ((completedIntegralCommRingProjectionUnrestricted l E (Spec (.of k)) n).hom.app
      (op (ProEt.mk (𝟙 (Spec (.of k))))))
      (pointIntegralSectionMap l E k (a ^ (n + 1))) •
        (show (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of k))))) from x) = 0
    rw [projection_scalar, hq, map_zero, zero_smul]
  have hd : (a ^ (n + 1)) • 𝟙 (DerivedCategory.Q.obj C) = 0 := by
    calc
      _ = DerivedCategory.Q.map ((a ^ (n + 1)) • 𝟙 C) := by
        rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
      _ = 0 := by rw [hC, CategoryTheory.Functor.map_zero]
  exact scalar_zero_iso e _ hd

end ScalarNilpotence

private theorem finite_quotient_of_finite_cone
    {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    (C : CochainComplex (ModuleCat.{v} R) ℤ)
    (r : R) (i : ℤ)
    (hfin : Finite ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i).obj
      (CochainComplex.mappingCone (r • 𝟙 C)))) :
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).obj
      (DerivedCategory.Q.obj C)
    Finite (N ⧸ ((Ideal.span {r}) • ⊤ : Submodule R N)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} R) i
  have hSC : (HomologicalComplex.shortComplexFunctor
      (ModuleCat.{v} R) (.up ℤ) i).Linear R := ⟨by intros; rfl⟩
  have hCH : (HomologicalComplex.homologyFunctor
      (ModuleCat.{v} R) (.up ℤ) i).Linear R :=
    Functor.linear_of_iso _
      (HomologicalComplex.homologyFunctorIso (ModuleCat.{v} R) (.up ℤ) i).symm
  have hHL : H.Linear R := by
    let : Localization.Lifting DerivedCategory.Q
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ))
        (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i) H :=
      ⟨DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i⟩
    exact (Localization.functor_linear_iff DerivedCategory.Q
      (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ)) R
      (HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i) H).mp hCH
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (r • 𝟙 C))
  have hT := DerivedCategory.mappingCone_triangle_distinguished (r • 𝟙 C)
  let S := ShortComplex.mk (H.map T.mor₁) (H.map T.mor₂)
    (by rw [← H.map_comp, CategoryTheory.Pretriangulated.comp_distTriang_mor_zero₁₂ T hT,
      H.map_zero])
  have hS : S.Exact := DerivedCategory.HomologySequence.exact₂ T hT i
  have hf : S.f = r • 𝟙 (H.obj (DerivedCategory.Q.obj C)) := by
    change H.map (DerivedCategory.Q.map (r • 𝟙 C)) = _
    simp [CategoryTheory.Functor.map_smul]
  have hrange : LinearMap.range S.f.hom =
      ((Ideal.span {r}) • ⊤ : Submodule R S.X₂) := by
    rw [hf, Submodule.ideal_span_singleton_smul]
    ext x
    simp only [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists,
      Submodule.mem_top, true_and]
    change (∃ y, r • y = x) ↔ (∃ y, r • y = x)
    rfl
  have hker : LinearMap.ker S.g.hom =
      ((Ideal.span {r}) • ⊤ : Submodule R S.X₂) :=
    hS.moduleCat_range_eq_ker.symm.trans hrange
  let g := ((Ideal.span {r}) • ⊤ : Submodule R S.X₂).liftQ S.g.hom hker.ge
  have hg : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have : Finite S.X₃ := Finite.of_equiv _
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i).app
      (CochainComplex.mappingCone (r • 𝟙 C))).toLinearEquiv.symm.toEquiv
  exact Finite.of_injective g hg

/-- Integral sections have bounded derived-complete cohomology and finite residue.
Source: the point evaluation assertion in blueprint `lemma-perfect-complexes-geometric-point`,
steps 3--5 of `lem-weil-point-sections-finiteness`; Stacks Tags 091W, 093M and 091P.
(blueprint: lem-weil-point-sections-integral-cohomology-control).

Proof: choose the common cohomological interval [a,b] for the derived reductions.
Exact point sections and finite-torsion finiteness give finite reduction cohomology in
that interval. Sections preserve products and the Roos triangle defining integral
completeness. Products of modules are exact coordinatewise; their homology is the
product of the homologies. The Roos long exact sequence therefore bounds sections
in [a,b+1]. Every element of the uniformizer ideal acts nilpotently on each reduction,
so the nilpotent-torsion derived-limit criterion gives derived completeness of sections.
Finally specialize the existing point-sections derived-reduction comparison to
exponent one. Its cone assertion identifies the first reduced section object, after
restriction of scalars, with the uniformizer cone. Exact finite sections identify
its cohomology with the finite sections of reduced constructible cohomology sheaves.
The cone long exact sequence injects cohomology modulo the uniformizer into this
finite cohomology module. Thus each residue module is finite. No surjectivity of
transition maps on cohomology is asserted or needed. -/
theorem point_sections_integral_cohomology_control (D : FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (C : CochainComplex (scalarReductionSource.{u, u} l E (Spec (.of D.k))) ℤ)
    (hC : sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj C)) :
    let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
    let I : Ideal R := Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)}
    let M := DerivedCategory.Q.obj
      (((pointIntegralSections.{u} l E D.k).mapHomologicalComplex (.up ℤ)).obj C)
    (∃ s : Finset ℤ, ∀ i : ℤ, i ∉ s →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M)) ∧
    DerivedCategory.IsDerivedComplete I M ∧
    ∀ i : ℤ, let N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj M
      Finite (N ⧸ (I • ⊤ : Submodule R N)) := by
  let A := scalarReductionSource.{u, u} l E (Spec (.of D.k))
  let R := ULift.{u + 1, u} (Padic.coefficientExtensionIntegers l E)
  let B := ModuleCat.{u + 1} R
  let F := pointIntegralSections.{u} l E D.k
  let S := completedIntegralCommRingSheafUnrestricted l E (Spec (.of D.k))
  refine ⟨point_sections_bounded D l E C hC, ?_, ?_⟩
  · have : CountableAB4Star A := point_source_countableAB4Star l E D.k
    have : CountableAB4Star B := point_module_countableAB4Star
    obtain ⟨hPA, hQA, hHA⟩ := derivedCategory_countableProducts_core.{0} A
    let := hPA
    obtain ⟨hPB, hQB, hHB⟩ := derivedCategory_countableProducts_core.{0} B
    let := hPB
    have : PreservesLimitsOfShape (Discrete ℕ) (pointModuleSections D.k S) :=
      (ProEt.countableProducts_exact.{u, u, 0} (Spec (.of D.k)) S).2.1
        ℕ (ProEt.mk (𝟙 _))
    let : CommRing (((sheafCompose (ProEt.topology (Spec (.of D.k)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj.obj
          (op (ProEt.mk (𝟙 _)))) :=
      completedIntegralCoefficientCommRingUnrestricted l E (Spec (.of D.k)) _
    have : (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
        (pointIntegralSectionMap l E D.k)).IsRightAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{0, u + 1, u + 1}
        (pointIntegralSectionMap l E D.k)).isRightAdjoint
    have : PreservesLimitsOfShape (Discrete ℕ) F := by
      exact comp_preservesLimitsOfShape (pointModuleSections D.k S)
        (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1}
          (pointIntegralSectionMap l E D.k))
    have : PreservesLimitsOfShape (Discrete ℕ) F.mapDerivedCategory :=
      exact_derived_preserves_products F
    let K := DerivedCategory.Q.obj C
    let L := fun n : ℕ ↦
      (sfDerivedReductionRestricted l E (Spec (.of D.k)) n).obj K
    obtain ⟨hprod, δ, hT⟩ := hC.1
    let := hprod
    have hL : IsDerivedLimit
        (fun n ↦ (sfDerivedReductionTransition l E (Spec (.of D.k)) n).app K) K :=
      ⟨_, δ, hT⟩
    have hFL := exact_map_roos F L _ K hL
    have hnil : ∀ (a : R), a ∈ Ideal.span
        {ULift.up (Padic.coefficientExtensionUniformizer l E)} → ∀ n : ℕ, ∃ e : ℕ,
        1 ≤ e ∧ (a ^ e) • 𝟙 (F.mapDerivedCategory.obj (L n)) = 0 := by
      intro a ha n
      refine ⟨n + 1, by omega, ?_⟩
      let G := scalarReductionRestriction.{u, u} l E (Spec (.of D.k)) n
      let X := (scalarReductionDerivedExtension.{u, u} l E
        (Spec (.of D.k)) n).obj K
      have hz := restricted_sections_nilpotent l E D.k n X a ha
      exact hz
    exact DerivedCategory.isDerivedComplete_of_isDerivedLimit_of_nilpotent
      (Ideal.span {ULift.up (Padic.coefficientExtensionUniformizer l E)})
      (fun n ↦ F.mapDerivedCategory.obj (L n))
      (fun n ↦ F.mapDerivedCategory.map
        ((sfDerivedReductionTransition l E (Spec (.of D.k)) n).app K))
      hnil _ (roos_of_iso _ _ hFL (F.mapDerivedCategoryFactors.app C))
  · intro i
    let N := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).obj
      (DerivedCategory.Q.obj (((pointIntegralSections l E D.k).mapHomologicalComplex
        (.up ℤ)).obj C))
    let Csec := ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).obj C
    apply finite_quotient_of_finite_cone.{u + 1, u + 1, u + 1} Csec
      (ULift.up (Padic.coefficientExtensionUniformizer l E)) i
    let : HasDerivedCategory.{u + 2} B := pointReductionModuleDerived R
    let : HasDerivedCategory.{u + 2} (ModuleCat.{u + 1}
        (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (0 + 1)))) :=
      pointReductionModuleDerived _
    let N' : sfIntegralConstructibleCategory l E (Spec (.of D.k)) :=
      ⟨DerivedCategory.Q.obj C, hC⟩
    obtain ⟨e, hcone, _⟩ := point_sections_derived_reduction D l E _hl 0
    obtain ⟨e⟩ := e
    obtain ⟨ec⟩ := hcone N' Csec ⟨(F.mapDerivedCategoryFactors.app C).symm⟩
    let G := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (0 + 1))
    let Bfin := ModuleCat.{u + 1}
      (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (0 + 1)))
    let X := (scalarReductionDerivedExtension l E (Spec (.of D.k)) 0).obj N'.obj
    let Q := ModuleCat.restrictScalars (pointReductionQuotient l E 0)
    have hred := (hC.2.choose_spec.choose_spec.2 0).1
    have hfin : Finite (G.obj ((DerivedCategory.homologyFunctor _ i).obj X)) := by
      let : Finite (Padic.coefficientExtensionRing l E (0 + 1)) :=
        Padic.finite_coefficientExtensionRing l E 1 (by omega)
      exact point_finiteSections_finite_of_constructible D.k _ _ (hred.2 i)
    let es := (G.mapDerivedCategoryHomologyFunctorIso i).app X
    have hsec : Finite ((DerivedCategory.homologyFunctor.{u + 2} Bfin i).obj
        (G.mapDerivedCategory.obj X)) :=
      @Finite.of_equiv _ _ hfin es.toLinearEquiv.toEquiv
    let et := Q.mapDerivedCategory.mapIso (e.app N')
    let er := (Q.mapDerivedCategoryHomologyFunctorIso i).app (G.mapDerivedCategory.obj X)
    have hrestricted : Finite (Q.obj ((DerivedCategory.homologyFunctor.{u + 2} Bfin i).obj
        (G.mapDerivedCategory.obj X))) := by
      change Finite ((DerivedCategory.homologyFunctor.{u + 2} Bfin i).obj
        (G.mapDerivedCategory.obj X))
      exact hsec
    have hcoh : Finite ((DerivedCategory.homologyFunctor.{u + 2} B i).obj
        (Q.mapDerivedCategory.obj (G.mapDerivedCategory.obj X))) :=
      @Finite.of_equiv _ _ hrestricted er.toLinearEquiv.toEquiv
    let ef := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} R) i).mapIso
      (et.symm ≪≫ ec)
    have hconeFin := @Finite.of_equiv _ _ hcoh ef.toLinearEquiv.toEquiv
    have ecfin := (DerivedCategory.homologyFunctorFactors B i).app
      (CochainComplex.mappingCone
        ((ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (0 + 1)) • 𝟙 Csec))
    simpa only [Nat.zero_add, pow_one] using
      (@Finite.of_equiv _ _ hconeFin ecfin.toLinearEquiv.toEquiv)

end WeilConjectures
