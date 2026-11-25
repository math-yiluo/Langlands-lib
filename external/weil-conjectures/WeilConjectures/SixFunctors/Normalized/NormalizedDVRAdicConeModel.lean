/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Normalized.NormalizedDVRTower
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRFlatCokernel
import WeilConjectures.SixFunctors.Normalized.NormalizedDVRBoundedFreeCone
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
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
import all WeilConjectures.SixFunctors.Normalized.NormalizedDVRKFlatTransition
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralFiniteQuotientHomExt
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralScalarRegular
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.Algebra.Homology.RegularQuotientCone.RegularQuotientConeBasic

/-! # Strict adic cone model for a normalized DVR Roos limit -/

@[expose] public noncomputable section
set_option autoImplicit false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
set_option linter.style.haveILetI false
universe d t u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ZeroObject ChangeOfRings
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : AlgebraicGeometry.Scheme.{t})
  (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)
/-- The canonical standard derived category, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal1 :
    HasDerivedCategory (completedIntegralModuleSheaves l E X D hl) :=
  HasDerivedCategory.standard _
attribute [local instance] normalizedDVRAdicConeModelLocal1
/-- The canonical size witness, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal2 :
    EssentiallySmall.{max u (t + 1)} X.ProEt :=
  essentiallySmallSelf.{u} X.ProEt
attribute [local instance 10000] normalizedDVRAdicConeModelLocal2
/-- Canonical abelian sheafification, registered only in this file. -/
abbrev normalizedDVRAdicConeModelLocal3 :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology X)
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} X
attribute [local instance 10000] normalizedDVRAdicConeModelLocal3
/-- The canonical locally bijective sheafification criterion, registered locally. -/
abbrev normalizedDVRAdicConeModelLocal4 :
    (AlgebraicGeometry.Scheme.ProEt.topology X).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} X
attribute [local instance 10000] normalizedDVRAdicConeModelLocal4

section FlatScalar
universe c v r
open SheafOfModules SheafOfModules.RegularQuotientCone
  SheafOfModules.IndependentExtensionTensor MonoidalCategory
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
attribute [local instance] SheafOfModules.monoidalCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private instance (priority := 10000) flatScalarWeakSheafify :
    HasWeakSheafify J AddCommGrpCat.{r} := HasSheafify.isRightAdjoint

private theorem scalar_tensor_unit
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (N : Modules R) :
    (scalar R t).app N ≫ (regularTensorIso N).inv =
      (regularTensorIso N).inv ≫ (tensorRight N).map
        ((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))) := by
  ext U x
  change (regularTensorIso N).inv.val.app U ((show R.obj.obj U from t.val U) • x) =
    (((scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))) ▷ N).val.app U
      ((regularTensorIso N).inv.val.app U x)
  let μ := (scalar R t).app (unit (derivedChangeRingIndependentCoefficients J R))
  have hn := tensorPresheafUnit_whiskerRight_apply (R := R)
    (L := unit (derivedChangeRingIndependentCoefficients J R))
    (L' := unit (derivedChangeRingIndependentCoefficients J R)) μ N U
    (1 : R.obj.obj U) x
  have hb : (1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] ((show R.obj.obj U from t.val U) • x) =
      ((show R.obj.obj U from t.val U) • (1 : R.obj.obj U)) ⊗ₜ[R.obj.obj U] x :=
    TensorProduct.tmul_smul (R := R.obj.obj U)
      (show R.obj.obj U from t.val U) (1 : R.obj.obj U) x
  calc
    _ = (tensorPresheafUnit (R := R)
        (unit (derivedChangeRingIndependentCoefficients J R)) N).app U
        ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] ((show R.obj.obj U from t.val U) • x)) :=
      regularTensorIso_inv_apply (R := R) N U ((show R.obj.obj U from t.val U) • x)
    _ = (tensorPresheafUnit (R := R)
        (unit (derivedChangeRingIndependentCoefficients J R)) N).app U
        (((show R.obj.obj U from t.val U) • (1 : R.obj.obj U)) ⊗ₜ[R.obj.obj U] x) :=
      congrArg (fun z ↦ (tensorPresheafUnit (R := R)
        (unit (derivedChangeRingIndependentCoefficients J R)) N).app U z) hb
    _ = ((μ ▷ N).val.app U)
        ((tensorPresheafUnit (R := R)
          (unit (derivedChangeRingIndependentCoefficients J R)) N).app U
          ((1 : R.obj.obj U) ⊗ₜ[R.obj.obj U] x)) := hn.symm
    _ = _ := congrArg (fun z ↦ ((μ ▷ N).val.app U) z)
      (regularTensorIso_inv_apply (R := R) N U x).symm

attribute [local irreducible] SheafOfModules.IndependentExtensionTensor.regularTensorIso

private theorem flatScalar_exact
    (s t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (hzero : ∀ U : Cᵒᵖ,
      (show R.obj.obj U from s.val U) * (show R.obj.obj U from t.val U) = 0)
    (hexact : ∀ U : Cᵒᵖ,
      Function.Exact (fun x : R.obj.obj U ↦ (show R.obj.obj U from s.val U) * x)
        (fun x ↦ (show R.obj.obj U from t.val U) * x))
    (N : Modules R) (hflat : exactFunctor _ _ (tensorRight N)) :
    (ShortComplex.mk ((scalar R s).app N) ((scalar R t).app N) (by
      ext U x
      change (show R.obj.obj U from t.val U) •
        ((show R.obj.obj U from s.val U) • x) = 0
      rw [smul_smul, mul_comm, hzero, zero_smul])).Exact := by
  let A := unit (derivedChangeRingIndependentCoefficients J R)
  let S := ShortComplex.mk ((scalar R s).app A) ((scalar R t).app A) (by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let x' : R.obj.obj U := x
    change (show R.obj.obj U from t.val U) *
      ((show R.obj.obj U from s.val U) * x') = 0
    rw [← mul_assoc, mul_comm (show R.obj.obj U from t.val U), hzero, zero_mul])
  have hS : S.Exact := by
    apply (toSheaf (derivedChangeRingIndependentCoefficients J R)).reflects_exact_of_faithful
    apply (sheafToPresheaf J AddCommGrpCat.{r}).reflects_exact_of_faithful
    rw [ShortComplex.exact_iff_evaluation]
    intro U
    exact (ShortComplex.ab_exact_iff_function_exact _).2 (hexact U)
  letI : PreservesFiniteLimits (tensorRight N) := hflat.1
  letI : PreservesFiniteColimits (tensorRight N) := hflat.2
  let e := regularTensorIso N
  have he (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections) :
      (tensorRight N).map ((scalar R t).app A) ≫ e.hom = e.hom ≫ (scalar R t).app N := by
    apply (cancel_epi e.inv).1
    change e.inv ≫ (tensorRight N).map ((scalar R t).app A) ≫ e.hom =
      e.inv ≫ e.hom ≫ (scalar R t).app N
    rw [← Category.assoc, ← scalar_tensor_unit R t N, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Iso.inv_hom_id_assoc]
  exact (ShortComplex.exact_iff_of_iso
    (ShortComplex.isoMk e e e (he s).symm (he t).symm)).1
      (hS.map (tensorRight N))

end FlatScalar

private structure FiniteFlatModel (j : ℕ) (L : normalizedDVRDerived l E X j) where
  P : CochainComplex (normalizedDVRModules l E X j) ℤ
  iso : (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj P ≅ L
  flat (i : ℤ) : exactFunctor _ _
    (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E X j))
      (P.X i))
  kflat : CochainComplex.IsKFlatIndependentCoefficients P

private theorem finite_flat_representative (j : ℕ)
    (L : normalizedDVRDerived l E X j) : Nonempty (FiniteFlatModel l E X j L) := by
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X j)
  let G := DerivedCategory.Q.objPreimage L
  obtain ⟨P, q, hk, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := integralCoefficientCommRingSheaf l E X j) G
  have : QuasiIso q := hq
  exact ⟨⟨P, asIso (DerivedCategory.Q.map q) ≪≫
    DerivedCategory.Q.objObjPreimageIso L, hflat, hk⟩⟩

private theorem finite_flat_representative_map (j : ℕ)
    {L : normalizedDVRDerived l E X j} (A : FiniteFlatModel l E X j L)
    {L' : normalizedDVRDerived l E X (j + 1)}
    (f : L' ⟶ (normalizedDVRRes l E X j.le_succ).obj L) :
    ∃ (B : FiniteFlatModel l E X (j + 1) L')
      (g : B.P ⟶ ((normalizedDVRModuleRes l E X j.le_succ).mapHomologicalComplex
        (.up ℤ)).obj A.P),
      DerivedCategory.Q.map g ≫
          (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app A.P ≫
          (normalizedDVRRes l E X j.le_succ).map A.iso.hom = B.iso.hom ≫ f := by
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X j)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X (j + 1))
  let F := normalizedDVRModuleRes l E X j.le_succ
  let Y := DerivedCategory.Q.objPreimage L'
  let eY : DerivedCategory.Q.obj Y ≅ L' := DerivedCategory.Q.objObjPreimageIso L'
  let φ : DerivedCategory.Q.obj Y ⟶
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj A.P) :=
    eY.hom ≫ f ≫ (normalizedDVRRes l E X j.le_succ).map A.iso.inv ≫
      F.mapDerivedCategoryFactors.hom.app A.P
  obtain ⟨Z, s, hs, g, hφ⟩ := DerivedCategory.right_fac φ
  obtain ⟨P', q, hk, hflat, hq, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology X)
      (R := integralCoefficientCommRingSheaf l E X (j + 1)) Z
  have : QuasiIso q := hq
  refine ⟨⟨P', asIso (DerivedCategory.Q.map q) ≪≫
    asIso (DerivedCategory.Q.map s) ≪≫ eY, hflat, hk⟩, q ≫ g, ?_⟩
  have hg : DerivedCategory.Q.map g = DerivedCategory.Q.map s ≫ φ := by
    rw [hφ, IsIso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc, hg, φ, F]
  simp

private def finiteModel (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    FiniteFlatModel l E X j (T.M j) :=
  Nat.rec (motive := fun j ↦ FiniteFlatModel l E X j (T.M j))
    (finite_flat_representative l E X 0 (T.M 0)).some
    (fun j A ↦ (finite_flat_representative_map l E X j A (T.tau j.le_succ)).choose) j

private def finiteModelMap (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    (finiteModel l E X D hl T (j + 1)).P ⟶
      ((normalizedDVRModuleRes l E X j.le_succ).mapHomologicalComplex (.up ℤ)).obj
        (finiteModel l E X D hl T j).P :=
  (finite_flat_representative_map l E X j (finiteModel l E X D hl T j)
    (T.tau j.le_succ)).choose_spec.choose

private theorem finiteModelMap_spec (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    DerivedCategory.Q.map (finiteModelMap l E X D hl T j) ≫
      (normalizedDVRModuleRes l E X j.le_succ).mapDerivedCategoryFactors.inv.app
        (finiteModel l E X D hl T j).P ≫
      (normalizedDVRRes l E X j.le_succ).map (finiteModel l E X D hl T j).iso.hom =
    (finiteModel l E X D hl T (j + 1)).iso.hom ≫ T.tau j.le_succ :=
  (finite_flat_representative_map l E X j (finiteModel l E X D hl T j)
    (T.tau j.le_succ)).choose_spec.choose_spec

attribute [local irreducible] finiteModel finiteModelMap

private abbrev Scalar := normalizedDVRScalars l E X

private abbrev scalarUniformizer := normalizedDVRUniformizer l E X

private instance completedRestrictionAdditive (j : ℕ) :
    (completedIntegralRestrictScalars l E X D hl j).Additive :=
  inferInstanceAs (SheafOfModules.restrictScalars.{max u (t + 1)}
    (completedIntegralCoefficientProjection l E X D hl j)).Additive

private instance completedRestrictionLimits (j : ℕ) :
    PreservesFiniteLimits (completedIntegralRestrictScalars l E X D hl j) :=
  (completedIntegralRestrictScalars_exact l E X D hl j).1

private instance completedRestrictionColimits (j : ℕ) :
    PreservesFiniteColimits (completedIntegralRestrictScalars l E X D hl j) :=
  (completedIntegralRestrictScalars_exact l E X D hl j).2

private abbrev completedRestrictionComp {m n : ℕ} (h : n ≤ m) :=
  normalizedDVRFlatRestrictionComp l E X D hl h

private abbrev modelTower (T : NormalizedDVRTower l E X D hl) :=
  normalizedDVRFlatTower l E X D hl (fun j ↦ (finiteModel l E X D hl T j).P)
    (finiteModelMap l E X D hl T)

private def modelTowerIso (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    DerivedCategory.Q.obj ((modelTower l E X D hl T).obj (op (j + 1))) ≅
      (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower :=
  ((completedIntegralRestrictScalars l E X D hl j).mapDerivedCategoryFactors.app _).symm ≪≫
    (normalizedDVRResCompleted l E X D hl j).mapIso
      (finiteModel l E X D hl T j).iso ≪≫ (T.evaluationIso j).symm

private theorem completedRestrictionComp_fac {m n : ℕ} (h : n ≤ m)
    (P : CochainComplex (normalizedDVRModules l E X n) ℤ) :
    (completedIntegralRestrictScalars l E X D hl m).mapDerivedCategoryFactors.inv.app
        (((normalizedDVRModuleRes l E X h).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (normalizedDVRResCompleted l E X D hl m).map
        ((normalizedDVRModuleRes l E X h).mapDerivedCategoryFactors.inv.app P) ≫
      (normalizedDVRResCompletedComp l E X D hl h).hom.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso
        (completedRestrictionComp l E X D hl h) (.up ℤ)).hom.app P) ≫
      (completedIntegralRestrictScalars l E X D hl n).mapDerivedCategoryFactors.inv.app P := by
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X n)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X m)
  let F := normalizedDVRModuleRes l E X h
  let G := completedIntegralRestrictScalars l E X D hl m
  let H := completedIntegralRestrictScalars l E X D hl n
  let e := completedRestrictionComp l E X D hl h
  have he : normalizedDVRResCompletedComp l E X D hl h =
      Functor.mapDerivedCategoryCompIso F G ≪≫
        Functor.mapDerivedCategoryNatIso e := by
    rfl
  rw [he]
  have hfac := exactComp_fac F G H e P
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app P)).1
  simp only [Category.assoc]
  change G.mapDerivedCategoryFactors.inv.app _ ≫
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app P) ≫
      _ ≫ H.mapDerivedCategoryFactors.hom.app P =
    DerivedCategory.Q.map _ ≫ H.mapDerivedCategoryFactors.inv.app P ≫
      H.mapDerivedCategoryFactors.hom.app P
  rw [hfac]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc,
    Category.comp_id]

private theorem completedProjection_surjective (j : ℕ) (U : X.ProEtᵒᵖ) :
    Function.Surjective ((completedIntegralCoefficientProjection l E X D hl j).hom.app U) := by
  intro x
  obtain ⟨y, hy⟩ := AlgebraicGeometry.ProEtale.constantQuotient_surjective l E X j U x
  refine ⟨(integralConstantToCompletionOfUniverses l E X).hom.app U y, ?_⟩
  exact (congrArg (fun h ↦ h.hom.app U y)
    (limit.lift_π (integralConstantConeOfUniverses l E X) (op j))).trans hy

private theorem finiteScalar_exact (a b j : ℕ) (hj : j + 1 = a + b)
    (U : X.ProEtᵒᵖ) :
    Function.Exact
      (fun x : (integralCoefficientSheaf l E X j).obj.obj U ↦
        (completedIntegralCoefficientProjection l E X D hl j).hom.app U
          ((scalarUniformizer l E X).val U ^ a) * x)
      (fun x : (integralCoefficientSheaf l E X j).obj.obj U ↦
        (completedIntegralCoefficientProjection l E X D hl j).hom.app U
          ((scalarUniformizer l E X).val U ^ b) * x) := by
  let p := ((completedIntegralCoefficientProjection l E X D hl j).hom.app U).hom
  let s : (completedIntegralCoefficientSheaf l E X D hl).obj.obj U :=
    (scalarUniformizer l E X).val U
  intro x
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := completedProjection_surjective l E X D hl j U x
    have hz : p (s ^ b * y) = 0 := by
      rw [map_mul]
      exact hx
    obtain ⟨z, hzy⟩ := AlgebraicGeometry.ProEtale.completedIntegralProjection_divisible
      l E X j U (s ^ b * y) hz
    let z' : (completedIntegralCoefficientSheaf l E X D hl).obj.obj U := z
    have hzy' : s ^ b * y = s ^ (a + b) * z' := by
      change s ^ b * y = s ^ (j + 1) * z' at hzy
      simpa only [hj] using hzy
    have hy : y = s ^ a * z' := by
      apply AlgebraicGeometry.ProEtale.completedIntegralScalar_regular l E X b U
      change s ^ b * y = s ^ b * (s ^ a * z')
      rw [hzy', ← mul_assoc, ← pow_add, Nat.add_comm b a]
    refine ⟨p z', ?_⟩
    change p (s ^ a) * p z' = p y
    rw [← map_mul, ← hy]
  · rintro ⟨y, rfl⟩
    change p (s ^ b) * (p (s ^ a) * y) = 0
    rw [← mul_assoc, ← map_mul, ← pow_add, Nat.add_comm b a, ← hj]
    have hz := PrincipalKoszulStrictReplacement.scalar_projection_zero l E X j U
    change p (s ^ (j + 1)) = 0 at hz
    rw [hz, zero_mul]

private def finiteScalar (j k : ℕ) :
    (SheafOfModules.unit (integralCoefficientSheaf l E X j)).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ (completedIntegralCoefficientProjection l E X D hl j).hom.app U
      ((scalarUniformizer l E X).val U ^ k)) (by
        intro U V f
        have hn := congrArg (fun g ↦ g ((scalarUniformizer l E X).val U ^ k))
          ((completedIntegralCoefficientProjection l E X D hl j).hom.naturality f)
        change (completedIntegralCoefficientProjection l E X D hl j).hom.app V
          ((completedIntegralCoefficientSheaf l E X D hl).obj.map f
            ((scalarUniformizer l E X).val U ^ k)) = _ at hn
        have hs : (completedIntegralCoefficientSheaf l E X D hl).obj.map f
            ((scalarUniformizer l E X).val U) = (scalarUniformizer l E X).val V :=
          (PrincipalKoszulStrictReplacement.uniformizer l E X).property f
        rw [map_pow, hs] at hn
        exact hn.symm)

private theorem finiteScalar_flat_exact (a b j : ℕ) (hj : j + 1 = a + b)
    (N : normalizedDVRModules l E X j)
    (hflat : exactFunctor _ _ (@MonoidalCategory.tensorRight _ _
      (SheafOfModules.monoidalCategory (integralCoefficientCommRingSheaf l E X j)) N)) :
    ∃ hz, (ShortComplex.mk
      ((SheafOfModules.RegularQuotientCone.scalar
        (integralCoefficientCommRingSheaf l E X j) (finiteScalar l E X D hl j a)).app N)
      ((SheafOfModules.RegularQuotientCone.scalar
        (integralCoefficientCommRingSheaf l E X j) (finiteScalar l E X D hl j b)).app N)
      hz).Exact := by
  refine ⟨_, flatScalar_exact (integralCoefficientCommRingSheaf l E X j)
    (finiteScalar l E X D hl j a) (finiteScalar l E X D hl j b) ?_ ?_ N hflat⟩
  · intro U
    change (completedIntegralCoefficientProjection l E X D hl j).hom.app U
      ((scalarUniformizer l E X).val U ^ a) *
      (completedIntegralCoefficientProjection l E X D hl j).hom.app U
        ((scalarUniformizer l E X).val U ^ b) = 0
    rw [← map_mul, ← pow_add, ← hj]
    exact PrincipalKoszulStrictReplacement.scalar_projection_zero l E X j U
  · exact finiteScalar_exact l E X D hl a b j hj

private theorem modelTower_annihilated (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    scalarUniformizer l E X ^ j • 𝟙 ((modelTower l E X D hl T).obj (op j)) = 0 := by
  cases j with
  | zero =>
    exact (isZero_zero (CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)).eq_of_src
      _ _
  | succ j =>
    ext i U x
    change ((completedIntegralCoefficientProjection l E X D hl j).hom.app U
      ((scalarUniformizer l E X).val U ^ (j + 1))) •
        (show ((finiteModel l E X D hl T j).P.X i).val.obj U from x) = 0
    have hz := PrincipalKoszulStrictReplacement.scalar_projection_zero l E X j U
    change (completedIntegralCoefficientProjection l E X D hl j).hom.app U
      ((scalarUniformizer l E X).val U ^ (j + 1)) = 0 at hz
    rw [hz, zero_smul]

private theorem modelTower_exact (T : NormalizedDVRTower l E X D hl) (a b : ℕ) :
    (ShortComplex.mk
      (scalarUniformizer l E X ^ a • 𝟙 ((modelTower l E X D hl T).obj (op (a + b))))
      (scalarUniformizer l E X ^ b • 𝟙 ((modelTower l E X D hl T).obj (op (a + b)))) (by
        rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add, Nat.add_comm,
          modelTower_annihilated])).Exact := by
  have hex (j : ℕ) (hj : j + 1 = a + b) :
      ∃ hz, (ShortComplex.mk
        (scalarUniformizer l E X ^ a • 𝟙 ((modelTower l E X D hl T).obj (op (j + 1))))
        (scalarUniformizer l E X ^ b • 𝟙 ((modelTower l E X D hl T).obj (op (j + 1))))
        hz).Exact := by
    have hz : (scalarUniformizer l E X ^ a •
        𝟙 ((modelTower l E X D hl T).obj (op (j + 1)))) ≫
        (scalarUniformizer l E X ^ b •
          𝟙 ((modelTower l E X D hl T).obj (op (j + 1)))) = 0 := by
      rw [Linear.smul_comp, Category.id_comp, smul_smul, ← pow_add,
        ← hj]
      exact modelTower_annihilated l E X D hl T (j + 1)
    refine ⟨hz, HomologicalComplex.exact_of_degreewise_exact _ fun i ↦ ?_⟩
    obtain ⟨hz', he⟩ := finiteScalar_flat_exact l E X D hl a b j hj
      ((finiteModel l E X D hl T j).P.X i) ((finiteModel l E X D hl T j).flat i)
    let F := SheafOfModules.restrictScalars.{max u (t + 1)}
      (completedIntegralCoefficientProjection l E X D hl j)
    letI : PreservesFiniteLimits F :=
      completedRestrictionLimits l E X D hl j
    letI : PreservesFiniteColimits F :=
      completedRestrictionColimits l E X D hl j
    have he' := he.map F
    refine (ShortComplex.exact_iff_of_iso ?_).1 he'
    refine ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    · ext U x
      change (completedIntegralCoefficientProjection l E X D hl j).hom.app U
        ((scalarUniformizer l E X).val U ^ a) •
          (show ((finiteModel l E X D hl T j).P.X i).val.obj U from x) = _
      rfl
    · ext U x
      change (completedIntegralCoefficientProjection l E X D hl j).hom.app U
        ((scalarUniformizer l E X).val U ^ b) •
          (show ((finiteModel l E X D hl T j).P.X i).val.obj U from x) = _
      rfl
  cases b with
  | succ b => exact (hex (a + b) rfl).choose_spec
  | zero =>
    cases a with
    | succ a => exact (hex a rfl).choose_spec
    | zero =>
      apply ShortComplex.exact_of_isZero_X₂
      exact isZero_zero _

attribute [local irreducible] normalizedDVRUniformizer
  Functor.mapDerivedCategory normalizedDVRResCompletedComp
  completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence

private theorem modelTowerIso_successor (T : NormalizedDVRTower l E X D hl) (j : ℕ) :
    DerivedCategory.Q.map ((modelTower l E X D hl T).map
        (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (modelTowerIso l E X D hl T j).hom =
      (modelTowerIso l E X D hl T (j + 1)).hom ≫
        (normalizedDVRTowerTransition l E X D hl j.le_succ).app T.tower := by
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X j)
  letI := HasDerivedCategory.standard (normalizedDVRModules l E X (j + 1))
  have hfac := completedRestrictionComp_fac l E X D hl j.le_succ
    (finiteModel l E X D hl T j).P
  apply (cancel_mono (T.evaluationIso j).hom).1
  simp only [modelTower, normalizedDVRFlatTower, Functor.ofOpSequence_map_homOfLE_succ,
    normalizedDVRFlatComplexMap,
    modelTowerIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, T.tower_tau]
  have hnat := (normalizedDVRResCompletedComp l E X D hl j.le_succ).hom.naturality
    (finiteModel l E X D hl T j).iso.hom
  simp only [Functor.comp_obj, Functor.comp_map] at hnat
  rw [← Functor.map_comp_assoc (normalizedDVRResCompleted l E X D hl (j + 1))
    _ (T.tau j.le_succ), ← finiteModelMap_spec l E X D hl T j]
  simp only [Functor.map_comp, Category.assoc, hnat, Iso.app_inv]
  have hq :=
    (completedIntegralRestrictScalars l E X D hl (j + 1)).mapDerivedCategoryFactors.inv.naturality
      (finiteModelMap l E X D hl T j)
  dsimp only [Functor.comp_map] at hq
  rw [← reassoc_of% hq, reassoc_of% hfac]

private theorem modelTower_normalized (T : NormalizedDVRTower l E X D hl) :
    CochainComplex.IsNormalizedAdicTower (scalarUniformizer l E X)
      (modelTower l E X D hl T) := by
  refine ⟨modelTower_annihilated l E X D hl T, ?_, modelTower_exact l E X D hl T⟩
  intro n m h
  exact normalizedDVR_flat_cokernel l E X D hl
    (fun j ↦ (finiteModel l E X D hl T j).P) (finiteModelMap l E X D hl T)
    T (fun j ↦ (finiteModel l E X D hl T j).iso)
    (finiteModelMap_spec l E X D hl T)
    (fun j i ↦ (finiteModel l E X D hl T j).flat i)
    (fun j ↦ (finiteModel l E X D hl T j).kflat)
    (modelTower_annihilated l E X D hl T) h

private theorem completed_exact_products :
    CountableAB4Star (completedIntegralModuleSheaves l E X D hl) := by
  let A := completedIntegralModuleSheaves l E X D hl
  let R := completedIntegralCommRingSheafUnrestricted l E X
  constructor
  intro I _
  have : (lim : (Discrete I ⥤ A) ⥤ A).PreservesEpimorphisms := by
    constructor
    intro B C f hf
    let eB := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))
    let eC := HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := C))
    have h (i : I) : Epi (f.app ⟨i⟩) := inferInstance
    have : Epi (Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩)) :=
      (AlgebraicGeometry.Scheme.ProEt.countableProducts_exact X R).2.2 I _ _ _ h
    have hh : lim.map f = eB.hom ≫ Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ eC.inv := by
      apply limit.hom_ext
      rintro ⟨i⟩
      dsimp only [eB, eC]
      simp only [Category.assoc, HasLimit.isoOfNatIso_inv_π,
        Discrete.natIsoFunctor_inv_app]
      change lim.map f ≫ limit.π C ⟨i⟩ =
        (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := B))).hom ≫
          Limits.Pi.map (fun i : I ↦ f.app ⟨i⟩) ≫ Pi.π _ i
      rw [Pi.map_π, HasLimit.isoOfNatIso_hom_π_assoc]
      simp
    rw [hh]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi (C := A) (Discrete I)

private theorem completed_derived_products :
    Nonempty (HasLimitsOfShape (Discrete ℕ) (completedIntegralDerivedCategory l E X D hl)) := by
  letI : CountableAB4Star (completedIntegralModuleSheaves l E X D hl) :=
    completed_exact_products l E X D hl
  obtain ⟨hP, _⟩ := derivedCategory_countableProducts_core.{0}
    (completedIntegralModuleSheaves l E X D hl)
  letI := hP
  exact ⟨inferInstance⟩

/-- A strict normalized adic complex model and the bounded-free cone computation
of a finite scalar extension of a Roos limit.
Source: Bhatt--Scholze, Lemmas 3.5.4 and 3.5.5, regular-element case; Stacks 06YS,
05RT and 0941. (blueprint: lem-coef-normalized-dvr-adic-cone-model).

Proof: write the ring of integers as a DVR and choose a uniformizer. Its constant
action on the completed sheaf gives the indicated linear category. Successively use
right fractions and K-flat resolutions with flat terms to represent the finite
transitions by semilinear chain maps. After restriction to the completed sheaf these
give U; insert the zero complex at index zero. Flatness over each finite quotient
identifies the kernel of the b-th power with the image of the a-th power at level
a+b. The adjoint normalization gives quasi-isomorphisms from the termwise quotients
to the smaller levels. These are the three fields of IsNormalizedAdicTower.
The level identifications eU cover every positive level and intertwine every
successor map. Their products
transport the given Roos triangle to this strict model, retaining projections; no
fullness theorem for derived evaluation is needed. Remove the finite prefix n+1. Tensoring
with the two-term free resolution [R --uniformizer^(n+1)--> R] commutes with products
and the Roos cone, since only two terms and finite sums occur in every degree.
Consequently the restricted derived reduction of M is the homotopy limit c of the
cones, giving a. The augmentation of the multiplication cone to the quotient is
rho followed by desc followed by the normalized cokernel map. The ordinary tensor
adjunction on pure tensors and its derived normalization show that a, this cone
projection and the specified level identification compose to the restriction of the adjoint of
the original limit
projection. This proves the displayed equation, including all signs and projections.
No assertion that this map is invertible is used: invertibility follows separately
from the existing strict adic tower theorem. All exponents are n+1. -/
theorem normalizedDVR_adic_cone_model
    (T : NormalizedDVRTower l E X D hl)
    (M : completedIntegralDerivedCategory l E X D hl)
    [HasProduct (fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower)
    (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) ⟶
      M⟦(1 : ℤ)⟧)
    (hc : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower)
      M p δ) (n : ℕ)
    (adj : scalarReductionDerivedExtension l E X n ⊣
      scalarReductionDerivedRestriction l E X n) :
    ∃ (S : Type (max u (t + 1))) (hS : CommRing S), letI := hS
      ∃ (hlin : Linear S (completedIntegralModuleSheaves l E X D hl)), letI := hlin
      ∃ (hprod : HasLimitsOfShape (Discrete ℕ)
          (completedIntegralDerivedCategory l E X D hl)), letI := hprod
      ∃ (ϖ : S)
        (U : ℕᵒᵖ ⥤ CochainComplex (completedIntegralModuleSheaves l E X D hl) ℤ)
        (hU : CochainComplex.IsNormalizedAdicTower ϖ U)
        (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
          (normalizedDVRTowerEvaluation l E X D hl j).obj T.tower),
        (∀ j : ℕ,
          DerivedCategory.Q.map (U.map
              (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (eU j).hom =
            (eU (j + 1)).hom ≫
              (normalizedDVRTowerTransition l E X D hl j.le_succ).app T.tower) ∧
        ∃ (c : Cone (CochainComplex.IsNormalizedAdicTower.arrowTower
          (ϖ := ϖ) (T := U) (n + 1) ⋙ CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q)),
        CategoryTheory.Pretriangulated.IsHomotopyLimit c ∧
        ∃ (a : (scalarReductionDerivedRestriction l E X n).obj
              ((scalarReductionDerivedExtension l E X n).obj M) ≅ c.pt),
          (scalarReductionDerivedRestriction l E X n).map
              ((adj.homEquiv M (T.M n)).symm
                (p ≫ Pi.π _ n ≫ (T.evaluationIso n).hom)) =
            a.hom ≫ c.π.app (op 0) ≫ DerivedCategory.Q.map
              (CochainComplex.ConeCoimage.ρ.app _ ≫ CochainComplex.ConeCoimage.desc.app _ ≫
                hU.cokerDesc (n + 1) (op 0)) ≫ (eU n).hom ≫
                (T.evaluationIso n).hom := by
  classical
  let hprod := (completed_derived_products l E X D hl).some
  letI := hprod
  refine ⟨Scalar l E X, inferInstance, inferInstance, hprod,
    scalarUniformizer l E X, modelTower l E X D hl T,
    modelTower_normalized l E X D hl T, modelTowerIso l E X D hl T,
    modelTowerIso_successor l E X D hl T, ?_⟩
  exact normalizedDVR_bounded_free_cone l E X D hl T M p δ hc n adj
    (modelTower l E X D hl T) (modelTower_normalized l E X D hl T)
    (modelTowerIso l E X D hl T) (modelTowerIso_successor l E X D hl T)
    (finiteModel l E X D hl T n).P (Iso.refl _)
    (finiteModel l E X D hl T n).iso (by
      simp [modelTowerIso, Category.assoc])

end WeilConjectures
