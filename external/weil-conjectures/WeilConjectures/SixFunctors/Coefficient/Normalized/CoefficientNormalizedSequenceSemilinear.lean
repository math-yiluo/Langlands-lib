/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
public import WeilConjectures.AlgebraicGeometry.SemilinearSystemModels
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.SixFunctors.CoefficientClosedStructure.CoefficientRingedTensorHomModelSupplement
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
public import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import Mathlib.CategoryTheory.Limits.Final
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.CategoryTheory.Sites.CoverPreserving
import all WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement

/-! # Coefficient normalization as semilinear normalization

Source: Zheng Construction 4.1; Stacks 0941.
(blueprint: lem-coef-normalized-sequence-semilinear).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b c v w r
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

attribute [local implicit_reducible] CategoryTheory.uniformProd
  coefficientSequenceCommRingSheaf SemilinearSections.systemRing
  integralCoefficientSheaf integralCoefficientCommRingSheaf
  coefficientSequenceCommRingPresheaf coefficientSequenceCommRingSystem
  coefficientSequenceCommRingTransition coefficientSequenceEvaluation
  SemilinearSections.evaluation SemilinearSections.ringPresheaf SemilinearSections.rings
  CategoryTheory.sheafCompose CommRingCat.hasForgetToRingCat
  integralReductionTargetHasDerivedCategory coefficientFiniteHasDerived
  coefficientSequenceHasDerived
attribute [local irreducible] DerivedCategory _root_.instCategoryDerivedCategory
  DerivedCategory.Q DerivedCategory.Qh HasDerivedCategory.standard
  coefficientTotalTensor coefficientTensorGenerator CoefficientClosedStructure.tensor
  SheafOfModules.instPreadditive HomologicalComplex.instPreadditive
  SheafOfModules.monoidalCategory
  coefficientIntegralTensorModelIso coefficientFiniteTensorModelIso
  coefficientSystemTensorModelIso coefficientScalarTensorIso coefficientEvaluationTensorIso
  CoefficientTensorModels.iso coefficientEvaluationSection
  constantSheaf presheafToSheaf Functor.ofSequence Functor.ofOpSequence
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

-- Reuse already typed coefficient-site arguments; Lean's kernel checks the result.
local elab "kernel_exact " t:term : tactic => Lean.Elab.Tactic.withMainContext do
  let e ← Lean.Elab.Term.elabTerm t none
  (← Lean.Elab.Tactic.getMainGoal).assign e
  Lean.Elab.Tactic.replaceMainGoal []

private theorem abelian_transport_heq {A A' B B' : AddCommGrpCat.{u}}
    (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (hf : eqToHom hA.symm ≫ f ≫ eqToHom hB = g) :
    HEq (fun x ↦ f x) (fun x ↦ g x) := by
  subst A' B'
  apply heq_of_eq
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using
    congrArg (fun f ↦ fun x ↦ f x) hf

private theorem module_forget_heq {R : Type u} [Ring R]
    {M N : ModuleCat.{v} R} (f : M ⟶ N) :
    HEq (fun x ↦ ((forget₂ (ModuleCat R) AddCommGrpCat).map f) x)
      (fun x ↦ f x) := HEq.rfl

private theorem moduleNatTrans_heq
    {A : Type a} [Category.{b} A] {C : Type c} [Category.{v} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}
    {F F' G G' : A ⥤ SheafOfModules.{r} R} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G')
    (h : ∀ M U, HEq (fun x ↦ (α.app M).val.app U x)
      (fun x ↦ (β.app M).val.app U x)) : HEq α β := by
  subst F' G'
  apply heq_of_eq
  ext M U x
  exact congrFun (eq_of_heq (h M U)) x

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem restriction_eq {m n : ℕ} (h : n ≤ m) :
    SemilinearSections.res.{t + 1, t, max u (t + 1)}
      (SemilinearSections.coefficientMap (Scheme.ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) h) =
      normalizedDVRModuleRes l E W h := by
  apply congrArg SheafOfModules.restrictScalars
  have he := map_opSequence (sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat RingCat)) (coefficientSequenceCommRingTransition l E W) h
  have ht : (fun k ↦ (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat RingCat)).map (coefficientSequenceCommRingTransition l E W k)) =
        integralCoefficientSheafTransition l E W := by
    funext k
    rfl
  rw [ht] at he
  kernel_exact he

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
private theorem transition_heq {m n : ℕ} (h : n ≤ m) :
    HEq (SemilinearSections.transition.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) h)
        (coefficientSequenceTransition l E W h) := by
  apply moduleNatTrans_heq
    (show SemilinearSections.evaluation.{t + 1, t, max u (t + 1)}
      (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) m =
        coefficientSequenceEvaluation l E W m from rfl)
    (congrArg₂ (fun F G ↦ F ⋙ G)
      (show SemilinearSections.evaluation.{t + 1, t, max u (t + 1)}
        (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
        (coefficientSequenceCommRingTransition l E W) n =
          coefficientSequenceEvaluation l E W n from rfl)
      (restriction_eq l E W h))
  intro M U
  have hg := (SemilinearSections.transition_exists.{t + 1, t, max u (t + 1)}
    (Scheme.ProEt.topology W) (integralCoefficientCommRingSheaf l E W)
    (coefficientSequenceCommRingTransition l E W) h).exists.choose_spec M U
  have hc := abelian_transport_heq
    (coefficientSequenceEvaluationAb_eq l E W M m U)
    (coefficientSequenceRestrictedEvaluationAb_eq l E W M h U) _ _
    ((coefficientSequenceTransition_exists l E W h).exists.choose_spec M U)
  have hf := module_forget_heq
    ((((coefficientSequenceTransition_exists l E W h).exists.choose).app M).val.app U)
  simpa only [SemilinearSections.transition, coefficientSequenceTransition] using
    hg.trans (hf.symm.trans hc).symm

section LocalizedTransition
variable {A : Type a} [Category.{v} A] [Abelian A] [HasDerivedCategory A]
  {B : Type b} [Category.{w} B] [Abelian B] [HasDerivedCategory B]
  {D : Type c} [Category.{r} D] [Abelian D] [HasDerivedCategory D]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : A ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : D ⥤ B) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

private noncomputable def localizedTransition (δ : F ⟶ G ⋙ H) :
    F.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ H.mapDerivedCategory :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) _ _ F.mapDerivedCategory
    (G ⋙ H).mapDerivedCategory
    (Functor.whiskerRight (NatTrans.mapHomologicalComplex δ (.up ℤ)) DerivedCategory.Q) ≫
      (Functor.mapDerivedCategoryCompIso G H).inv

private theorem mapDerived_eq (H' : D ⥤ B)
    [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] (h : H = H') :
    H.mapDerivedCategory = H'.mapDerivedCategory := by
  subst H'
  rfl

private theorem localizedTransition_heq (H' : D ⥤ B)
    [H'.Additive] [PreservesFiniteLimits H'] [PreservesFiniteColimits H'] (h : H = H')
    (δ : F ⟶ G ⋙ H) (δ' : F ⟶ G ⋙ H') (hδ : HEq δ δ') :
    HEq (localizedTransition F G H δ) (localizedTransition F G H' δ') := by
  subst H'
  cases hδ
  rfl
end LocalizedTransition

private theorem bijective_transfer
    {A : Type a} [Category.{v} A] {B : Type b} [Category.{w} B]
    {D : Type c} [Category.{r} D] {F : A ⥤ B} {G : A ⥤ D}
    {H H' : D ⥤ B} (h : H = H')
    (δ : F ⟶ G ⋙ H) (δ' : F ⟶ G ⋙ H') (hδ : HEq δ δ') (M : A)
    (hM : ∀ P, Function.Bijective (fun f : G.obj M ⟶ P ↦ δ'.app M ≫ H'.map f)) :
    ∀ P, Function.Bijective (fun f : G.obj M ⟶ P ↦ δ.app M ≫ H.map f) := by
  subst H'
  cases hδ
  exact hM

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian in
/-- The universal Hom-bijection criterion for a coefficient sequence makes every
normalized scalar-extension adjunct of its actual transition invertible.
Source: Zheng Construction 4.1; Stacks 0941.
(blueprint: lem-coef-normalized-sequence-semilinear).

Proof: identify scalar restriction using the coefficient tower's composition law.
The unique sectionwise restriction formulas identify the ordinary transitions;
localization preserves their equality. The given Hom-bijections, transported across
this identification and the scalar adjunction, are the coyoneda criterion for each
transition adjunct to be an isomorphism. -/
theorem coefficientNormalizedSequence_semilinear
    (scalar : ∀ {m n : ℕ} (h : n ≤ m),
      SemilinearSections.ScalarData.{t + 1, t, max u (t + 1)}
        (SemilinearSections.coefficientMap (Scheme.ProEt.topology W)
          (integralCoefficientCommRingSheaf l E W)
          (coefficientSequenceCommRingTransition l E W) h))
    (M : coefficientSequenceDerived l E W) (hM : IsNormalizedCoefficientSequence l E W M) :
    SemilinearSections.Normalized (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W)
      (coefficientSequenceCommRingTransition l E W) scalar M := by
  intro m n h
  let J := Scheme.ProEt.topology W
  let B := integralCoefficientCommRingSheaf l E W
  let τ := coefficientSequenceCommRingTransition l E W
  let H := SemilinearSections.res (SemilinearSections.coefficientMap J B τ h)
  let : PreservesFiniteLimits H :=
    (SemilinearSections.res_exact (SemilinearSections.coefficientMap J B τ h)).1
  let : PreservesFiniteColimits H :=
    (SemilinearSections.res_exact (SemilinearSections.coefficientMap J B τ h)).2
  let : PreservesFiniteLimits (normalizedDVRModuleRes l E W h) :=
    (normalizedDVRModuleRes_exact l E W h).1
  let : PreservesFiniteColimits (normalizedDVRModuleRes l E W h) :=
    (normalizedDVRModuleRes_exact l E W h).2
  let : (coefficientSequenceEvaluation l E W m).Additive :=
    coefficientSequenceEvaluation_additive l E W m
  let : (coefficientSequenceEvaluation l E W n).Additive :=
    coefficientSequenceEvaluation_additive l E W n
  have hδ : HEq (SemilinearSections.derivedTransition J B τ h)
      (coefficientSequenceDerivedTransition l E W h) :=
    localizedTransition_heq (coefficientSequenceEvaluation l E W m)
      (coefficientSequenceEvaluation l E W n) H (normalizedDVRModuleRes l E W h)
      (restriction_eq l E W h) _ _ (transition_heq l E W h)
  have hb := bijective_transfer (mapDerived_eq H (normalizedDVRModuleRes l E W h)
    (restriction_eq l E W h)) _ _ hδ M (hM h)
  apply isIso_of_coyoneda_map_bijective
  intro P
  apply Function.Bijective.of_comp_left (f := (scalar h).adjunction.homEquiv _ P)
  · simpa only [Function.comp_def, SemilinearSections.reduction,
      Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply] using hb P
  · exact ((scalar h).adjunction.homEquiv _ P).injective

end WeilConjectures
