/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement

/-! # A normalized basis at one finite coefficient level

Source: Stacks Project, Modules on Sites, Tag 04J0; Bhatt--Scholze,
Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-finite-basis).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe a b r
open CategoryTheory Opposite

namespace WeilConjectures.IntegralFiniteBasisProof
open SheafOfModules
open scoped ChangeOfRings

section ScalarBasis
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [HasWeakSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
  (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))

private noncomputable def tensorPresentation :
    changeOfRingsPresheaf φ M ≅ changeOfRingsPresheafOfUniverses φ M :=
  PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by
    intro V W i
    apply ModuleCat.hom_ext
    ext t
    induction t using TensorProduct.inductionOn with
    | add z z' hz hz' => simp only [_root_.map_add, hz, hz']
    | tmul s x =>
      change changeOfRingsMap φ M i (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) =
        changeOfRingsMapOfUniverses φ M i (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)
      exact (Classical.choose_spec (exists_changeOfRingsMap φ M i) s x).trans
        (changeOfRingsMap_tmulOfUniverses φ M i s x).symm)

private noncomputable def tensorPresentationIso :
    changeOfRings φ M ≅ changeOfRingsOfUniverses φ M :=
  (PresheafOfModules.sheafification (𝟙 _)).mapIso (tensorPresentation φ M)

omit [∀ V, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem tensorPresentation_pure (V : Cᵒᵖ) (s : S.obj.obj V)
    (x : M.val.obj V) :
    (tensorPresentationIso φ M).hom.val.app V
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app V
        (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) =
      scalarExtensionSection φ M V s x := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S).obj)).unit.naturality
      (tensorPresentation φ M).hom
  exact (congrArg (fun f ↦ f.app V
    (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x)) h).symm

private noncomputable def scalarBasis {V : C}
    (e : M.over V ≅ (unit ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)).over V) :
    (changeOfRings φ M).over V ≅ (unit ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj S)).over V :=
  (overFunctor _ V).mapIso (tensorPresentationIso φ M) ≪≫ extendedBasisIso φ M e

private theorem scalarBasis_unit {V : C}
    (e : M.over V ≅ (unit ((sheafCompose J
      (forget₂ CommRingCat RingCat)).obj R)).over V) (T : Over V) :
    (scalarBasis φ M e).hom.val.app (op T)
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app (op T.left)
        ((1 : S.obj.obj (op T.left)) ⊗ₜ[R.obj.obj (op T.left),
          (φ.hom.app (op T.left)).hom] (e.inv.val.app (op T)
            (1 : R.obj.obj (op T.left))))) = (1 : S.obj.obj (op T.left)) := by
  change (extendedBasisIso φ M e).hom.val.app (op T)
    ((tensorPresentationIso φ M).hom.val.app (op T.left) _) =
      (1 : S.obj.obj (op T.left))
  rw [tensorPresentation_pure]
  exact (extendedCoordinateMap_tmul φ M e (op T) 1 _).trans (by
    change φ.hom.app (op T.left) ((localDual M e).app (op T)
      (localBasis M e (op T))) * 1 = 1
    rw [localDual_basis, map_one, one_mul])

end ScalarBasis
end WeilConjectures.IntegralFiniteBasisProof

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped ChangeOfRings
namespace WeilConjectures.IntegralObjectQuotient

private noncomputable instance (priority := 5000) fixedAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private noncomputable instance (priority := 5000) fixedAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) (W : X.ProEt) (L : integralTowerModules.{u, u} l E X)
  (e : L.over W ≅
    (SheafOfModules.unit.{u, u + 1, u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W)

/-- The single complex of the given module. Source: Stacks Tag 04J0
(blueprint: lem-pur-integral-object-finite-basis). -/
abbrev singleModule :=
  (CochainComplex.singleFunctor (integralTowerModules.{u, u} l E X) 0).obj L

/-- The finite pullback before restriction to the completed coefficient ring.
Source: Stacks Tag 04J0 (blueprint: lem-pur-integral-object-finite-basis). -/
noncomputable def finitePullback (n : ℕ) :=
  ((integralOperationsLevelPullback.{u, u} l E W.hom n).mapHomologicalComplex
    (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex.{u, u} l E X n).obj
      (singleModule l E X L))

/-- The finite regular module placed in degree zero. Source: Stacks Tag 04J0
(blueprint: lem-pur-integral-object-finite-basis). -/
abbrev finiteRegular (T : Scheme.{u}) (n : ℕ) :=
  (CochainComplex.singleFunctor (integralOperationsFiniteModules.{u, u} l E T n)
    0).obj (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E T n))

/-- The degree-zero identification for the regular single complex.
Source: Stacks Tag 04J0 (blueprint: lem-pur-integral-object-finite-basis). -/
abbrev finiteZero (T : Scheme.{u}) (n : ℕ) :=
  HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E T n))

/-- The section of L[0] supplied by the inverse integral basis on U over W.
Source: Stacks Tag 04J0 (blueprint: lem-pur-integral-object-finite-basis). -/
def basisSection (U : W.left.ProEt) :
    ((singleModule l E X L).X 0).val.obj
      (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)) :=
  (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).inv.val.app _
    (e.inv.val.app (op ((ProEt.sliceFrom X W).obj U))
      (1 : (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X).obj.obj
        (op ((ProEt.sliceFrom X W).obj U).left)))

/-- The actual inverse-image tensor generator, restricted along the distinguished
unit U → W ×_X U. No inverse-image or tensor comparison is chosen here.
Source: Stacks Tags 04J0 and 00VC (blueprint: lem-pur-integral-object-finite-basis). -/
def basisGenerator (n : ℕ) (U : W.left.ProEt) :
    ((finitePullback l E X W L n).X 0).val.obj (op U) :=
  ((finitePullback l E X W L n).X 0).val.presheaf.map
    (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit.app
      U).op)
    (integralOperationsPullbackGenerator.{u, u} l E W.hom n
      (((unrestrictedIntegralFiniteComplex.{u, u} l E X n).obj
        (singleModule l E X L)).X 0)
      ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)
      (unrestrictedIntegralTensorSection.{u, u} l E X n
        ((singleModule l E X L).X 0) _ 1 (basisSection l E X W L e U)))

private noncomputable def objectRingIso (n : ℕ) :=
  AlgebraicGeometry.Scheme.restrictionConstantIso W
    (Padic.coefficientExtensionRing l E (n + 1))

private instance objectMap_continuous :
    (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) :=
  ProEt.isContinuous_overMap W.prop

private noncomputable def objectRingMap (n : ℕ) :
    integralCoefficientSheaf l E W.left n ⟶
      ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).sheafPushforwardContinuous
        RingCat.{u + 1} (ProEt.topology W.left) (ProEt.topology X)).obj
          (integralCoefficientSheaf l E X n) :=
  ⟨Functor.whiskerRight (objectRingIso l E X W n).hom.hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private noncomputable def objectRestriction (n : ℕ) :
    integralOperationsFiniteModules.{u, u} l E X n ⥤
      integralOperationsFiniteModules.{u, u} l E W.left n := by
  letI : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) := ProEt.isContinuous_overMap W.prop
  exact SheafOfModules.pushforward.{u + 1}
    (F := MorphismProperty.Over.map (f := W.hom) ⊤ W.prop)
    (J := ProEt.topology W.left) (K := ProEt.topology X) (objectRingMap l E X W n)

private noncomputable def objectAdjunction (n : ℕ) :
    objectRestriction l E X W n ⊣
      coefficientProEtaleModuleDirectImage.{u, u} W.hom
        (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  letI : (MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).IsContinuous
      (ProEt.topology W.left) (ProEt.topology X) := ProEt.isContinuous_overMap W.prop
  letI : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ W.hom).IsContinuous
      (ProEt.topology X) (ProEt.topology W.left) := ProEt.isContinuous_overPullback W.hom
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let e := objectRingIso l E X W n
  let ψ : integralCoefficientSheaf l E X n ⟶
      ((proEtaleBaseChange W.hom).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology X) (ProEt.topology W.left)).obj
          (integralCoefficientSheaf l E W.left n) :=
    ⟨Functor.whiskerRight (coefficientProEtaleDirectRingMap.{u, u} W.hom
      (CommRingCat.of (ULift.{u + 1} A))).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  have H₁ := coefficient_restriction_counit W A e (restrictionConstantIso_unit W A)
  have H₂ := coefficient_restriction_unit W A e (restrictionConstantIso_unit W A)
  exact SheafOfModules.pushforwardPushforwardAdj
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial)
    (objectRingMap l E X W n) ψ
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₁)
    (congrArg (fun t ↦ Functor.whiskerRight t
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) H₂)

private noncomputable def objectPullbackIso (n : ℕ) :
    integralOperationsLevelPullback l E W.hom n ≅ objectRestriction l E X W n :=
  ((objectAdjunction l E X W n).leftAdjointUniq
    (coefficientProEtaleModuleAdjunction.{u, u} W.hom
      (CommRingCat.of
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))))).symm

-- The mate formula retains the distinguished site-adjunction unit.
private theorem objectPullbackIso_inv (n : ℕ)
    (M : integralOperationsFiniteModules.{u, u} l E X n)
    (U : W.left.ProEt)
    (x : M.val.obj (op ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U))) :
    ((objectPullbackIso l E X W n).inv.app M).val.app (op U) x =
      ((integralOperationsLevelPullback l E W.hom n).obj M).val.presheaf.map
        (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop trivial).unit.app
          U).op) (integralOperationsPullbackGenerator l E W.hom n M _ x) := by
  let a := objectAdjunction l E X W n
  let b := coefficientProEtaleModuleAdjunction.{u, u} W.hom
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have h : (objectPullbackIso l E X W n).inv.app M =
      (a.homEquiv _ _).symm (b.unit.app M) := by
    apply (a.homEquiv _ _).injective
    exact (Adjunction.homEquiv_leftAdjointUniq_hom_app a b M).trans
      ((a.homEquiv _ _).apply_symm_apply _).symm
  rw [h, Adjunction.homEquiv_counit]
  rfl

private instance sliceFrom_continuous :
    (ProEt.sliceFrom X W).IsContinuous (ProEt.topology W.left)
      ((ProEt.topology X).over W) := by
  have : (ProEt.sliceFrom X W).IsDenseSubsite (ProEt.topology W.left)
      ((ProEt.topology X).over W) := ProEt.sliceDense X W
  infer_instance

private noncomputable def sliceRingMap (n : ℕ) :
    integralCoefficientSheaf l E W.left n ⟶
      ((ProEt.sliceFrom X W).sheafPushforwardContinuous RingCat.{u + 1}
        (ProEt.topology W.left) ((ProEt.topology X).over W)).obj
          ((integralCoefficientSheaf l E X n).over W) :=
  ⟨Functor.whiskerRight (objectRingIso l E X W n).hom.hom
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩

private noncomputable def sliceRestriction (n : ℕ) :
    SheafOfModules.{u + 1} ((integralCoefficientSheaf l E X n).over W) ⥤
      integralOperationsFiniteModules.{u, u} l E W.left n :=
  SheafOfModules.pushforward.{u + 1} (F := ProEt.sliceFrom X W)
    (J := ProEt.topology W.left) (K := (ProEt.topology X).over W) (sliceRingMap l E X W n)

private theorem sliceUnit_isIso (n : ℕ) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit (sliceRingMap l E X W n)) := by
  rw [← isIso_iff_of_reflects_iso _
    (SheafOfModules.toSheaf (integralCoefficientSheaf l E W.left n))]
  change IsIso ((sheafCompose (ProEt.topology W.left)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).map
      ((sheafCompose (ProEt.topology W.left)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (objectRingIso l E X W n).hom))
  infer_instance

private noncomputable def restrictionBasis (n : ℕ)
    (M : integralOperationsFiniteModules.{u, u} l E X n)
    (q : M.over W ≅ (SheafOfModules.unit (integralCoefficientSheaf l E X n)).over W) :
    (objectRestriction l E X W n).obj M ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W.left n) := by
  letI := sliceUnit_isIso l E X W n
  exact (sliceRestriction l E X W n).mapIso q ≪≫
    (asIso (SheafOfModules.unitToPushforwardObjUnit (sliceRingMap l E X W n))).symm

private theorem restrictionBasis_inv_one (n : ℕ)
    (M : integralOperationsFiniteModules.{u, u} l E X n)
    (q : M.over W ≅ (SheafOfModules.unit (integralCoefficientSheaf l E X n)).over W)
    (U : W.left.ProEt) :
    (restrictionBasis l E X W n M q).inv.val.app (op U)
      (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U)) =
      q.inv.val.app (op ((ProEt.sliceFrom X W).obj U))
        (1 : (integralCoefficientSheaf l E X n).obj.obj
          (op ((ProEt.sliceFrom X W).obj U).left)) := by
  change q.inv.val.app (op ((ProEt.sliceFrom X W).obj U))
    ((objectRingIso l E X W n).hom.hom.app (op U)
      (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U))) = _
  rw [map_one]

private noncomputable def degreeBasis :
    ((singleModule l E X L).X 0).over W ≅
      (SheafOfModules.unit
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W :=
  (SheafOfModules.overFunctor _ W).mapIso
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L) ≪≫ e

private noncomputable def degreeReductionBasis (n : ℕ) :
    (((unrestrictedIntegralFiniteComplex l E X n).obj
      (singleModule l E X L)).X 0).over W ≅
      (SheafOfModules.unit (integralCoefficientSheaf l E X n)).over W :=
  (SheafOfModules.overFunctor _ W).mapIso
      (eqToIso ((unrestrictedIntegralReductionExistence l E X n).choose_spec.choose
        ((singleModule l E X L).X 0))) ≪≫
    IntegralFiniteBasisProof.scalarBasis (completedIntegralCommRingProjectionUnrestricted l E X n)
      ((singleModule l E X L).X 0) (degreeBasis l E X W L e)

private theorem degreeReductionBasis_unit (n : ℕ) (U : W.left.ProEt) :
    (degreeReductionBasis l E X W L e n).hom.val.app
      (op ((ProEt.sliceFrom X W).obj U))
      (unrestrictedIntegralTensorSection l E X n ((singleModule l E X L).X 0)
        _ 1 (basisSection l E X W L e U)) =
      (1 : (integralCoefficientSheaf l E X n).obj.obj
        (op ((ProEt.sliceFrom X W).obj U).left)) := by
  let M := (singleModule l E X L).X 0
  let φ := completedIntegralCommRingProjectionUnrestricted l E X n
  let T := (ProEt.sliceFrom X W).obj U
  let V := op T.left
  let h := (unrestrictedIntegralReductionExistence l E X n).choose_spec.choose M
  let t := (toSheafify (ProEt.topology X)
    (SheafOfModules.changeOfRingsPresheaf φ M).presheaf).app V
      ((1 : (integralCoefficientSheaf l E X n).obj.obj V) ⊗ₜ[
        (completedIntegralCommRingSheafUnrestricted l E X).obj.obj V,
        (φ.hom.app V).hom] (basisSection l E X W L e U))
  have hc : (eqToHom h).val.app V ((eqToHom h.symm).val.app V t) = t := by
    have hh := congrArg (fun f ↦ f.val.app V t) (eqToHom_trans h.symm h)
    simp only [eqToHom_refl] at hh
    exact hh
  change (IntegralFiniteBasisProof.scalarBasis φ M (degreeBasis l E X W L e)).hom.val.app
    (op T) ((eqToHom h).val.app V ((eqToHom h.symm).val.app V t)) = _
  rw [hc]
  exact IntegralFiniteBasisProof.scalarBasis_unit φ M (degreeBasis l E X W L e) T

private theorem degreeReductionBasis_inv_one (n : ℕ) (U : W.left.ProEt) :
    (degreeReductionBasis l E X W L e n).inv.val.app
      (op ((ProEt.sliceFrom X W).obj U))
        (1 : (integralCoefficientSheaf l E X n).obj.obj
          (op ((ProEt.sliceFrom X W).obj U).left)) =
      unrestrictedIntegralTensorSection l E X n ((singleModule l E X L).X 0)
        _ 1 (basisSection l E X W L e U) := by
  let q := degreeReductionBasis l E X W L e n
  let T := op ((ProEt.sliceFrom X W).obj U)
  have h := congrArg (fun x ↦ q.inv.val.app T x)
    (degreeReductionBasis_unit l E X W L e n U)
  have hc := congrArg (fun f ↦ f.val.app T
    (unrestrictedIntegralTensorSection l E X n ((singleModule l E X L).X 0)
      _ 1 (basisSection l E X W L e U))) q.hom_inv_id
  exact h.symm.trans hc

private noncomputable def degreePullbackBasis (n : ℕ) :
    (finitePullback l E X W L n).X 0 ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W.left n) :=
  (objectPullbackIso l E X W n).app _ ≪≫
    restrictionBasis l E X W n _ (degreeReductionBasis l E X W L e n)

private theorem degreePullbackBasis_inv_one (n : ℕ) (U : W.left.ProEt) :
    (degreePullbackBasis l E X W L e n).inv.val.app (op U)
      (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U)) =
        basisGenerator l E X W L e n U := by
  change ((objectPullbackIso l E X W n).inv.app _).val.app (op U)
    ((restrictionBasis l E X W n _ (degreeReductionBasis l E X W L e n)).inv.val.app
      (op U) (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U))) = _
  rw [restrictionBasis_inv_one, degreeReductionBasis_inv_one, objectPullbackIso_inv]
  rfl

private noncomputable def complexBasis (n : ℕ) :
    finitePullback l E X W L n ≅ finiteRegular l E W.left n :=
  ((integralOperationsLevelPullback l E W.hom n).mapHomologicalComplex (.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (unrestrictedIntegralReductionFunctor l E X n) (.up ℤ) 0).app L) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex
      (integralOperationsLevelPullback l E W.hom n) (.up ℤ) 0).app _ ≪≫
    (CochainComplex.singleFunctor (integralOperationsFiniteModules l E W.left n) 0).mapIso
      (((integralOperationsLevelPullback l E W.hom n).mapIso
        ((unrestrictedIntegralReductionFunctor l E X n).mapIso
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L))).symm ≪≫
        degreePullbackBasis l E X W L e n)

private theorem complexBasis_zero (n : ℕ) :
    (complexBasis l E X W L e n).hom.f 0 ≫ (finiteZero l E W.left n).hom =
      (degreePullbackBasis l E X W L e n).hom := by
  simp only [complexBasis, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    HomologicalComplex.comp_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    CochainComplex.singleFunctor]
  rw [HomologicalComplex.single_map_f_self]
  simp only [Category.assoc, finiteZero, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  simp only [Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Iso.symm_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  rw [← (unrestrictedIntegralReductionFunctor l E X n).map_comp, Iso.hom_inv_id]
  rw [(unrestrictedIntegralReductionFunctor l E X n).map_id]
  change (integralOperationsLevelPullback l E W.hom n).map
      (𝟙 ((unrestrictedIntegralReductionFunctor l E X n).obj
        ((singleModule l E X L).X 0))) ≫ _ = _
  rw [(integralOperationsLevelPullback l E W.hom n).map_id _, Category.id_comp]

/-- A slice basis induces a normalized basis at one finite coefficient level.
This asserts no compatibility between distinct coefficient levels.

Source: Stacks Project, Modules on Sites, Tag 04J0, localization of a morphism
of ringed sites; Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-finite-basis).

Proof: let R be the completed coefficient sheaf and A its quotient of exponent
n+1. Scalar extension along R → A commutes with localization: identify the
right adjoints (restriction of scalars followed by the slice pushforward) and
use uniqueness of left adjoints. Apply the given slice basis and the regular
multiplication isomorphism A tensor_R R → A. The pro-etale object
inverse-image/restriction comparison and the equivalence between the slice at
W and the site of W.left transport this to a finite module isomorphism.
Apply the single-complex comparison to obtain c. The inverse multiplication
sends z to z tensor 1. The localization unit is restriction along the
projection, and the inverse-image comparison is the coprojection indexed by
U → W ×_X U. Thus the transported inverse at U sends z to z times the
displayed basisGenerator. This proves the formula without any choice of a
basis at another exponent. All operations preserve zero objects, so the same
construction works on the empty scheme and for the zero coefficient ring. -/
theorem finiteNormalizedBasis (n : ℕ) :
    ∃ c : finitePullback l E X W L n ≅ finiteRegular l E W.left n,
      ∀ (U : W.left.ProEt)
        (z : (integralCoefficientSheaf.{u, u} l E W.left n).obj.obj (op U)),
        (((finiteZero l E W.left n).inv ≫ c.inv.f 0).val.app (op U)) z =
          z • basisGenerator l E X W L e n U := by
  let c := complexBasis l E X W L e n
  refine ⟨c, ?_⟩
  let d := (HomologicalComplex.eval
    (integralOperationsFiniteModules l E W.left n) (.up ℤ) 0).mapIso c ≪≫
      finiteZero l E W.left n
  have hc : (finiteZero l E W.left n).inv ≫ c.inv.f 0 =
      (degreePullbackBasis l E X W L e n).inv :=
    (Iso.inv_eq_inv d (degreePullbackBasis l E X W L e n)).mpr
      (complexBasis_zero l E X W L e n)
  intro U z
  let f := ((degreePullbackBasis l E X W L e n).inv.val.app (op U)).hom
  have hs : f z = z • f (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U)) :=
    (congrArg f (mul_one z).symm).trans
      (f.map_smul z (1 : (integralCoefficientSheaf l E W.left n).obj.obj (op U)))
  exact (congrArg (fun g ↦ g.val.app (op U) z) hc).trans
    (hs.trans (congrArg (fun t ↦ z • t) (degreePullbackBasis_inv_one l E X W L e n U)))

end WeilConjectures.IntegralObjectQuotient
