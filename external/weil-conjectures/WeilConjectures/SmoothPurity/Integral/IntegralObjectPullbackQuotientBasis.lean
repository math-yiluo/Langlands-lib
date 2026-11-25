/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Integral.IntegralScalarExtensionWellDefined
import WeilConjectures.SmoothPurity.IntegralObjectQuotient.IntegralObjectFiniteBasis
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.SmoothPurity.ConstantScalarStrictUnit.ConstantScalarStrictUnit

/-! # Compatible quotient bases after inverse image along a site object

Source: Stacks Project, Modules on Sites, localization at an object (Tag 04J0);
Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-pullback-quotient-basis).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 512
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
  WeilConjectures.integralOperationsAbSheafify WeilConjectures.integralOperationsSiteSmall
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures

attribute [local irreducible] constantSheaf CategoryTheory.Limits.limit
  HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence unrestrictedIntegralReductionFunctor
  completedIntegralCoefficientSheafUnrestricted
  completedIntegralCommRingProjectionUnrestricted
  AlgebraicGeometry.Scheme.coefficientProEtaleModuleAdjunction
  AlgebraicGeometry.Scheme.coefficientProEtaleModulePullback Functor.leftAdjoint
  IntegralObjectQuotient.basisSection
  integralScalarTransition integralScalarReduction integralScalarReductionConcrete
  integralScalarReductionWitness

private noncomputable instance (priority := 5000) fixedAbSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} T

private noncomputable instance (priority := 5000) fixedAbLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} T

/-- The fixed site-size witness used by the exported quotient-basis statement.
Source: Stacks Tag 04J0 (blueprint: lem-pur-integral-object-pullback-quotient-basis). -/
theorem integralObjectPullbackSiteSmall (T : Scheme.{u}) :
    EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0} _

attribute [local instance 5000] integralObjectPullbackSiteSmall

namespace IntegralObjectQuotientProof

open IntegralObjectQuotient

section RestrictionLemmas
universe a b r
variable {C : Type a} [Category.{b} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{r}} (q : R ⟶ S)
  {M : SheafOfModules.{r} R} {N : SheafOfModules.{r} S}
  (f : M ⟶ (SheafOfModules.restrictScalars q).obj N)

private def forgetModuleMap : M.val.presheaf ⟶ N.val.presheaf :=
  (PresheafOfModules.toPresheaf R.obj).map f.val

private theorem forgetModuleMap_apply (U : Cᵒᵖ) (x : M.val.obj U) :
    (forgetModuleMap q f).app U x = f.val.app U x := rfl

private theorem forgetModuleMap_smul (U : Cᵒᵖ) (s : R.obj.obj U) (x : M.val.obj U) :
    (forgetModuleMap q f).app U (s • x) =
      q.hom.app U s • (forgetModuleMap q f).app U x :=
  (f.val.app U).hom.map_smul s x

private theorem ab_map_eq_of_sections {F G : Cᵒᵖ ⥤ AddCommGrpCat.{r}} (g : F ⟶ G)
    {U V : Cᵒᵖ} (k : U ⟶ V) (x : F.obj U) (y : G.obj U)
    (bx : F.obj V) (by' : G.obj V) (hx : bx = F.map k x) (hy : by' = G.map k y)
    (h : g.app U x = y) : g.app V bx = by' :=
  (congrArg (fun z ↦ g.app V z) hx).trans
    ((ConcreteCategory.congr_hom (g.naturality k) x).trans
      ((congrArg (fun z ↦ G.map k z) h).trans hy.symm))

private theorem ringMap_one_congr {A B : RingCat.{r}} (g : A ⟶ B)
    {D : Type a} (h : B → D) : h (g 1) = h 1 :=
  congrArg h (map_one g.hom)

end RestrictionLemmas

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem pullbackTransition_eq {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ) :
    integralOperationsPullbackTransition.{u, u} l E f n =
      integralPullbackTransitionCandidate.{u, u} l E f n := by
  apply (integralOperationsPullbackTransition_existsUnique.{u, u} l E f n).unique
    (integralOperationsPullbackTransition_existsUnique.{u, u} l E f n).exists.choose_spec
  intro P i V x
  exact SheafOfModules.IntegralPullbackProof.mateData_unit_formula
    (integralOperationsBaseChange f)
    (integralCoefficientSheafTransition l E S n) (integralCoefficientSheafTransition l E T n)
    (integralDirectRingMap l E f (n + 1)) (integralDirectRingMap l E f n)
    (integralDirectRingMap_square l E f n)
    (integralPullbackAdj l E f (n + 1)) (integralPullbackAdj l E f n)
    (((integralFiniteTransition l E T n).app P).f i) (op V) x

attribute [local irreducible] unrestrictedIntegralTensorSection integralOperationsPullbackGenerator

private theorem pullbackTransition_generator {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (V : T.ProEt)
    (x : (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i).val.obj
      (op V)) :
    ((((integralOperationsPullbackTransition.{u, u} l E f n).app P).f i).val.app
      (op ((proEtaleBaseChange f).obj V)))
        (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
          (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V x) =
      integralOperationsPullbackGenerator.{u, u} l E f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i) V
        (((((unrestrictedIntegralTransition.{u, u} l E T n).app P).f i).val.app
          (op V)) x) :=
  (integralOperationsPullbackTransition_existsUnique.{u, u}
    l E f n).exists.choose_spec P i V x

attribute [local irreducible] integralPullbackFiniteComplexMap
  integralOperationsPullbackTransition SheafOfModules.IntegralScalarProof.restrictComplexMap

private theorem pullbackTransition_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : ((((integralOperationsLevelPullback.{u, u} l E f (n + 1)).mapHomologicalComplex
      (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P)).X
        i).val.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E f n).app P).f i).val.app
      (op U)) x =
      (((integralPullbackFiniteComplexMap.{u, u} l E f n P).f i).val.app (op U)) x := by
  have h := congrArg (fun (t : integralOperationsPullbackLevel.{u, u} l E f (n + 1) ⟶
      integralOperationsPullbackLevel.{u, u} l E f n) ↦
        (((t.app P).f i).val.app (op U)) x) (pullbackTransition_eq l E f n)
  exact h.trans (SheafOfModules.IntegralScalarProof.restrictComplexMap_apply
    (integralCompletedProjection l E S (n + 1)) (integralCompletedProjection l E S n)
    (integralCoefficientSheafTransition l E S n) (integralProjection_step l E S n)
    (integralPullbackFiniteComplexMap l E f n P) i (op U) x)

private theorem reduction_one (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (V : T.ProEt)
    (x : (P.X i).val.obj (op V)) :
    ((((unrestrictedIntegralTransition.{u, u} l E T n).app P).f i).val.app (op V))
      (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x) =
      unrestrictedIntegralTensorSection.{u, u} l E T n (P.X i) (op V) 1 x := by
  exact ((unrestrictedIntegralTransition_existsUnique.{u, u} l E T n).exists.choose_spec
    P i (op V) 1 x).trans
      (ringMap_one_congr ((integralCoefficientSheafTransition l E T n).hom.app (op V))
        (fun (z : (integralCoefficientSheaf.{u, u} l E T n).obj.obj (op V)) ↦
          unrestrictedIntegralTensorSection.{u, u} l E T n (P.X i) (op V) z x))

private theorem finite_generator_step {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (V : T.ProEt)
    (x : (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i).val.obj
      (op V)) :
    (((integralPullbackFiniteComplexMap.{u, u} l E f n P).f i).val.app
      (op ((proEtaleBaseChange f).obj V)))
        (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
          (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V x) =
      integralOperationsPullbackGenerator.{u, u} l E f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i) V
        (((((unrestrictedIntegralTransition.{u, u} l E T n).app P).f i).val.app
          (op V)) x) :=
  (pullbackTransition_apply l E f n P i ((proEtaleBaseChange f).obj V)
    (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
      (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V x)).symm.trans
        (pullbackTransition_generator l E f n P i V x)

private abbrev pulledDegree {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) :
    integralOperationsFiniteModules.{u, u} l E S n :=
  ((((integralOperationsLevelPullback.{u, u} l E f n).mapHomologicalComplex
    (.up ℤ)).obj ((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P)).X i)

private def nativeFiniteMap {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) :
    pulledDegree l E f (n + 1) P i ⟶
      (SheafOfModules.restrictScalars (integralCoefficientSheafTransition l E S n)).obj
        (pulledDegree l E f n P i) :=
  (integralPullbackFiniteComplexMap.{u, u} l E f n P).f i

private theorem nativeFiniteMap_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U)) :
    ((nativeFiniteMap l E f n P i).val.app (op U)) x =
      (((integralPullbackFiniteComplexMap.{u, u} l E f n P).f i).val.app (op U)) x := rfl

attribute [local irreducible] nativeFiniteMap

private theorem actual_native_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E f n).app P).f i).val.app
      (op U)) x = ((nativeFiniteMap l E f n P i).val.app (op U)) x :=
  (pullbackTransition_apply l E f n P i U x).trans
    (nativeFiniteMap_apply l E f n P i U x).symm

private def finiteAbMap {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) :
    (pulledDegree l E f (n + 1) P i).val.presheaf ⟶
      (pulledDegree l E f n P i).val.presheaf :=
  forgetModuleMap (integralCoefficientSheafTransition l E S n)
    (nativeFiniteMap l E f n P i)

private theorem finiteAbMap_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U)) :
    (finiteAbMap l E f n P i).app (op U) x =
      ((nativeFiniteMap l E f n P i).val.app (op U)) x :=
  forgetModuleMap_apply (integralCoefficientSheafTransition l E S n)
    (nativeFiniteMap l E f n P i) (op U) x

private theorem finiteAbMap_smul {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U))
    (z : (integralCoefficientSheaf.{u, u} l E S (n + 1)).obj.obj (op U)) :
    (finiteAbMap l E f n P i).app (op U) (z • x) =
      (integralCoefficientSheafTransition.{u, u} l E S n).hom.app (op U) z •
        (finiteAbMap l E f n P i).app (op U) x :=
  forgetModuleMap_smul (integralCoefficientSheafTransition l E S n)
    (nativeFiniteMap l E f n P i) (op U) z x

attribute [local irreducible] finiteAbMap forgetModuleMap

private theorem actual_ab_apply {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E f n).app P).f i).val.app
      (op U)) x = (finiteAbMap l E f n P i).app (op U) x :=
  (actual_native_apply l E f n P i U x).trans (finiteAbMap_apply l E f n P i U x).symm

private theorem finite_generator_one_step {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (V : T.ProEt)
    (x : (P.X i).val.obj (op V)) :
    ((nativeFiniteMap l E f n P i).val.app
      (op ((proEtaleBaseChange f).obj V)))
        (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
          (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V
          (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x)) =
      integralOperationsPullbackGenerator.{u, u} l E f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection.{u, u} l E T n (P.X i) (op V) 1 x) :=
  (nativeFiniteMap_apply l E f n P i ((proEtaleBaseChange f).obj V)
    (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
      (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V
      (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x))).trans
    ((finite_generator_step l E f n P i V
      (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x)).trans
      (congrArg
        (fun (y : (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i).val.obj
            (op V)) ↦
          integralOperationsPullbackGenerator.{u, u} l E f n
            (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i) V y)
        (reduction_one l E T n P i V x)))

private theorem finite_generator_restrict_step {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ)
    (U : S.ProEt) (V : T.ProEt) (k : op ((proEtaleBaseChange f).obj V) ⟶ op U)
    (x : (P.X i).val.obj (op V))
    (bx : (pulledDegree l E f (n + 1) P i).val.obj (op U))
    (by' : (pulledDegree l E f n P i).val.obj (op U))
    (hx : bx = (pulledDegree l E f (n + 1) P i).val.presheaf.map k
      (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V
        (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x)))
    (hy : by' = (pulledDegree l E f n P i).val.presheaf.map k
      (integralOperationsPullbackGenerator.{u, u} l E f n
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T n).obj P).X i) V
        (unrestrictedIntegralTensorSection.{u, u} l E T n (P.X i) (op V) 1 x))) :
    (finiteAbMap l E f n P i).app (op U) bx = by' :=
  ab_map_eq_of_sections (finiteAbMap l E f n P i) k _ _ bx by' hx hy
    ((finiteAbMap_apply l E f n P i ((proEtaleBaseChange f).obj V)
      (integralOperationsPullbackGenerator.{u, u} l E f (n + 1)
        (((unrestrictedIntegralFiniteComplex.{u, u} l E T (n + 1)).obj P).X i) V
        (unrestrictedIntegralTensorSection.{u, u} l E T (n + 1) (P.X i) (op V) 1 x))).trans
      (finite_generator_one_step l E f n P i V x))

private theorem pullback_smul_eq {S T : Scheme.{u}} (f : S ⟶ T) (n : ℕ)
    (P : CochainComplex (integralTowerModules.{u, u} l E T) ℤ) (i : ℤ) (U : S.ProEt)
    (x : (pulledDegree l E f (n + 1) P i).val.obj (op U))
    (y : (pulledDegree l E f n P i).val.obj (op U))
    (h : (finiteAbMap l E f n P i).app (op U) x = y)
    (z : (integralCoefficientSheaf.{u, u} l E S (n + 1)).obj.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E f n).app P).f i).val.app
      (op U)) (z • x) =
        (integralCoefficientSheafTransition.{u, u} l E S n).hom.app (op U) z • y :=
  (actual_ab_apply l E f n P i U (z • x)).trans
    ((finiteAbMap_smul l E f n P i U x z).trans
      (congrArg (fun (v : (pulledDegree l E f n P i).val.obj (op U)) ↦
        (integralCoefficientSheafTransition.{u, u} l E S n).hom.app (op U) z • v) h))

variable (X : Scheme.{u}) (W : X.ProEt) (L : integralTowerModules.{u, u} l E X)
  (e : L.over W ≅
    (SheafOfModules.unit.{u, u + 1, u + 1}
      (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W)

private theorem basisGenerator_eq (n : ℕ) (U : W.left.ProEt) :
    basisGenerator l E X W L e n U =
      ((finitePullback l E X W L n).X 0).val.presheaf.map
        (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop
          trivial).unit.app U).op)
        (integralOperationsPullbackGenerator.{u, u} l E W.hom n
          (((unrestrictedIntegralFiniteComplex.{u, u} l E X n).obj
            (singleModule l E X L)).X 0)
          ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)
          (unrestrictedIntegralTensorSection.{u, u} l E X n
            ((singleModule l E X L).X 0) _ 1 (basisSection l E X W L e U))) := rfl

attribute [local irreducible] IntegralObjectQuotient.basisGenerator

private theorem basisGenerator_step (n : ℕ) (U : W.left.ProEt) :
    (finiteAbMap l E W.hom n (singleModule l E X L) 0).app (op U)
        (basisGenerator l E X W L e (n + 1) U) =
      basisGenerator l E X W L e n U := by
  exact finite_generator_restrict_step l E W.hom n (singleModule l E X L) 0 U
    ((MorphismProperty.Over.map (f := W.hom) ⊤ W.prop).obj U)
    (((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ W.hom W.prop
      trivial).unit.app U).op)
    (basisSection l E X W L e U) _ _
    (basisGenerator_eq l E X W L e (n + 1) U) (basisGenerator_eq l E X W L e n U)

private theorem basisGenerator_smul_step (n : ℕ) (U : W.left.ProEt)
    (z : (integralCoefficientSheaf.{u, u} l E W.left (n + 1)).obj.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E W.hom n).app
      (singleModule l E X L)).f 0).val.app (op U))
        (z • basisGenerator l E X W L e (n + 1) U) =
      (integralCoefficientSheafTransition.{u, u} l E W.left n).hom.app (op U) z •
        basisGenerator l E X W L e n U := by
  exact pullback_smul_eq l E W.hom n (singleModule l E X L) 0 U
    (basisGenerator l E X W L e (n + 1) U) (basisGenerator l E X W L e n U)
    (basisGenerator_step l E X W L e n U) z

private theorem normalizedBasis_step
    (c : ∀ n, finitePullback l E X W L n ≅ finiteRegular l E W.left n)
    (hc : ∀ (n : ℕ) (U : W.left.ProEt)
      (z : (integralCoefficientSheaf.{u, u} l E W.left n).obj.obj (op U)),
      (((finiteZero l E W.left n).inv ≫ (c n).inv.f 0).val.app (op U)) z =
        z • basisGenerator l E X W L e n U)
    (n : ℕ) (U : W.left.ProEt)
    (z : (integralCoefficientSheaf.{u, u} l E W.left (n + 1)).obj.obj (op U)) :
    ((((integralOperationsPullbackTransition.{u, u} l E W.hom n).app
      (singleModule l E X L)).f 0).val.app (op U))
        ((((finiteZero l E W.left (n + 1)).inv ≫ (c (n + 1)).inv.f 0).val.app (op U)) z) =
      (((finiteZero l E W.left n).inv ≫ (c n).inv.f 0).val.app (op U))
        ((integralCoefficientSheafTransition.{u, u} l E W.left n).hom.app (op U) z) := by
  exact (congrArg (fun y ↦
    ((((integralOperationsPullbackTransition.{u, u} l E W.hom n).app
      (singleModule l E X L)).f 0).val.app (op U)) y) (hc (n + 1) U z)).trans
    ((basisGenerator_smul_step l E X W L e n U z).trans
      (hc n U ((integralCoefficientSheafTransition.{u, u} l E W.left n).hom.app
        (op U) z)).symm)

end IntegralObjectQuotientProof

/-- A slice basis gives compatible bases of all finite quotient inverse images.

Source: Stacks Project, Modules on Sites, localization at an object (Tag 04J0);
Bhatt--Scholze, Definition 3.4.10 and Lemma 6.5.9.
(blueprint: lem-pur-integral-object-pullback-quotient-basis).

Proof: write R for the completed coefficient sheaf and A_n for its positive
quotient at exponent n+1. Restrict the scalar-extension adjunction along the
slice projection. Its right adjoint is restriction of scalars, so uniqueness
of left adjoints identifies (A_n tensor_R L)|_W with
(A_n|_W) tensor_(R|_W) (L|_W). Apply the supplied basis to the second factor;
multiplication identifies the result with A_n|_W. The object-inverse-image
restriction comparison transports this to the regular A_n-module on W.left.
For the identity coefficient extension the finite scalar multiplication
isomorphism identifies the reduced regular R-module with this same regular
A_n-module. Compose with its inverse, restrict scalars along R -> A_n, and
apply the single-complex comparison to obtain b_n. For each successor square,
both composites on a local tensor generator a tensor x give reduction of a
times the reduction of the coefficient of x in the supplied basis. The
constant-ring comparison is normalized on constant sections, hence commutes
with these reductions. Tensor generation and the sheafification universal
property give equality of the module maps, and therefore the asserted chain
map equation. This argument needs no flatness of L or coefficient projection;
it also applies to the empty scheme and the zero coefficient sheaf. -/
theorem integralObjectPullbackQuotientBasis (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (W : X.ProEt) (L : integralTowerModules.{u, u} l E X)
    (e : L.over W ≅
      (SheafOfModules.unit.{u, u + 1, u + 1}
        (completedIntegralCoefficientSheafUnrestricted.{u, u} l E X)).over W) :
    ∃ b : ∀ n : ℕ,
      (integralOperationsPullbackLevel.{u, u} l E W.hom n).obj
          ((CochainComplex.singleFunctor (integralTowerModules.{u, u} l E X) 0).obj L) ≅
        (integralScalarLevel.{u, u} l E E (AlgHom.id _ _) W.left n).obj
          ((CochainComplex.singleFunctor
              (integralTowerModules.{u, u} l E W.left) 0).obj
            (SheafOfModules.unit.{u, u + 1, u + 1}
              (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W.left))),
      ∀ n : ℕ,
        (integralOperationsPullbackTransition.{u, u} l E W.hom n).app
            ((CochainComplex.singleFunctor
              (integralTowerModules.{u, u} l E X) 0).obj L) ≫ (b n).hom =
          (b (n + 1)).hom ≫
            (integralScalarTransition.{u, u} l E E (AlgHom.id _ _) W.left n).app
              ((CochainComplex.singleFunctor
                  (integralTowerModules.{u, u} l E W.left) 0).obj
                (SheafOfModules.unit.{u, u + 1, u + 1}
                  (completedIntegralCoefficientSheafUnrestricted.{u, u} l E W.left))) := by
  classical
  choose c hc using (fun n ↦ IntegralObjectQuotient.finiteNormalizedBasis l E X W L e n)
  obtain ⟨s, _, _, hs⟩ :=
    ConstantScalarStrictUnit.regular_scalar_strict_unit_finite_multiplication
      l E W.left E (AlgHom.id _ _)
  let p := fun n ↦ (integralOperationsRestrict.{u, u} l E W.left n).mapIso (c n)
  let q := fun n ↦ (integralOperationsRestrict.{u, u} l E W.left n).mapIso (s n)
  refine ⟨fun n ↦ p n ≪≫ (q n).symm, ?_⟩
  intro n
  apply (cancel_epi (p (n + 1)).inv).mp
  apply (cancel_mono (q n).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i = 0
  · subst i
    apply (cancel_epi ((SheafOfModules.restrictScalars
      (integralOperationsProjection.{u, u} l E W.left (n + 1))).map
        (IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv)).mp
    apply (cancel_mono ((SheafOfModules.restrictScalars
      (integralOperationsProjection.{u, u} l E W.left n)).map
        (IntegralObjectQuotient.finiteZero l E W.left n).hom)).mp
    ext U z
    have ht := IntegralObjectQuotientProof.normalizedBasis_step l E X W L e c hc
      n U.unop z
    have hs' := hs n U.unop
      (((s (n + 1)).inv.f 0).val.app U
        ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z))
    have hsi := congrArg (fun f ↦ (f.f 0).val.app U
      ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z))
      (s (n + 1)).inv_hom_id
    change ((s (n + 1)).hom.f 0).val.app U
      (((s (n + 1)).inv.f 0).val.app U
        ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z)) =
      (IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z at hsi
    have hz : (((s (n + 1)).hom.f 0 ≫
        (ConstantScalarStrictUnit.finiteZeroIso l E W.left (n + 1)).hom).val.app U)
      (((s (n + 1)).inv.f 0).val.app U
        ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z)) = z := by
      change (IntegralObjectQuotient.finiteZero l E W.left (n + 1)).hom.val.app U
        (((s (n + 1)).hom.f 0).val.app U
          (((s (n + 1)).inv.f 0).val.app U
            ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z))) = z
      exact (congrArg
        (fun y ↦ (IntegralObjectQuotient.finiteZero l E W.left (n + 1)).hom.val.app U y)
        hsi).trans (congrArg (fun f ↦ f.val.app U z)
          (IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv_hom_id)
    have hsr := hs'.trans (congrArg
      (fun y ↦ (integralCoefficientSheafTransition l E W.left n).hom.app U y) hz)
    have hci := congrArg (fun f ↦ (f.f 0).val.app U
      ((IntegralObjectQuotient.finiteZero l E W.left n).inv.val.app U
        ((integralCoefficientSheafTransition l E W.left n).hom.app U z)))
      (c n).inv_hom_id
    change ((c n).hom.f 0).val.app U
      (((c n).inv.f 0).val.app U
        ((IntegralObjectQuotient.finiteZero l E W.left n).inv.val.app U
          ((integralCoefficientSheafTransition l E W.left n).hom.app U z))) =
      (IntegralObjectQuotient.finiteZero l E W.left n).inv.val.app U
        ((integralCoefficientSheafTransition l E W.left n).hom.app U z) at hci
    change (IntegralObjectQuotient.finiteZero l E W.left n).hom.val.app U
      (((c n).hom.f 0).val.app U
        ((((integralOperationsPullbackTransition l E W.hom n).app
          (IntegralObjectQuotient.singleModule l E X L)).f 0).val.app U
            (((c (n + 1)).inv.f 0).val.app U
              ((IntegralObjectQuotient.finiteZero l E W.left (n + 1)).inv.val.app U z)))) = _
    exact (congrArg (fun y ↦
      (IntegralObjectQuotient.finiteZero l E W.left n).hom.val.app U
        (((c n).hom.f 0).val.app U y)) ht).trans
      ((congrArg (fun y ↦
        (IntegralObjectQuotient.finiteZero l E W.left n).hom.val.app U y) hci).trans
        ((congrArg (fun f ↦ f.val.app U
          ((integralCoefficientSheafTransition l E W.left n).hom.app U z))
          (IntegralObjectQuotient.finiteZero l E W.left n).inv_hom_id).trans hsr.symm))
  · exact ((SheafOfModules.restrictScalars
        (integralOperationsProjection.{u, u} l E W.left (n + 1))).map_isZero
      (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
        (SheafOfModules.unit (integralCoefficientSheaf.{u, u} l E W.left (n + 1))) i
        hi)).eq_of_src _ _

end WeilConjectures
