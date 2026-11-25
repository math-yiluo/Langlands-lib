/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.ProperBaseChange.IntegralActualUnitRoosNormalization
import WeilConjectures.ProperBaseChange.IntegralCompletionTransportCoordinates
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleWeaklyContractibleEvaluationColimitsSupplement
import Mathlib.CategoryTheory.Sites.CompatibleSheafification
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Completion map compatibility on resolving representatives

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5).
(blueprint: lem-weil-pbc-integral-completion-matching-on-good).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

private abbrev boundary {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
    (integralOperationsTowerStep C)

private theorem cocone_ext {A : Type*} [Category* A] [Abelian A]
    {K L M : CochainComplex A ℤ} (f : K ⟶ L)
    (a b : M ⟶ CochainComplex.mappingCocone f)
    (hf : ∀ i, a.f i ≫ (CochainComplex.mappingCocone.fst f).f i =
      b.f i ≫ (CochainComplex.mappingCocone.fst f).f i)
    (hs : ∀ i j hij, a.f i ≫ (CochainComplex.mappingCocone.snd f).v i j hij =
      b.f i ≫ (CochainComplex.mappingCocone.snd f).v i j hij) : a = b := by
  ext i
  have hid := CochainComplex.mappingCocone.id_X f i (i - 1) (by omega)
  have ha := congrArg (fun z ↦ a.f i ≫ z) hid
  have hb := congrArg (fun z ↦ b.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at ha hb
  rw [hf, hs] at ha
  exact ha.symm.trans hb

private instance baseLimitAdditive {A : Type*} [Category* A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

private def termwiseLimitCone {A : Type*} [Category* A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private def termwiseLimitIsLimit {A : Type*} [Category* A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (termwiseLimitCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private def termwiseLimitIso {A : Type*} [Category* A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (termwiseLimitIsLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

private theorem termwiseLimitIso_π {A : Type*} [Category* A] [Abelian A]
    [HasLimitsOfShape ℕᵒᵖ A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    (termwiseLimitIso I).hom ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  IsLimit.conePointUniqueUpToIso_hom_comp (termwiseLimitIsLimit I)
    (limit.isLimit I.asFunctor) n

private theorem normalized_inclusion_eq {A : Type*} [Category* A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (ι : ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ⟶
      integralOperationsRoos I.asFunctor)
    (hf : ∀ n i, ι.f i ≫ (CochainComplex.mappingCocone.fst (boundary I.asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i)
    (hs : ∀ i j hij,
      ι.f i ≫ (CochainComplex.mappingCocone.snd (boundary I.asFunctor)).v i j hij = 0) :
    ι = (termwiseLimitIso I).hom ≫ roosι I := by
  apply cocone_ext (boundary I.asFunctor)
  · intro i
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval A (.up ℤ) i)
      (fun n : ℕ ↦ I.asFunctor.obj (op n))).hom_ext
    rintro ⟨n⟩
    simp only [Fan.mk_π_app, HomologicalComplex.eval_map, Category.assoc,
      HomologicalComplex.comp_f]
    rw [hf]
    have h := congrArg (fun f ↦ f.f i)
      (termwiseLimitIso_π I (op n))
    rw [← h]
    have hproj : roosProj I =
        CochainComplex.mappingCocone.fst (boundary I.asFunctor) := by rfl
    have he := congrArg (fun f ↦ f.f i) (roosι_eval I n)
    simp only [roosEval, hproj, HomologicalComplex.comp_f] at he
    simpa only [HomologicalComplex.comp_f, Category.assoc] using
      congrArg (fun k ↦ (termwiseLimitIso I).hom.f i ≫ k) he.symm
  · intro i j hij
    simp only [HomologicalComplex.comp_f, Category.assoc, hs]
    change 0 = _ ≫ ((roosLift _ _).f i ≫
      (CochainComplex.mappingCocone.snd (roosU I)).v i j hij)
    unfold roosLift
    rw [CochainComplex.mappingCocone.lift_f_snd_v]
    simp

private instance abSheafify (T : Scheme.{u}) :
    HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, 0} T

private instance abLocallyBijective (T : Scheme.{u}) :
    (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, 0} T

private theorem actual_products_exact (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (pbcModules T R) := by
  have : HasCountableProducts (pbcModules T R) :=
    (ProEt.countableProducts_exact.{u, u, 0} T R).1
  have hp := (ProEt.countableProducts_exact.{u, u, 0} T R).2.2
  have : (lim (J := Discrete ℕ) (C := pbcModules T R)).PreservesEpimorphisms := by
    constructor
    intro F G f hf
    have h : lim.map f = (Pi.isoLimit F).inv ≫
        Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩) ≫ (Pi.isoLimit G).hom := by
      apply limit.hom_ext
      rintro ⟨n⟩
      simp
    have : Epi (Limits.Pi.map (fun n : ℕ ↦ f.app ⟨n⟩)) :=
      hp ℕ (fun n ↦ F.obj ⟨n⟩) (fun n ↦ G.obj ⟨n⟩)
        (fun n ↦ f.app ⟨n⟩) (fun n ↦ inferInstance)
    rw [h]
    infer_instance
  exact hasExactLimitsOfShape_of_preservesEpi (pbcModules T R) (Discrete ℕ)

private theorem normalized_inclusion_quasiIso (T : Scheme.{u})
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
    (I : CochainComplex (pbcTowers T R) ℤ) [I.IsKInjective]
    (hi : ∀ i : ℤ, Injective (I.X i))
    (ι : ((lim : pbcTowers T R ⥤ pbcModules T R).mapHomologicalComplex (.up ℤ)).obj I ⟶
      integralOperationsRoos I.asFunctor)
    (hf : ∀ n i, ι.f i ≫ (CochainComplex.mappingCocone.fst (boundary I.asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
      ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i)
    (hs : ∀ i j hij,
      ι.f i ≫ (CochainComplex.mappingCocone.snd (boundary I.asFunctor)).v i j hij = 0) :
    QuasiIso ι := by
  have := actual_products_exact T R
  obtain ⟨CF, κ, hCF, hι⟩ := strictRoosDerivation.{u + 1, u, 0, u + 2} (ProEt.topology T)
    ((adicLisseForget T).obj R)
    (fun V a b ↦ @mul_comm (R.obj.obj V) _ a b)
  have := hι I hi
  rw [normalized_inclusion_eq I ι hf hs]
  infer_instance

private structure ChosenResolution {B : Type*} [Category* B] [Abelian B]
    (C : CochainComplex B ℤ) where
  I : CochainComplex B ℤ
  r : C ⟶ I
  qis : QuasiIso r
  kinj : I.IsKInjective
  hi : ∀ i : ℤ, Injective (I.X i)

@[irreducible] private def chooseResolution {B : Type*} [Category* B] [Abelian B]
    [IsGrothendieckAbelian.{w} B] (C : CochainComplex B ℤ) : ChosenResolution C := by
  let I := (CochainComplex.kInjectiveResolutionFunctor.{w} B).obj C
  let r := (CochainComplex.toKInjectiveResolution.{w} B).app C
  exact ⟨I, r, (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{w} B C).2,
    inferInstance, fun _ ↦ inferInstance⟩

private theorem combine_completion_diagram {V : Type*} [Category* V]
    {A B C D E F G H I J K : V}
    {e : A ⟶ B} {d : B ⟶ E} {f : A ⟶ D} {g : D ⟶ E}
    {t : E ⟶ H} {s : D ⟶ G} {j : G ⟶ F} {c : F ⟶ I}
    {q : C ⟶ F} {p : K ⟶ C} {a : A ⟶ K} {h : G ⟶ H} {z : H ⟶ I}
    (r : I ⟶ J) (hη : e ≫ d = f ≫ g) (hn : g ≫ t = s ≫ h)
    (hd : a ≫ p ≫ q = f ≫ s ≫ j) (hc : j ≫ c = h ≫ z) :
    e ≫ d ≫ t ≫ z ≫ r = a ≫ p ≫ q ≫ c ≫ r := by
  calc
    e ≫ d ≫ t ≫ z ≫ r = (e ≫ d) ≫ t ≫ z ≫ r := by simp only [Category.assoc]
    _ = (f ≫ g) ≫ t ≫ z ≫ r := by rw [hη]
    _ = f ≫ (g ≫ t) ≫ z ≫ r := by simp only [Category.assoc]
    _ = f ≫ (s ≫ h) ≫ z ≫ r := by rw [hn]
    _ = f ≫ s ≫ (h ≫ z) ≫ r := by simp only [Category.assoc]
    _ = f ≫ s ≫ (j ≫ c) ≫ r := by rw [hc]
    _ = (f ≫ s ≫ j) ≫ c ≫ r := by simp only [Category.assoc]
    _ = (a ≫ p ≫ q) ≫ c ≫ r := by rw [hd]
    _ = _ := by simp only [Category.assoc]

/-- On a flat-term K-flat representative, the independently normalized model
comparison carries the ordinary completion map to the actual strict-tower unit.
The pullback identification and model comparison are inputs, not constructed here.

Source: Stacks 0941 and 099N(5); Bhatt--Scholze, Lemma 6.5.9(4).
(blueprint: lem-weil-pbc-integral-completion-matching-on-good).

Proof: choose an entire-tower K-injective resolution r of the actual pulled
reduction tower, with injective tower terms. The model-matching hypothesis
supplies t, z and the limit inclusion iota for this resolution. The coordinate
identities characterize iota as the inclusion (limit projections,0); exact
countable products and the split transitions in injective towers show it is a
quasi-isomorphism. Postcompose the desired equation with the invertible actual
tower counit, derived r, universal Rlim computation and localized iota. Substitute
the model-matching formula for b. Substitute the defining good-representative
formula of ordinaryIntegralCompletionComparison and the derived_counit equation
of a. At the chain level ordinaryIntegralCompletionChain has first coordinate
the quotient augmentation and second coordinate zero. The augmentation identity
for t and both coordinate equations for z identify its transported composite
with the map having coordinates r_n times the actual quotient augmentation and
zero. Naturality of the strict-tower derived-limit unit gives these same two
coordinates for completedPullbackComparison followed by the limit inclusion.
The mapping-cocone extensionality lemma and product extensionality prove equality
of the chain maps. Localize and cancel the invertible postcomposition. This
establishes the asserted equation on P, without any extension to arbitrary
derived objects. -/
theorem pbc_integral_completion_matching_on_good
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (a : PbcProperIntegralPullbackIdentification l E h)
    (b : integralDerivedPullback l E h ⋙ integralDetailedTransport U l E ≅
      integralDetailedTransport T l E ⋙ completedReductionTower T (pbcIntegralDatum l E) ⋙
        completedTowerPullback h (pbcIntegralDatum l E) ⋙
          completedTowerRlim (pbcIntegralDatum l E) U)
    (hm : PbcProperIntegralModelMatching l E h a b)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
      (integralDetailedTransport U l E).map
          ((ordinaryIntegralCompletionComparison l E h).app (DerivedCategory.Q.obj P.obj)) ≫
          b.hom.app (DerivedCategory.Q.obj P.obj) =
        a.derivedIso.hom.app (DerivedCategory.Q.obj P.obj) ≫
          completedPullbackComparison h (pbcIntegralDatum l E)
            ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P.obj)) := by
  classical
  obtain ⟨hact, t, z, ht, hz, hb⟩ := hm P
  let G := pbcIntegralTransportComplex U l E
  let j := (NatIso.mapHomologicalComplex a.moduleIso (.up ℤ)).app P.obj
  let c := j.inv ≫ G.map (ordinaryIntegralCompletionChain l E h P.obj) ≫ z.hom
  obtain ⟨hjc, hc₁, hc₂⟩ :=
    pbc_integral_completion_transport_coordinates l E h a.moduleIso P.obj t z ht hz
  let B := pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))
  have : IsGrothendieckAbelian.{u + 1} B :=
    reductionTower_isGrothendieckAbelian U
      ((adicLisseForget U).obj (pbcAdicCompletion U (pbcIntegralDatum l E)))
  let d := chooseResolution.{u + 1} (pbcIntegralActualTower l E h P.obj)
  let I := d.I
  let r := d.r
  have : I.IsKInjective := d.kinj
  have : QuasiIso r := d.qis
  have hi (i : ℤ) : Injective (I.X i) := d.hi i
  obtain ⟨ι, hι₁, hι₂, hb⟩ := hb I r hi
  have : QuasiIso ι := normalized_inclusion_quasiIso U _ I hi ι hι₁ hι₂
  have : IsIso (pbcIntegralActualTowerCounit l E h P.obj) := hact
  let R := completedTowerRlim (pbcIntegralDatum l E) U
  let v := R.map (pbcIntegralActualTowerCounit l E h P.obj ≫ DerivedCategory.Q.map r) ≫
    (Functor.rightDerivedFunctorObjQIso
      (lim : B ⥤ pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) I).hom ≫
    DerivedCategory.Q.map ι
  have : IsIso v := by dsimp only [v]; infer_instance
  apply (cancel_mono v).1
  dsimp only [v]
  simp only [Category.assoc]
  rw [hb]
  have hη : (ordinaryIntegralCompletionComparison l E h).app (DerivedCategory.Q.obj P.obj) ≫
      (integralDerivedPullbackComparison l E h).hom.app P =
      ordinaryIntegralPullComplexCounit l E h P.obj ≫
        DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E h P.obj) :=
    (ordinaryIntegralCompletionComparison_existsUnique l E h).exists.choose_spec P
  have hn := (pbcIntegralDetailedTransportFactors U l E).hom.naturality
    (ordinaryIntegralCompletionChain l E h P.obj)
  simp only [Functor.comp_map] at hn
  change (integralDetailedTransport U l E).map
    (DerivedCategory.Q.map (ordinaryIntegralCompletionChain l E h P.obj)) ≫ _ = _ at hn
  have hu := pbc_integral_actual_unit_roos_normalization l E h P c hc₁ hc₂ I r ι hι₁ hι₂
  rw [hu]
  change (NatTrans.mapHomologicalComplex a.moduleIso.hom (.up ℤ)).app P.obj ≫ c =
    (pbcIntegralTransportComplex U l E).map
      (ordinaryIntegralCompletionChain l E h P.obj) ≫ z.hom at hjc
  have hη' := congrArg (integralDetailedTransport U l E).map hη
  simp only [Functor.map_comp] at hη'
  have hc' := congrArg DerivedCategory.Q.map hjc
  simp only [Functor.map_comp] at hc'
  exact combine_completion_diagram
    (DerivedCategory.Q.map (integralOperationsRoosFunctor.map
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)))
    hη' hn (a.derived_counit P) hc'

end WeilConjectures
