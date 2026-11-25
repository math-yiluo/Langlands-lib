/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.Algebra.Homology.RingIsomorphismTensorTransport
import WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.PreservesTotalTensorKFlatQuasiIsoSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import Mathlib.Algebra.Category.Ring.Limits
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquationsSupplement
import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceDataSupplement
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.CategoryTheory.Monoidal.BraidedLocalizationSquare
import WeilConjectures.CategoryTheory.Monoidal.OplaxOfLaxSquare
import WeilConjectures.ProperBaseChange.CompletedPullbackStrictNormalization

/-! # Actual completion unit in Roos coordinates

Source: Bhatt--Scholze, Lemma 6.5.9(4), Remark 6.8.15; Stacks Tags 0941 and 099N(5).
(blueprint: lem-weil-pbc-integral-actual-unit-roos-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] completedModulePullback HasDerivedCategory.standard
  SheafOfModules.monoidalCategory completedReductionModuleTowerFunctor

private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

private def strictPullbackAugmentation
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) :
    ((completedTowerConstant d U).mapHomologicalComplex (.up ℤ)).obj
      (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K) ⟶
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).obj
      ((completedReductionComplexTowerFunctor T d).obj K) :=
  letI := completedReductionModuleTowerFunctor_additive T d
  eqToHom (completedPullbackConstantComplex_eq h d K) ≫
    ((completedTowerModulePullback h d).mapHomologicalComplex (.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (completedReductionModuleUnit d T) (.up ℤ)).app K)

private theorem strictPullbackAugmentation_component
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{u}} (h : U ⟶ T)
    (K : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ) (n : ℕ) (i : ℤ) :
    ((strictPullbackAugmentation d h K).f i).app (op n) =
      (completedModulePullback h d).map
        (((completedReductionModuleUnit d T).app (K.X i)).app (op n)) := by
  simp only [strictPullbackAugmentation, HomologicalComplex.comp_f, NatTrans.comp_app,
    HomologicalComplex.eqToHom_f, eqToHom_app, eqToHom_refl, Category.id_comp]
  rfl

private theorem transport_kflat
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (P : (integralOperationsGoodComplex l E T).FullSubcategory) :
    CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (R := pbcAdicCompletion T (pbcIntegralDatum l E))
      ((pbcIntegralTransportComplex T l E).obj P.obj) := by
  let : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} T
  let : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} T
  let ff := fullyFaithfulSheafCompose (ProEt.topology T)
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  let e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
      completedIntegralCommRingSheafUnrestricted l E T :=
    ff.preimageIso (integralDetailedCoefficientComparison T l E)
  have he : (adicLisseForget T).map e.hom =
      (integralDetailedCoefficientComparison T l E).hom := ff.map_preimage _
  obtain ⟨tr⟩ := SheafOfModules.ringIso_tensor_transport.{u + 1, u, u + 1, u + 2, u + 2} e
  have ht := (tr.kflat_iff P.obj).mpr P.property.1
  dsimp only [SheafOfModules.scalarRestriction] at ht
  simpa only [he] using ht

private abbrev boundary {B : Type*} [Category* B] [Abelian B]
    [HasCountableProducts B] (C : ℕᵒᵖ ⥤ CochainComplex B ℤ) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
    (integralOperationsTowerStep C)

private theorem cocone_ext {B : Type*} [Category* B] [Abelian B]
    {K L M : CochainComplex B ℤ} (f : K ⟶ L)
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

private theorem cofiberMap_eq_coneMap
    {B : Type*} [Category B] [Abelian B]
    {K L K' L' : CochainComplex B ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      CochainComplex.mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    CochainComplex.mappingCone.map, CochainComplex.mappingCone.desc,
    CochainComplex.mappingCone.descCochain,
    CochainComplex.HomComplex.Cochain.comp_v, CochainComplex.mappingCone.inl,
    CochainComplex.mappingCone.fst, CochainComplex.mappingCone.snd,
    CochainComplex.mappingCone.inr]

open CochainComplex CochainComplex.HomComplex in
private theorem roosMap_coordinates
    {A : Type*} [Category* A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    integralOperationsRoosMap a ≫ mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')) =
      mappingCocone.fst (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)) ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (integralOperationsRoosMap a).f p ≫
          (mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h =
        (mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h ≫
            (Limits.Pi.map (fun n : ℕ ↦ a.app (op n))).f q := by
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square a)]
  let φ := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)
  let ψ := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')
  let b := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  let c := mappingCone.map φ ψ b b (integralOperationsRoos_square a)
  have hc₁ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.fst ψ).1.v (p + -1) p (by omega) =
      (mappingCone.fst φ).1.v (p + -1) p (by omega) ≫ b.f p := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  have hc₂ (p : ℤ) : c.f (p + -1) ≫
      (mappingCone.snd ψ).v (p + -1) (p + -1) (add_zero _) =
      (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) ≫ b.f (p + -1) := by
    simp [c, mappingCone.ext_from_iff φ p (p + -1) (by omega), mappingCone.map]
  constructor
  · apply HomologicalComplex.hom_ext
    intro p
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫ (mappingCocone.fst ψ).f p =
      (mappingCocone.fst φ).f p ≫ b.f p
    simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_map_f', mappingCocone.fst,
      HomologicalComplex.neg_f_apply, Cocycle.homOf_f, Cocycle.leftShift_coe,
      Cochain.leftShift_v (mappingCone.fst ψ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega),
      mul_zero, Int.reduceSub, mul_neg, neg_mul, one_mul, neg_neg, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self, zero_add,
      Int.negOnePow_one, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Units.neg_smul, one_smul,
      Cochain.leftShift_v (mappingCone.fst φ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega), Category.assoc]
    erw [Category.id_comp, Category.id_comp]
    exact hc₁ p
  · intro p q h
    obtain rfl : q = p + -1 := h.symm
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫
      (mappingCocone.snd ψ).v p (p + -1) h =
        (mappingCocone.snd φ).v p (p + -1) h ≫ b.f (p + -1)
    simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_map_f', mappingCocone.snd,
      Cochain.leftShift_v (mappingCone.snd ψ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      mul_neg, mul_one, neg_neg, Int.reduceSub, neg_mul, one_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
      Int.reduceAdd, Int.negOnePow_even 2 ⟨1, rfl⟩, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, one_smul,
      Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega), Category.assoc]
    erw [Category.id_comp, Category.id_comp]
    exact hc₂ p

private theorem lift_roos
    {B : Type*} [Category* B] [Abelian B]
    [HasCountableProducts B] [HasLimitsOfShape ℕᵒᵖ B]
    [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (P : CochainComplex B ℤ) (J I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ)
    (a : ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapHomologicalComplex (.up ℤ)).obj P ⟶ J)
    (r : J ⟶ I) (c : P ⟶ integralOperationsRoos J.asFunctor)
    (hc₁ : ∀ n i, c.f i ≫ (CochainComplex.mappingCocone.fst (boundary J.asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦ J.asFunctor.obj (op m)) n).f i = (a.f i).app (op n))
    (hc₂ : ∀ i j hij,
      c.f i ≫ (CochainComplex.mappingCocone.snd (boundary J.asFunctor)).v i j hij = 0)
    (ι : ((lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (.up ℤ)).obj I ⟶
      integralOperationsRoos I.asFunctor)
    (hι₁ : ∀ n i, ι.f i ≫ (CochainComplex.mappingCocone.fst (boundary I.asFunctor)).f i ≫
      (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i)
    (hι₂ : ∀ i j hij,
      ι.f i ≫ (CochainComplex.mappingCocone.snd (boundary I.asFunctor)).v i j hij = 0) :
    (((constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B) ⊣ lim).mapHomologicalComplex
      (.up ℤ)).homEquiv P I (a ≫ r)) ≫ ι =
      c ≫ integralOperationsRoosFunctor.map
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r) := by
  let adj := (constLimAdj : (Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B) ⊣ lim).mapHomologicalComplex
    (.up ℤ)
  let b := adj.homEquiv P I (a ≫ r)
  let α : J.asFunctor ⟶ I.asFunctor :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r
  have hb : ((Functor.const ℕᵒᵖ : B ⥤ ℕᵒᵖ ⥤ B).mapHomologicalComplex (.up ℤ)).map b ≫
      adj.counit.app I = a ≫ r := by
    exact (adj.homEquiv_counit P I b).symm.trans
      ((adj.homEquiv P I).symm_apply_apply (a ≫ r))
  have hbπ (i : ℤ) (n : ℕ) : b.f i ≫ limit.π (I.X i) (op n) =
      (a.f i).app (op n) ≫ (r.f i).app (op n) := by
    exact congrArg (fun f ↦ (f.f i).app (op n)) hb
  apply cocone_ext (boundary I.asFunctor)
  · intro i
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (.up ℤ) i)
      (fun n : ℕ ↦ I.asFunctor.obj (op n))).hom_ext
    rintro ⟨n⟩
    simp only [Fan.mk_π_app, HomologicalComplex.eval_map, HomologicalComplex.comp_f,
      Category.assoc]
    rw [hι₁]
    have hm := congrArg (fun f ↦ f.f i) (roosMap_coordinates α).1
    simp only [HomologicalComplex.comp_f] at hm
    have hp := congrArg (fun f ↦ f.f i) (Pi.map_π (fun n : ℕ ↦ α.app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hp
    change b.f i ≫ limit.π (I.X i) (op n) =
      c.f i ≫ (integralOperationsRoosMap α).f i ≫
        (CochainComplex.mappingCocone.fst (boundary I.asFunctor)).f i ≫
          (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i
    erw [reassoc_of% hm, hp]
    have hcoords := hbπ i n
    rw [← hc₁ n i] at hcoords
    change b.f i ≫ limit.π (I.X i) (op n) =
      c.f i ≫ (CochainComplex.mappingCocone.fst (boundary J.asFunctor)).f i ≫
        (Pi.π (fun m : ℕ ↦ J.asFunctor.obj (op m)) n).f i ≫ (r.f i).app (op n)
    simpa only [Category.assoc] using hcoords
  · intro i j hij
    simp only [HomologicalComplex.comp_f, Category.assoc]
    change b.f i ≫ ι.f i ≫
        (CochainComplex.mappingCocone.snd (boundary I.asFunctor)).v i j hij =
      c.f i ≫ (integralOperationsRoosMap α).f i ≫
        (CochainComplex.mappingCocone.snd (boundary I.asFunctor)).v i j hij
    erw [hι₂, comp_zero, (roosMap_coordinates α).2,
      ← Category.assoc, hc₂, zero_comp]

/-- On a good representative, the actual strict completion unit is computed by
any chain augmentation with quotient first coordinates and zero second coordinate.
This concerns only the actual completed coefficients; no ordinary integral model
comparison or pullback identification is an input.

Source: Stacks 0941, proof of lemma-derived-limit-is-ok, and 099N(5);
Bhatt--Scholze, Lemma 6.5.9(4).
(blueprint: lem-weil-pbc-integral-actual-unit-roos-normalization).

Proof: transport P by the quotient-normalized coefficient equivalence, which
preserves flat terms and K-flatness. Expand completedPullbackComparison into the
constant-derived-limit unit and the pulled strict quotient augmentation. Apply
the representative normalizations of completedPullbackConstantIso and
completedReductionTowerUnit, retaining their universal counits. Naturality of
the tower pullback counit identifies their composite with the actual module
quotient augmentation. The constant/limit adjunction sends this strict
augmentation followed by r to its compatible-family lift into the termwise
limit of I. Naturality of the right-derived unit and its computation on I
therefore give the left side as ordinary pullback's computation counit followed
by the localized compatible-family lift and localized iota. The first
coordinates of this chain composite are augmentation_n followed by r_n; its
second coordinate is zero. The same equations hold for c followed by the Roos
map of r, by diagonal functoriality of the mapping cocone. Product and cocone
extensionality identify the chain maps. Localize to get the displayed formula.
The argument uses whole strict towers; equality of derived level projections
alone is not used. Zero complexes and empty schemes obey the same formulas. -/
theorem pbc_integral_actual_unit_roos_normalization
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {U T : Scheme.{u}} (h : U ⟶ T)
    (P : (integralOperationsGoodComplex l E T).FullSubcategory)
    (c : ((completedModulePullback h (pbcIntegralDatum l E)).mapHomologicalComplex
        (.up ℤ)).obj ((pbcIntegralTransportComplex T l E).obj P.obj) ⟶
      integralOperationsRoos (pbcIntegralActualTower l E h P.obj).asFunctor)
    (hc₁ : ∀ (n : ℕ) (i : ℤ),
      c.f i ≫ (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (pbcIntegralActualTower l E h P.obj).asFunctor.obj (op n))
          (integralOperationsTowerStep (pbcIntegralActualTower l E h P.obj).asFunctor))).f i ≫
        (Pi.π (fun m : ℕ ↦
          (pbcIntegralActualTower l E h P.obj).asFunctor.obj (op m)) n).f i =
        (pbcIntegralActualTowerAugmentation l E h P.obj n).f i)
    (hc₂ : ∀ (i j : ℤ) (hij : i + -1 = j),
      c.f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ (pbcIntegralActualTower l E h P.obj).asFunctor.obj (op n))
          (integralOperationsTowerStep (pbcIntegralActualTower l E h P.obj).asFunctor))).v
        i j hij = 0)
    (I : CochainComplex (pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
    (r : pbcIntegralActualTower l E h P.obj ⟶ I) [QuasiIso r] [I.IsKInjective]
    (ι : ((lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
      pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))).mapHomologicalComplex
        (.up ℤ)).obj I ⟶ integralOperationsRoos I.asFunctor)
    (hι₁ : ∀ (n : ℕ) (i : ℤ),
      ι.f i ≫ (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
          (integralOperationsTowerStep I.asFunctor))).f i ≫
        (Pi.π (fun m : ℕ ↦ I.asFunctor.obj (op m)) n).f i =
        ((NatTrans.mapHomologicalComplex (lim.π (op n)) (.up ℤ)).app I).f i)
    (hι₂ : ∀ (i j : ℤ) (hij : i + -1 = j),
      ι.f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ I.asFunctor.obj (op n))
          (integralOperationsTowerStep I.asFunctor))).v
        i j hij = 0) :
    completedPullbackComparison h (pbcIntegralDatum l E)
        ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P.obj)) ≫
      (completedTowerRlim (pbcIntegralDatum l E) U).map
        (pbcIntegralActualTowerCounit l E h P.obj ≫ DerivedCategory.Q.map r) ≫
      (Functor.rightDerivedFunctorObjQIso
        (lim : pbcTowers U (pbcAdicCompletion U (pbcIntegralDatum l E)) ⥤
          pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) I).hom ≫
      DerivedCategory.Q.map ι =
    (completedOrdinaryPullback h (pbcIntegralDatum l E)).map
        ((pbcIntegralDetailedTransportFactors T l E).hom.app P.obj) ≫
      completedOrdinaryPullbackComplexCounit h (pbcIntegralDatum l E)
        ((pbcIntegralTransportComplex T l E).obj P.obj) ≫
      DerivedCategory.Q.map c ≫ DerivedCategory.Q.map
        (integralOperationsRoosFunctor.map
          (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map r)) := by
  let d := pbcIntegralDatum l E
  let K := (pbcIntegralTransportComplex T l E).obj P.obj
  let a := strictPullbackAugmentation d h K
  have ha (n : ℕ) (i : ℤ) : (a.f i).app (op n) =
      (pbcIntegralActualTowerAugmentation l E h P.obj n).f i := by
    exact strictPullbackAugmentation_component d h K n i
  have hc := lift_roos
    (((completedModulePullback h d).mapHomologicalComplex (.up ℤ)).obj K)
    (pbcIntegralActualTower l E h P.obj) I a r c
    (fun n i ↦ (hc₁ n i).trans (ha n i).symm) hc₂ ι hι₁ hι₂
  have ht := completedPullbackComparison_strict_normalization d h K (transport_kflat l E T P)
    ((integralDetailedTransport T l E).obj (DerivedCategory.Q.obj P.obj))
    ((pbcIntegralDetailedTransportFactors T l E).hom.app P.obj) I r
  erw [← strictPullbackAugmentation] at ht
  have ht' := congrArg (fun f ↦ f ≫ DerivedCategory.Q.map ι) ht
  simp only [Category.assoc, ← DerivedCategory.Q.map_comp] at ht'
  erw [hc] at ht'
  simpa only [pbcIntegralActualTowerCounit, DerivedCategory.Q.map_comp,
    Category.assoc] using ht'

end WeilConjectures
