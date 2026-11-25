/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientModels
public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.CategoryTheory.StrictRoosComparison
public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.StrictRoosDerivation
public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.RoosComplex
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.StrictRoosNormalization
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import Mathlib.Basic.Denumerable
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosChainMaps
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosDescent
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.AlgebraicGeometry.ExactProductFunctorRoosCompatibility

import WeilConjectures.TraceFormula.Isomorphism.IsomorphismStrictQuotientMultiplication
import WeilConjectures.TraceFormula.Isomorphism.IsomorphismQuotientRoosComparison
import WeilConjectures.TraceFormula.Supporting.StrictQuotientCompletionRealization

/-! # Multiplication and product comparison on entire strict quotient cones

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md, (2)--(3); Stacks Tags 0941 and 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent).

The positive exponent is n+1. The finite pullbacks and quotient transitions are the
published strict constructions. Multiplication is specified on their sheafified
unit generators; bundled linearity gives all scalar multiples. The two existing
mapping-cocone projections specify the product comparison on both coordinates,
including zero off-diagonal entries. The completion comparison is normalized on
every simultaneous quotient presentation through the existing K-injective-normalized Roos model.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  SheafOfModules.monoidalCategory CategoryTheory.Limits.limit

universe t u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

private theorem component_conjugation
    {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (τ : F ⟶ G) {A B : C} (e : A ≅ B) :
    τ.app B = F.map e.inv ≫ τ.app A ≫ G.map e.hom := by
  rw [← τ.naturality e.hom, ← F.map_comp_assoc, e.inv_hom_id, F.map_id, Category.id_comp]

private theorem component_substitution
    {C : Type*} [Category C] {D : Type*} [Category D]
    {F G : C ⥤ D} (tau : F ⟶ G) {A B : C} (e : A ≅ B)
    {D1 D2 D3 : D} (p : F.obj A ⟶ D1) (q : D1 ⟶ D2)
    (r : D2 ⟶ D3) (s : D3 ⟶ G.obj A)
    (h : tau.app A = p ≫ q ≫ r ≫ s) :
    tau.app B = F.map e.inv ≫ p ≫ q ≫ r ≫ s ≫ G.map e.hom := by
  rw [component_conjugation tau e, h]
  simp only [Category.assoc]

private theorem mapped_pair_identity
    {C : Type*} [Category C] {D : Type*} [Category D]
    (F : C ⥤ D) {A B : C} (a : A ⟶ B) (a' : B ⟶ A) (h : a ≫ a' = 𝟙 A) :
    F.map a ≫ F.map a' = 𝟙 (F.obj A) := by
  rw [← F.map_comp, h, F.map_id]

private theorem remove_two_pairs
    {C : Type*} [Category C] {A B D E F : C}
    (f : A ⟶ B) (a : B ⟶ D) (a' : D ⟶ B) (b : D ⟶ E) (b' : E ⟶ D)
    (k : A ⟶ F) (k' : F ⟶ E) (ha : a ≫ a' = 𝟙 B) (hb : b ≫ b' = 𝟙 D)
    (h : f ≫ a ≫ b = k ≫ k') : f = k ≫ k' ≫ b' ≫ a' := by
  have hb' : b ≫ b' ≫ a' = a' := by
    rw [← Category.assoc, hb, Category.id_comp]
  have h' := congrArg (fun z ↦ z ≫ b' ≫ a') h
  simpa only [Category.assoc, hb', ha, Category.comp_id] using h'

-- Combine independent witnesses before specializing their predicates to large categories.
private theorem combine_comparisons
    {A : Sort*} {B : Sort*} {C : Sort*} {D : Sort*}
    {P1 P2 : A → Prop} {Q1 Q2 : B → Prop} {R : C → Prop} {F : Prop}
    {S1 S2 : A → B → C → D → Prop}
    (ha : ∃ a, P1 a ∧ P2 a) (hb : ∃ b, Q1 b ∧ Q2 b) (hc : ∃ c, R c)
    (hf : F) (hd : ∀ a b c, ∃ d, S1 a b c d ∧ S2 a b c d) :
    ∃ a b c d, P1 a ∧ P2 a ∧ F ∧ Q1 b ∧ Q2 b ∧ R c ∧
      S1 a b c d ∧ S2 a b c d := by
  obtain ⟨a, ha1, ha2⟩ := ha
  obtain ⟨b, hb1, hb2⟩ := hb
  obtain ⟨c, hc⟩ := hc
  obtain ⟨d, hd1, hd2⟩ := hd a b c
  exact ⟨a, b, c, d, ha1, ha2, hf, hb1, hb2, hc, hd1, hd2⟩

section ComparisonAPI

variable {C0 C1 C2 C3 C4 C5 C6 : Type*}
  [Category C0] [Category C1] [Category C2] [Category C3]
  [Category C4] [Category C5] [Category C6]
  (i : C0 ⥤ C1) (p : C1 ⥤ C3) (t : C1 ⥤ C2) (v : C2 ⥤ C3)
  (hx : C3 ⥤ C4) (hy : C2 ⥤ C1) (f : C1 ⥤ C4)
  (qy : C1 ⥤ C5) (qx : C4 ⥤ C6) (g : C5 ⥤ C6)
  (q : C0 ⥤ C5) (r : C5 ⥤ C5)
  (j : i ⋙ p ≅ i ⋙ t ⋙ v)
  (eta : i ⋙ t ⋙ hy ⋙ f ≅ i ⋙ t ⋙ v ⋙ hx)
  (rho : q ⋙ r ≅ i ⋙ t ⋙ hy ⋙ qy) (a : qy ⋙ g ≅ f ⋙ qx)

-- These constructions keep functor reassociation abstract.
private def chain_comparison : i ⋙ (p ⋙ hx) ⋙ qx ≅ i ⋙ t ⋙ hy ⋙ f ⋙ qx :=
  isoWhiskerRight (isoWhiskerRight j hx ≪≫ eta.symm) qx

private def descent_comparison : q ⋙ (r ⋙ g) ≅ i ⋙ (p ⋙ hx) ⋙ qx :=
  (isoWhiskerRight rho g ≪≫ isoWhiskerLeft (i ⋙ t ⋙ hy) a) ≪≫
    (chain_comparison (i := i) (p := p) (t := t) (v := v)
      (hx := hx) (hy := hy) (f := f) (qx := qx) (j := j) (eta := eta)).symm

private theorem descent_comparison_component {L : C5 ⥤ C6}
    (Theta : L ≅ r ⋙ g) (k : q ⋙ L ≅ i ⋙ (p ⋙ hx) ⋙ qx)
    (h : isoWhiskerLeft q Theta ≪≫
      descent_comparison (i := i) (p := p) (t := t) (v := v)
        (hx := hx) (hy := hy) (f := f) (qy := qy) (qx := qx) (g := g)
        (q := q) (r := r) (j := j) (eta := eta) (rho := rho) (a := a) = k)
    (x : C0) :
    Theta.hom.app (q.obj x) ≫ g.map (rho.hom.app x) ≫
        a.hom.app (hy.obj (t.obj (i.obj x))) =
      k.hom.app x ≫ qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x) := by
  let c := chain_comparison (i := i) (p := p) (t := t) (v := v)
    (hx := hx) (hy := hy) (f := f) (qx := qx) (j := j) (eta := eta)
  have hh := congrArg (fun z ↦ z.hom.app x) h
  have hh' := congrArg (fun z ↦ z ≫ c.hom.app x) hh
  dsimp only [descent_comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, isoWhiskerLeft_hom, whiskerLeft_app] at hh'
  have hc : (isoWhiskerRight (isoWhiskerRight j hx ≪≫ eta.symm) qx).inv.app x ≫
      qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x) = 𝟙 _ :=
    (isoWhiskerRight (isoWhiskerRight j hx ≪≫ eta.symm) qx).inv_hom_id_app x
  dsimp only [c, chain_comparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, Functor.comp_obj] at hh'
  simpa only [Functor.comp_obj, Category.assoc, hc, Category.comp_id] using hh'

private theorem normalized_cone_descent (L : C5 ⥤ C6)
    (k : q ⋙ L ≅ i ⋙ (p ⋙ hx) ⋙ qx)
    (univ : ∀ (G : C5 ⥤ C6) (e : q ⋙ G ≅ i ⋙ (p ⋙ hx) ⋙ qx),
      ∃! theta : L ≅ G, isoWhiskerLeft q theta ≪≫ e = k) :
    ∃ (Theta : L ≅ r ⋙ g),
      (∀ x : C0,
        Theta.hom.app (q.obj x) ≫ g.map (rho.hom.app x) ≫
            a.hom.app (hy.obj (t.obj (i.obj x))) =
          k.hom.app x ≫ qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x)) ∧
      (∀ (N : C5) (x : C0) (e : q.obj x ≅ N),
        Theta.hom.app N = L.map e.inv ≫ k.hom.app x ≫
          qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x) ≫
          a.inv.app (hy.obj (t.obj (i.obj x))) ≫ g.map (rho.inv.app x) ≫
          (r ⋙ g).map e.hom) := by
  let e' := descent_comparison (i := i) (p := p) (t := t) (v := v)
    (hx := hx) (hy := hy) (f := f) (qy := qy) (qx := qx) (g := g)
    (q := q) (r := r) (j := j) (eta := eta) (rho := rho) (a := a)
  obtain ⟨Theta, hTheta, _⟩ := univ (r ⋙ g) e'
  have hrep (x : C0) :
      Theta.hom.app (q.obj x) ≫ g.map (rho.hom.app x) ≫
          a.hom.app (hy.obj (t.obj (i.obj x))) =
        k.hom.app x ≫ qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x) := by
    exact descent_comparison_component (i := i) (p := p) (t := t) (v := v)
      (hx := hx) (hy := hy) (f := f) (qy := qy) (qx := qx) (g := g)
      (q := q) (r := r) (j := j) (eta := eta) (rho := rho) (a := a)
      (Theta := Theta) (k := k) (h := hTheta) (x := x)
  refine ⟨Theta, hrep, ?_⟩
  intro N x e
  have h : Theta.hom.app (q.obj x) = k.hom.app x ≫
      qx.map (hx.map (j.hom.app x) ≫ eta.inv.app x) ≫
      a.inv.app (hy.obj (t.obj (i.obj x))) ≫ g.map (rho.inv.app x) := by
    exact remove_two_pairs _ _ _ _ _ _ _
      (mapped_pair_identity g _ _ (rho.hom_inv_id_app x))
      (a.hom_inv_id_app (hy.obj (t.obj (i.obj x)))) (hrep x)
  exact component_substitution Theta.hom e _ _ _ _ h

end ComparisonAPI

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section DescentProof

attribute [local instance 3000] integralTowerHasDerivedCategory

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  inverseImageCompletedCoefficientMap isoSectionwiseModuleInverseImage
  Functor.mapHomologicalComplex

attribute [local irreducible] integralOperationsGoodComplex
  coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

attribute [local irreducible] integralOperationsRoos trfQuotientTowerFunctor
  integralOperationsPullbackTowerFunctor unrestrictedIntegralComplexFunctor

private theorem pullback_descent_universal
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (G : DerivedCategory (integralTowerModules l E Y) ⥤
      DerivedCategory (integralTowerModules l E X))
    (e : integralOperationsGoodLocalization l E Y ⋙ G ≅
      integralOperationsPullbackOnGood l E g) :
    ∃! i : integralDerivedPullback l E g ≅ G,
      isoWhiskerLeft (integralOperationsGoodLocalization l E Y) i ≪≫ e =
        integralDerivedPullbackComparison l E g := by
  unfold integralDerivedPullback integralDerivedPullbackComparison
  exact (integralPullbackDescent l E g).universal G e

private theorem assembled_cone_descent
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (S : CoefficientDerivedSystemCalculus l E Y)
    (j : (integralOperationsGoodComplex l E Y).ι ⋙
          integralOperationsPullbackTowerFunctor l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g)
    (eta : (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ integralOperationsRoosFunctor ⋙
            trfInverseImageComplex l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          trfInverseImageTower l E g ⋙ integralOperationsRoosFunctor)
    (rho : integralOperationsGoodLocalization l E Y ⋙
          (S.reduction ⋙ coefficientSequenceLimit l E Y) ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q) :
    ∃ (Theta : integralDerivedPullback l E g ≅
        (S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙ inverseImageIntegralDerived l E g),
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
        Theta.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (inverseImageIntegralDerived l E g).map (rho.hom.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) =
          (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map ((j.hom.app P)) ≫ eta.inv.app P)) ∧
      -- This equation includes every resolution and every derived object N.
      (∀ (N : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ N),
        Theta.hom.app N =
          (integralDerivedPullback l E g).map e.inv ≫
            (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map (j.hom.app P) ≫ eta.inv.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.inv.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) ≫
            (inverseImageIntegralDerived l E g).map (rho.inv.app P) ≫
            ((S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
              inverseImageIntegralDerived l E g).map e.hom) := by
  exact normalized_cone_descent
    (i := (integralOperationsGoodComplex l E Y).ι)
    (p := integralOperationsPullbackTowerFunctor l E g)
    (t := trfQuotientTowerFunctor l E Y) (v := trfInverseImageTower l E g)
    (hx := integralOperationsRoosFunctor) (hy := integralOperationsRoosFunctor)
    (f := trfInverseImageComplex l E g) (qy := DerivedCategory.Q)
    (qx := DerivedCategory.Q) (g := inverseImageIntegralDerived l E g)
    (q := integralOperationsGoodLocalization l E Y)
    (r := S.reduction ⋙ coefficientSequenceLimit l E Y)
    (j := j) (eta := eta) (rho := rho)
    (a := (inverseImageIntegralModules l E g).mapDerivedCategoryFactors)
    (L := integralDerivedPullback l E g) (k := integralDerivedPullbackComparison l E g)
    (univ := pullback_descent_universal l E g)

end DescentProof

attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  integralOperationsGoodComplex coefficientSequenceLimit TrfCompletionRoosNormalized
  integralDerivedPullback integralDerivedPullbackComparison integralPullbackDescent
  Functor.mapDerivedCategoryFactors Functor.mapDerivedCategory DerivedCategory.Q
  integralOperationsRoosMap

-- The fixed statement elaborates both strict section and derived-category coordinates.
/-- Multiplication and the canonical product comparison give the same natural
isomorphism on all strict quotient cones and after localization.

Source: blueprint main-20261015, sec-trace-formula/sk-d-weil/
prop-trf-rational-frobenius-integral-model.proof.md (2)--(3); Stacks 0941 and 08TC
(blueprint: lem-trf-isomorphism-multiplication-cone-descent).

Proof, following the ten steps of the node:
1. The site equivalence identifies inverse-image sections with sections after
postcomposition by g. Transport through c inverse preserves addition, kernels,
cokernels and sectionwise products. Product projections fix phi and its inverse.
2. Resolve by one flat-term K-flat Q. The derived-system evaluation calculus gives
its entire strict quotient system. The ambient pullback is H(C), and normalized
strict Roos comparison identifies L R with H(D), without completeness or bounds.
3. Scalar extension through c_n has multiplication inverse to x to x tensor 1.
The completed projection equation proves completed linearity. Both composites
are identities by the tensor balancing relation, also after sheafification.
4. The actual quotient transition sends x tensor a to tau(x) tensor reduction(a).
The coefficient square shows multiplication commutes with this map. Restrictions,
differentials and arbitrary chain maps satisfy the same generator identities.
5. Product projections give phi G(s)=s phi and hence the difference square.
Apply phi to both coordinates of the shifted cone. Its differential is
(-db-(1-s)a,da), so this is an invertible chain map with no cross terms. The
exact-product derived-limit comparison gives this same map under normalized Roos
identifications: (b,a) to (a,-b) converts its signed-coordinate convention.
6. Apply H to the strict multiplication isomorphism and follow by eta inverse.
Products and cone coordinates prove naturality of this entire chain isomorphism.
7. A homotopy h acts on reductions and their products, commuting with the quotient
shift. On the cone its homotopy is (-h,h); the cross term h(1-s)-(1-s)h vanishes.
Thus both constructions and their natural isomorphism respect homotopies.
8. The ambient-operation well-definedness theorem inverts quasi-isomorphisms on
good representatives. On the other side, reduction, strict Roos localization and
exact inverse image invert them too. Their normalized comparisons are functorial.
9. The resolving-class localization theorem extends the strict natural isomorphism
and its inverse uniquely to the ordinary unbounded derived category. Uniqueness
makes both composites identity and proves naturality on every derived morphism.
10. The representative equation below holds after every isomorphism Q(P) to N.
Consequently every allowed resolution gives this same component through its
canonical comparisons. No completeness, constructibility or boundedness is used. -/
theorem isomorphismMultiplicationConeDescent
    {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (S : CoefficientDerivedSystemCalculus l E Y)
    (r : IntegralComparisonRoosModel l E Y) :
    (inverseImageIntegralModules l E g).Additive ∧
    PreservesFiniteLimits (inverseImageIntegralModules l E g) ∧
    PreservesFiniteColimits (inverseImageIntegralModules l E g) ∧
    (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
      IsIso (trfQuotientProductComparison l E g Q.obj)) ∧
    ∃ (j : (integralOperationsGoodComplex l E Y).ι ⋙
          integralOperationsPullbackTowerFunctor l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ trfInverseImageTower l E g)
      (eta : (integralOperationsGoodComplex l E Y).ι ⋙
          trfQuotientTowerFunctor l E Y ⋙ integralOperationsRoosFunctor ⋙
            trfInverseImageComplex l E g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          trfInverseImageTower l E g ⋙ integralOperationsRoosFunctor)
      (rho : integralOperationsGoodLocalization l E Y ⋙
          (S.reduction ⋙ coefficientSequenceLimit l E Y) ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ trfQuotientTowerFunctor l E Y ⋙
          integralOperationsRoosFunctor ⋙ DerivedCategory.Q)
      (Theta : integralDerivedPullback l E g ≅
        (S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙ inverseImageIntegralDerived l E g),
      -- The unit-generator equation and bundled linearity specify multiplication.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.hom.app Q).app (op n)).f i).val.app (op U)
            ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
              (proEtaleIsoCommaArrow g U).op
              (integralOperationsPullbackGenerator l E g n
                (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
                ((proEtaleIsoPostcompose g).obj U) x)) = x) ∧
      -- The inverse is the actual sheafified x to x tensor 1 map.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (n : ℕ) (i : ℤ)
        (U : X.ProEt)
        (x : (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i).val.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (((j.inv.app Q).app (op n)).f i).val.app (op U) x =
          ((((integralOperationsPullbackLevel l E g n).obj Q.obj).X i).val.map
            (proEtaleIsoCommaArrow g U).op
            (integralOperationsPullbackGenerator l E g n
              (((unrestrictedIntegralFiniteComplex l E Y n).obj Q.obj).X i)
              ((proEtaleIsoPostcompose g).obj U) x))) ∧
      (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        (trfInverseImageComplex l E g).map (trfQuotientDifference l E Y Q.obj) ≫
            trfQuotientProductComparison l E g Q.obj =
          trfQuotientProductComparison l E g Q.obj ≫ trfInverseQuotientDifference l E g Q.obj) ∧
      -- Equality on the a coordinate of H, as a chain map.
      (∀ Q : (integralOperationsGoodComplex l E Y).FullSubcategory,
        eta.hom.app Q ≫ CochainComplex.mappingCocone.fst
            (trfInverseQuotientDifference l E g Q.obj) =
          (trfInverseImageComplex l E g).map
              (CochainComplex.mappingCocone.fst (trfQuotientDifference l E Y Q.obj)) ≫
            trfQuotientProductComparison l E g Q.obj) ∧
      -- Equality on the shifted b coordinate; together these specify a diagonal map.
      (∀ (Q : (integralOperationsGoodComplex l E Y).FullSubcategory) (p : ℤ),
        (eta.hom.app Q).f (p + 1) ≫
            (CochainComplex.mappingCocone.snd
              (trfInverseQuotientDifference l E g Q.obj)).v (p + 1) p
                (add_neg_cancel_right p 1) =
          (inverseImageIntegralModules l E g).map
              ((CochainComplex.mappingCocone.snd
                (trfQuotientDifference l E Y Q.obj)).v (p + 1) p
                  (add_neg_cancel_right p 1)) ≫
            (trfQuotientProductComparison l E g Q.obj).f p) ∧
      TrfCompletionRoosNormalized l E Y S r rho ∧
      -- The descended map is H(j) followed by eta inverse on every representative.
      (∀ (P : (integralOperationsGoodComplex l E Y).FullSubcategory),
        Theta.hom.app (DerivedCategory.Q.obj P.obj) ≫
            (inverseImageIntegralDerived l E g).map (rho.hom.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.hom.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) =
          (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map ((j.hom.app P)) ≫ eta.inv.app P)) ∧
      -- This equation includes every resolution and every derived object N.
      (∀ (N : DerivedCategory (integralTowerModules l E Y))
        (P : (integralOperationsGoodComplex l E Y).FullSubcategory)
        (e : DerivedCategory.Q.obj P.obj ≅ N),
        Theta.hom.app N =
          (integralDerivedPullback l E g).map e.inv ≫
            (integralDerivedPullbackComparison l E g).hom.app P ≫
            DerivedCategory.Q.map
              (integralOperationsRoosFunctor.map (j.hom.app P) ≫ eta.inv.app P) ≫
            (inverseImageIntegralModules l E g).mapDerivedCategoryFactors.inv.app
              (integralOperationsRoos ((trfQuotientTowerFunctor l E Y).obj P.obj)) ≫
            (inverseImageIntegralDerived l E g).map (rho.inv.app P) ≫
            ((S.reduction ⋙ coefficientSequenceLimit l E Y) ⋙
              inverseImageIntegralDerived l E g).map e.hom) := by
  have hc := isomorphismQuotientRoosComparison l E g
  refine ⟨inferInstance, inferInstance, inferInstance, hc.1, ?_⟩
  exact combine_comparisons (isomorphismStrictQuotientMultiplication l E g) hc.2.2
    (strictQuotientCompletionRealization l E Y S r) hc.2.1
    (assembled_cone_descent l E g S)

end WeilConjectures
