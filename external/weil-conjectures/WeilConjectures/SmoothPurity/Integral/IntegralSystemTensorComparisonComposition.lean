/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonStrictComparisonAux
public import WeilConjectures.SmoothPurity.IntegralCoherence.SequencePullbackMonoidal
public import WeilConjectures.CategoryTheory.TensorPullbackRepresentativeDescentComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SmoothPurity.Integral.IntegralStrictComparisonComposition
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction

/-! # Composition law of the coherent system pullback/tensor comparison

Source: Stacks 07A4, 0D6D and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).

The coherent system comparison `pullbackTensorSystemComparison` is written on the
derived inverse image of the sequence-site interface `pullbackTensorSequenceInverse`.
Transporting it along the proved equality with the strict inverse image
`integralComparisonSequencePullback` gives a comparison on the derived strict inverse
images. It is the descent of the generator-normalized strict cochain comparison, and
therefore inherits the strict composition law with the adjunction-normalized compositor.
All maps are maps of entire coefficient systems, before any finite evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.SemilinearSections.abelianSheafify
attribute [-instance] WeilConjectures.SemilinearSections.locallyBijective
attribute [-instance] WeilConjectures.finiteSystemSequenceSmall
attribute [-instance] AlgebraicGeometry.ProEtale.VaryingRing.sequenceSiteSmall

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The derived identification of the two names of the strict sequence inverse image.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
def sequenceDerivedPullbackBridge {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f ≅ integralComparisonDerivedSequencePullback l E f :=
  Functor.mapDerivedCategoryNatIso (eqToIso (CompletedQuotient.sequencePullback_eq l E f))

/-- The derived bridge is the localization of the strict bridge.
Source: Stacks 03D2, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem sequenceDerivedPullbackBridge_factors {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app A ≫
        DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).hom.app A) =
      (sequenceDerivedPullbackBridge l E f).hom.app (DerivedCategory.Q.obj A) ≫
        (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app A := by
  unfold CompletedQuotient.pullBridge sequenceDerivedPullbackBridge
  exact (Functor.mapDerivedCategoryNatIso_fac
    (eqToIso (CompletedQuotient.sequencePullback_eq l E f)) A).symm

/-- Strict inverse image preserves K-flat strict quotient complexes.
Source: Stacks 0DEN, 07A4
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem integralComparisonSequenceGood {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P) :
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × X.ProEt) (inferInstance : Category.{u} (ℕ × X.ProEt))
      (pullbackTensorSequenceSmall X) (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X)
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P) := by
  with_unfolding_all exact pullbackTensorSequenceGood l E f P hP

/-- The coherent system pullback/tensor comparison on the derived strict inverse images.
Source: Stacks 07A4, 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
def integralSystemTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackTensorCalculus l E Y).systemClosed.tensor ⋙
        integralComparisonDerivedSequencePullback l E f ≅
      ((integralComparisonDerivedSequencePullback l E f).prod
        (integralComparisonDerivedSequencePullback l E f)) ⋙
        (pullbackTensorCalculus l E X).systemClosed.tensor :=
  Functor.isoWhiskerLeft _ (sequenceDerivedPullbackBridge l E f).symm ≪≫
    pullbackTensorSystemComparison l E f ≪≫
    Functor.isoWhiskerRight (NatIso.prod (sequenceDerivedPullbackBridge l E f)
      (sequenceDerivedPullbackBridge l E f)) _

/-- The generator-normalized strict cochain comparison on the strict inverse images.
Source: Stacks 07A4
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
def strictTensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology Y))
        (coefficientSequenceCommRingSheaf l E Y) ⋙
        (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ≅
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).prod
        ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X) :=
  Functor.isoWhiskerLeft _ (CompletedQuotient.pullBridge l E f).symm ≪≫
    pullbackTensorSequenceCochain l E f ≪≫
    Functor.isoWhiskerRight (NatIso.prod (CompletedQuotient.pullBridge l E f)
      (CompletedQuotient.pullBridge l E f)) _

/-- The components of the strict comparison are the recorded quotient comparisons.
Source: Stacks 07A4
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem strictTensorComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y) :
    (strictTensorComparison l E f).app (P, Q) = CompletedQuotient.comparison l E f P Q := by
  apply Iso.ext
  unfold strictTensorComparison CompletedQuotient.comparison
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    NatIso.prod_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.prod_hom]
  rfl

section Square

attribute [local irreducible] pullbackTensorCalculus pullbackTensorSystemModel
  pullbackTensorSequenceCochain coefficientTotalTensor
  CompletedQuotient.pullBridge sequenceDerivedPullbackBridge Functor.mapDerivedCategory
  Functor.leftAdjoint HasDerivedCategory.standard Scheme.residueField

/-- The transported system comparison is the descent of the strict cochain comparison.
Source: Stacks 06YU, 07A4
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: insert the derived bridge, whose localization formula is the strict bridge, into
the defining K-flat normalization of `pullbackTensorSystemComparison`. Naturality of the
bridge and of the target tensor model move the strict bridges to the cochain level,
where they assemble to the strict comparison. -/
theorem integralSystemTensorComparison_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) (inferInstance : Category.{u} (ℕ × Y.ProEt))
      (pullbackTensorSequenceSmall Y) (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y) Q) :
    (integralComparisonDerivedSequencePullback l E f).map
        (pullbackTensorSystemModel l E Y P Q hP hQ).hom ≫
      (integralSystemTensorComparison l E f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app P)
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app Q)) =
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app _ ≫
      DerivedCategory.Q.map ((strictTensorComparison l E f).hom.app (P, Q)) ≫
      (pullbackTensorSystemModel l E X _ _ (integralComparisonSequenceGood l E f P hP)
        (integralComparisonSequenceGood l E f Q hQ)).hom := by
  have h₀ := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec P Q hP hQ
  have hb := sequenceDerivedPullbackBridge_factors l E f
  have hbn := (sequenceDerivedPullbackBridge l E f).inv.naturality
    (pullbackTensorSystemModel l E Y P Q hP hQ).hom
  have hr := (pullbackTensorCalculus l E X).systemTensorModel.comparison.hom.naturality
    (X := (⟨((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj P,
        pullbackTensorSequenceGood l E f P hP⟩,
      ⟨((pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)).obj Q,
        pullbackTensorSequenceGood l E f Q hQ⟩))
    (Y := (⟨((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj P,
        integralComparisonSequenceGood l E f P hP⟩,
      ⟨((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj Q,
        integralComparisonSequenceGood l E f Q hQ⟩))
    (Prod.mkHom (ObjectProperty.homMk ((CompletedQuotient.pullBridge l E f).hom.app P))
      (ObjectProperty.homMk ((CompletedQuotient.pullBridge l E f).hom.app Q)))
  have hT : (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((sequenceDerivedPullbackBridge l E f).hom.app (DerivedCategory.Q.obj P))
          ((sequenceDerivedPullbackBridge l E f).hom.app (DerivedCategory.Q.obj Q))) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app P)
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app Q)) =
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
          ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).hom.app P))
          (DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).hom.app Q))) := by
    simp only [← Functor.map_comp, prod_comp, hb]
  have hs : (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app
        ((coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology Y))
          (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q)) ≫
      DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).inv.app _) =
      (sequenceDerivedPullbackBridge l E f).inv.app _ ≫
        (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app _ := by
    have hbt := hb ((coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)).obj (P, Q))
    have h₁ := (Iso.inv_comp_eq ((sequenceDerivedPullbackBridge l E f).app _)).mpr hbt
    exact (Iso.comp_inv_eq (DerivedCategory.Q.mapIso ((CompletedQuotient.pullBridge l E f).app
      _))).mpr (h₁.symm.trans (Category.assoc _ _ _).symm)
  have eσ : (integralSystemTensorComparison l E f).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
      (sequenceDerivedPullbackBridge l E f).inv.app _ ≫
        (pullbackTensorSystemComparison l E f).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (pullbackTensorCalculus l E X).systemClosed.tensor.map
          (Prod.mkHom ((sequenceDerivedPullbackBridge l E f).hom.app (DerivedCategory.Q.obj P))
            ((sequenceDerivedPullbackBridge l E f).hom.app (DerivedCategory.Q.obj Q))) := rfl
  have es : (strictTensorComparison l E f).hom.app (P, Q) =
      (CompletedQuotient.pullBridge l E f).inv.app _ ≫
        (pullbackTensorSequenceCochain l E f).hom.app (P, Q) ≫
        (coefficientTotalTensor.{u, u + 1, u}
          (coefficientSequenceTopology (Scheme.ProEt.topology X))
          (coefficientSequenceCommRingSheaf l E X)).map
          (Prod.mkHom ((CompletedQuotient.pullBridge l E f).hom.app P)
            ((CompletedQuotient.pullBridge l E f).hom.app Q)) := rfl
  have hr' : DerivedCategory.Q.map ((coefficientTotalTensor.{u, u + 1, u}
        (coefficientSequenceTopology (Scheme.ProEt.topology X))
        (coefficientSequenceCommRingSheaf l E X)).map
        (Prod.mkHom ((CompletedQuotient.pullBridge l E f).hom.app P)
          ((CompletedQuotient.pullBridge l E f).hom.app Q))) ≫
      (pullbackTensorSystemModel l E X _ _ (integralComparisonSequenceGood l E f P hP)
        (integralComparisonSequenceGood l E f Q hQ)).hom =
      (pullbackTensorSystemModel l E X _ _ (pullbackTensorSequenceGood l E f P hP)
        (pullbackTensorSequenceGood l E f Q hQ)).hom ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom (DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).hom.app P))
          (DerivedCategory.Q.map ((CompletedQuotient.pullBridge l E f).hom.app Q))) := by
    unfold pullbackTensorSystemModel CoefficientTensorModels.iso
    exact hr
  rewrite [eσ, es]
  exact descentSquare_transport DerivedCategory.Q DerivedCategory.Q
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom
    (CompletedQuotient.pullBridge l E f) (sequenceDerivedPullbackBridge l E f) hb _ _ _ _
    (pullbackTensorSystemComparison l E f) (pullbackTensorSequenceCochain l E f) P Q _ _ _ hr' h₀

end Square

section Factors

variable {C D F : Type*} [Category C] [Category D] [Category F]
  [Abelian C] [Abelian D] [Abelian F]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory F]

/-- The derived compositor of exact functors induced by `e : H ≅ F₁ ⋙ F₂` is the
localization of the termwise compositor.
Source: Stacks 05RU, 0D6D
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced). -/
theorem mapDerivedCategoryComposition_factors (F₁ : C ⥤ D) (F₂ : D ⥤ F) (H : C ⥤ F)
    [F₁.Additive] [F₂.Additive] [H.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F₁ ⋙ F₂) (K : CochainComplex C ℤ) :
    H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) =
      (Functor.mapDerivedCategoryNatIso e ≪≫ (Functor.mapDerivedCategoryCompIso F₁ F₂).symm).hom.app
          (DerivedCategory.Q.obj K) ≫
        F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app K) ≫
        F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj K) := by
  rw [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac]

end Factors

/-- The coherent system pullback/tensor comparisons satisfy the composition law with the
derived adjunction-normalized compositor.
Source: Stacks 07A4, 0D6D and 0941
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced).
Proof: all three comparisons are descents of the strict generator-normalized cochain
comparisons, and the derived compositor is the localization of the strict compositor.
The strict comparisons satisfy the cochain composition law
(`sequenceComparison_compositionLaw`). Restriction to pairs of K-flat representatives is
faithful on natural transformations, so the law descends. -/
theorem integralSystemTensorComparison_comp {X Y Z : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y)
    (A B : coefficientSequenceDerived l E Y) :
    (integralSystemTensorComparison l E (h ≫ f)).hom.app (A, B) ≫
        (pullbackTensorCalculus l E Z).systemClosed.tensor.map
          (Prod.mkHom ((integralComparisonSystemComposition l E h f).hom.app A)
            ((integralComparisonSystemComposition l E h f).hom.app B)) =
      (integralComparisonSystemComposition l E h f).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (A, B)) ≫
        (integralComparisonDerivedSequencePullback l E h).map
          ((integralSystemTensorComparison l E f).hom.app (A, B)) ≫
        (integralSystemTensorComparison l E h).hom.app
          ((integralComparisonDerivedSequencePullback l E f).obj A,
            (integralComparisonDerivedSequencePullback l E f).obj B) := by
  let PY : ObjectProperty (CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
    @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (ℕ × Y.ProEt) _ (pullbackTensorSequenceSmall Y)
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)
  let V := (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ)).inverseImage
    PY.ι
  let : (PY.ι ⋙ DerivedCategory.Q).IsLocalization V :=
    CategoryTheory.RingedDerivedNative.kFlatLocalization.{u + 1, u, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y)
  let ff := Localization.fullyFaithfulWhiskeringLeft
    ((PY.ι ⋙ DerivedCategory.Q).prod (PY.ι ⋙ DerivedCategory.Q)) (V.prod V)
    (coefficientSequenceDerived l E Z)
  refine tensorComparisonDescent_comp DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    ((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ))
    ((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ))
    ((integralComparisonSequencePullback l E (h ≫ f)).mapHomologicalComplex (.up ℤ))
    (integralComparisonDerivedSequencePullback l E f)
    (integralComparisonDerivedSequencePullback l E h)
    (integralComparisonDerivedSequencePullback l E (h ≫ f))
    (integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom
    (integralComparisonSequencePullback l E h).mapDerivedCategoryFactors.hom
    (integralComparisonSequencePullback l E (h ≫ f)).mapDerivedCategoryFactors.hom
    PY _ _ (integralComparisonSequenceGood l E f) (integralComparisonSequenceGood l E h)
    (integralComparisonSequenceGood l E (h ≫ f)) ?_
    (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Y))
      (coefficientSequenceCommRingSheaf l E Y))
    (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology X))
      (coefficientSequenceCommRingSheaf l E X))
    (coefficientTotalTensor.{u, u + 1, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology Z))
      (coefficientSequenceCommRingSheaf l E Z)) _ _ _
    (pullbackTensorCalculus l E Y).systemTensorModel.comparison
    (pullbackTensorCalculus l E X).systemTensorModel.comparison
    (pullbackTensorCalculus l E Z).systemTensorModel.comparison
    (strictTensorComparison l E f) (strictTensorComparison l E h)
    (strictTensorComparison l E (h ≫ f))
    (integralSystemTensorComparison l E f) (integralSystemTensorComparison l E h)
    (integralSystemTensorComparison l E (h ≫ f))
    ?_ ?_ ?_
    (IntegralCoherence.compositor l E h f) (integralComparisonSystemComposition l E h f)
    ?_ ?_ ?_ ?_ A B
  · exact ff.faithful
  -- Normalize model components so the descent hypotheses match at reducible transparency.
  · intro P Q hP hQ
    have hs := integralSystemTensorComparison_square l E f P Q hP hQ
    dsimp only [pullbackTensorSystemModel, CoefficientTensorModels.iso, Iso.app_hom] at hs
    with_reducible exact hs
  · intro P Q hP hQ
    have hs := integralSystemTensorComparison_square l E h P Q hP hQ
    dsimp only [pullbackTensorSystemModel, CoefficientTensorModels.iso, Iso.app_hom] at hs
    with_reducible exact hs
  · intro P Q hP hQ
    have hs := integralSystemTensorComparison_square l E (h ≫ f) P Q hP hQ
    dsimp only [pullbackTensorSystemModel, CoefficientTensorModels.iso, Iso.app_hom] at hs
    with_reducible exact hs
  · intro P
    dsimp only [integralComparisonSystemComposition, integralComparisonDerivedSequencePullback]
    rw [Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
      Functor.mapDerivedCategoryCompIso_hom_app_factors, Functor.mapDerivedCategoryNatIso_fac]
    rfl
  · intro P Q
    have hc := CompletedQuotient.comparison_composition l E h f P Q
    simp only [← strictTensorComparison_app, Iso.app_hom] at hc
    with_reducible exact hc
  · intro P _
    infer_instance
  · intro P _
    infer_instance

end WeilConjectures
