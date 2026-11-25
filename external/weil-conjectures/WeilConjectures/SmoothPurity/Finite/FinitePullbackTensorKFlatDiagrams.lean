/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackDescentData

/-! # Naturality of the two finite tensor comparison composites

Source: Stacks Tags 06YS and 07A4.
(blueprint: lem-pur-finite-pullback-tensor-kflat-diagrams).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u v w
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  Functor.mapDerivedCategory finitePullbackTensorConstruction
  finiteIntrinsicClosed finiteIntrinsicTensorModels
  proEtaleTensorPullbackTotalIso proEtaleTensorPullbackTotal
  proEtaleOrdinaryTensorPullback SheafOfModules.monoidalCategory
attribute [local implicit_reducible] integralCoefficientSheaf integralCoefficientCommRingSheaf
  finiteIntrinsicDerivedTensor
  coefficientTotalTensor coefficientKFlatInclusion coefficientFiniteInternalHom
  FinitePullbackTensorRep.totalTensor
attribute [local semireducible] FinitePullbackTensorRep.pull
attribute [local implicit_reducible] FinitePullbackTensorRep.pull
  CategoryTheory.Functor.map₂HomologicalComplex
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
attribute [local instance] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived FinitePullbackTensorRep.ordinary_additive
  FinitePullbackTensorRep.ordinary_limits FinitePullbackTensorRep.ordinary_colimits
attribute [local implicit_reducible] FinitePullbackTensorRep.modules_abelian
  FinitePullbackTensorRep.modules_derived

private theorem comparison_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    FinitePullbackTensorRep.comparison l E f n P Q =
      (proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
        (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
        P Q).inv := by
  unfold FinitePullbackTensorRep.comparison
  rfl

private theorem constructionIso_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))) :
    (finitePullbackTensorConstructionIso l E f n).hom.app (M, N) =
      ((@finitePullbackTensorConstruction l _ E _ _ _ X Y f n hX hY) M N).hom := by
  unfold finitePullbackTensorConstructionIso finitePullbackTensorConstruction
  rfl

/-- Restrict the prescribed tensor-model comparison to a family of K-flat complexes.
Source: Stacks 06YS (blueprint: lem-pur-finite-pullback-tensor-kflat-diagrams). -/
@[irreducible] def finiteTensorModelOnKFlatFamily (W : Scheme.{u}) (n : ℕ)
    {C : Type v} [Category.{w} C]
    (I : C ⥤ CochainComplex (normalizedDVRModules l E W n) ℤ)
    (h : ∀ K, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (I.obj K)) :
    (I.prod I) ⋙ FinitePullbackTensorRep.totalTensor l E W n ⋙ DerivedCategory.Q ≅
      ((I ⋙ DerivedCategory.Q).prod (I ⋙ DerivedCategory.Q)) ⋙
        finiteIntrinsicDerivedTensor l E W n := by
  let KP : ObjectProperty (CochainComplex (normalizedDVRModules l E W n) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n)
  let j := KP.lift I h
  exact isoWhiskerLeft (j.prod j) (finiteIntrinsicTensorModels l E W n).comparison

private theorem finiteTensorModelOnKFlatFamily_app (W : Scheme.{u}) (n : ℕ)
    {C : Type v} [Category.{w} C]
    (I : C ⥤ CochainComplex (normalizedDVRModules l E W n) ℤ)
    (h : ∀ K, CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E W n) (I.obj K)) (A B : C) :
    (finiteTensorModelOnKFlatFamily l E W n I h).hom.app (A, B) =
      ((finiteIntrinsicTensorModels l E W n).iso (ProEt.topology W)
        (integralCoefficientCommRingSheaf l E W n) (finiteIntrinsicClosed l E W n)
        (I.obj A) (I.obj B) (h A) (h B)).hom := by
  unfold finiteTensorModelOnKFlatFamily
  rfl

/-- Both composites in the ordinary pullback tensor square are natural on every
family of K-flat complexes with K-flat pullbacks. Source: Stacks 06YS and 07A4
(blueprint: lem-pur-finite-pullback-tensor-kflat-diagrams).
Proof: restrict the finite tensor-model natural isomorphisms to the given full
subcategory. The first composite consists of the source model, the derived
pullback tensor comparison, and the two pullback factor maps. The second consists
of the factor map on the total tensor, the ordinary total tensor pullback
comparison, and the target tensor model. Whiskering and composition give the two
natural transformations; their components are exactly the stated formulas. -/
theorem finitePullbackTensor_kflat_diagrams {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (PR : ObjectProperty (CochainComplex (normalizedDVRModules l E Y n) ℤ))
    (hy : ∀ K, PR K → CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E Y n) K)
    (hx : ∀ K, PR K → CochainComplex.IsKFlatIndependentCoefficients
      (R := integralCoefficientCommRingSheaf l E X n)
      ((FinitePullbackTensorRep.pull l E f n).obj K)) :
    ∃ a b :
        (PR.ι.prod PR.ι ⋙ FinitePullbackTensorRep.totalTensor l E Y n ⋙
          DerivedCategory.Q ⋙ finiteDerivedPullback l E n f) ⟶
        ((PR.ι ⋙ FinitePullbackTensorRep.pull l E f n ⋙ DerivedCategory.Q).prod
          (PR.ι ⋙ FinitePullbackTensorRep.pull l E f n ⋙ DerivedCategory.Q)) ⋙
            finiteIntrinsicDerivedTensor l E X n,
      (∀ A B : PR.FullSubcategory, a.app (A, B) =
        (finiteDerivedPullback l E n f).map
          ((finiteIntrinsicTensorModels l E Y n).iso (ProEt.topology Y)
            (integralCoefficientCommRingSheaf l E Y n) (finiteIntrinsicClosed l E Y n)
            A.obj B.obj (hy A.obj A.property) (hy B.obj B.property)).hom ≫
        (finitePullbackTensorConstruction l E f n (DerivedCategory.Q.obj A.obj)
          (DerivedCategory.Q.obj B.obj)).hom ≫
        (finiteIntrinsicDerivedTensor l E X n).map
          (Prod.mkHom ((FinitePullbackTensorRep.factors l E f n).hom.app A.obj)
            ((FinitePullbackTensorRep.factors l E f n).hom.app B.obj))) ∧
      (∀ A B : PR.FullSubcategory, b.app (A, B) =
        (FinitePullbackTensorRep.factors l E f n).hom.app
          (FinitePullbackTensorRep.tensor l E Y n A.obj B.obj) ≫
        DerivedCategory.Q.map (FinitePullbackTensorRep.comparison l E f n A.obj B.obj) ≫
        ((finiteIntrinsicTensorModels l E X n).iso (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X n) (finiteIntrinsicClosed l E X n)
          ((FinitePullbackTensorRep.pull l E f n).obj A.obj)
          ((FinitePullbackTensorRep.pull l E f n).obj B.obj)
          (hx A.obj A.property) (hx B.obj B.property)).hom) := by
  let R := integralCoefficientCommRingSheaf l E Y n
  let S := integralCoefficientCommRingSheaf l E X n
  let F := FinitePullbackTensorRep.pull l E f n
  let LF := finiteDerivedPullback l E n f
  let TY := finiteIntrinsicDerivedTensor l E Y n
  let TX := finiteIntrinsicDerivedTensor l E X n
  let i := PR.ι
  let q := i ⋙ DerivedCategory.Q
  let z := i ⋙ F ⋙ DerivedCategory.Q
  let rY := finiteTensorModelOnKFlatFamily l E Y n i (fun A ↦ hy A.obj A.property)
  let rX := finiteTensorModelOnKFlatFamily l E X n (i ⋙ F) (fun A ↦ hx A.obj A.property)
  let ep := isoWhiskerLeft i (FinitePullbackTensorRep.factors l E f n)
  obtain ⟨_, _, b0, hb0⟩ := proEtaleTensorPullbackDescentData f
    (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n)
  let b := isoWhiskerLeft (i.prod i) b0.symm
  let t := (i.prod i) ⋙ FinitePullbackTensorRep.totalTensor l E Y n
  let L : t ⋙ DerivedCategory.Q ⋙ LF ≅ (z.prod z) ⋙ TX :=
    isoWhiskerRight rY LF ≪≫
      isoWhiskerLeft (q.prod q) (finitePullbackTensorConstructionIso l E f n) ≪≫
      isoWhiskerRight (NatIso.prod ep ep) TX
  let N : t ⋙ DerivedCategory.Q ⋙ LF ≅ (z.prod z) ⋙ TX :=
    isoWhiskerLeft t (FinitePullbackTensorRep.factors l E f n) ≪≫
      isoWhiskerRight b DerivedCategory.Q ≪≫ rX
  refine ⟨L.hom, N.hom, ?_, ?_⟩
  · intro A B
    change LF.map (rY.hom.app (A, B)) ≫
      (finitePullbackTensorConstructionIso l E f n).hom.app
        (DerivedCategory.Q.obj A.obj, DerivedCategory.Q.obj B.obj) ≫
      TX.map (Prod.mkHom ((FinitePullbackTensorRep.factors l E f n).hom.app A.obj)
        ((FinitePullbackTensorRep.factors l E f n).hom.app B.obj)) = _
    rw [finiteTensorModelOnKFlatFamily_app, constructionIso_app]
    rfl
  · intro A B
    change (FinitePullbackTensorRep.factors l E f n).hom.app
        (FinitePullbackTensorRep.tensor l E Y n A.obj B.obj) ≫
      DerivedCategory.Q.map (b0.inv.app (A.obj, B.obj)) ≫ rX.hom.app (A, B) = _
    rw [hb0, ← comparison_eq, finiteTensorModelOnKFlatFamily_app]
    rfl

end WeilConjectures
