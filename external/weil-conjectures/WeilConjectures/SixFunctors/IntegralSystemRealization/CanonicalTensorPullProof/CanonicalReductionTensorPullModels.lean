/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictComparison
import WeilConjectures.SixFunctors.Tensor.TensorReductionStrictDerivedSquare
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Representative normalization for coefficient tensor pullback

Source: blueprint fix-prop-coherence, individual coefficient comparisons; Stacks 07A4.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSystemRealization.CanonicalTensorPullProof

attribute [local irreducible] pullbackTensorCalculus

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

abbrev good (W : Scheme.{u}) := integralOperationsGoodComplex l E W

abbrev total (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (completedIntegralCommRingSheafUnrestricted l E W)

abbrev sysTotal (W : Scheme.{u}) :=
  coefficientTotalTensor.{u, u + 1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology W))
    (coefficientSequenceCommRingSheaf l E W)

def mu (d : RingedModels l E) (W : Scheme.{u}) :=
  Functor.whiskerRight (eqToIso (d.tensorClosed W)).hom (calculus l E W).reduction ≫
    (calculus l E W).reductionTensor.hom

def leftPath (o : Operations l E) (m : RealizationModel l E o)
    (d : RingedModels l E) {U V : Scheme.{u}} (f : U ⟶ V) :=
  Functor.whiskerLeft (d.tensor V).ordinary.tensor (m.reductionPull f).hom ≫
    Functor.whiskerRight (mu l E d V) (pull l E f) ≫
    Functor.whiskerLeft ((calculus l E V).reduction.prod (calculus l E V).reduction)
      (pullbackTensorSystemComparison l E f).hom

def rightPath (o : Operations l E) (m : RealizationModel l E o)
    (d : RingedModels l E) {U V : Scheme.{u}} (f : U ⟶ V) :=
  Functor.whiskerRight (ringedTensorPull l E d f).hom (calculus l E U).reduction ≫
    Functor.whiskerLeft ((ringedPull l E f).prod (ringedPull l E f)) (mu l E d U) ≫
    Functor.whiskerRight (NatTrans.prod (m.reductionPull f).hom (m.reductionPull f).hom)
      (calculus l E U).systemClosed.tensor

attribute [local implicit_reducible] CategoryTheory.Functor.map₂HomologicalComplex
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory

theorem total_good (W : Scheme.{u}) (P Q : (good l E W).FullSubcategory) :
    good l E W ((total l E W).obj (P.obj, Q.obj)) := by
  have h := SheafOfModules.KFlatTotalTensorModel.kFlat_total_tensor_model
    (completedIntegralCommRingSheafUnrestricted l E W) P.obj Q.obj
    P.property.1 Q.property.1 P.property.2 Q.property.2
  exact ⟨h.1, h.2.1⟩

theorem pull_good {U V : Scheme.{u}} (f : U ⟶ V)
    (P : (good l E V).FullSubcategory) :
    good l E U
      (((integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)).obj P.obj) := by
  exact AlgebraicGeometry.ProEtale.VaryingRing.ringPull_preserves_flat f
    ((PurCompactSupport.completed l E).ring V)
    ((PurCompactSupport.completed l E).ring U)
    ((PurCompactSupport.completed l E).pull f) P.obj P.property.1 P.property.2

/-- Reduction tensor on flat K-flat representatives agrees with the strict tensor map.
Source: tensorRepresentative and tensorReductionStrictMap_derived_square.
(blueprint: lem-sf-canonical-reduction-tensor-pull-models).

Proof: compose the tensorRepresentative equation with coefficient reduction and
apply the already normalized strict reduction tensor square. -/
theorem mu_model (d : RingedModels l E) (W : Scheme.{u})
    (P Q :
      (proEtaleFlatRepresentatives W ((PurCompactSupport.completed l E).ring W)).FullSubcategory) :
    (calculus l E W).reduction.map
        ((d.tensor W).ordinary.representative.hom.app (P, Q)) ≫
      (mu l E d W).app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
      (calculus l E W).systemClosed.tensor.map
        (Prod.mkHom ((pullbackTensorReductionModel l E W).hom.app
          ⟨P.obj, (d.tensor W).good P.obj P.property⟩)
          ((pullbackTensorReductionModel l E W).hom.app
            ⟨Q.obj, (d.tensor W).good Q.obj Q.property⟩)) =
    (pullbackTensorReductionModel l E W).hom.app
        ⟨(total l E W).obj (P.obj, Q.obj), total_good l E W
          ⟨P.obj, (d.tensor W).good P.obj P.property⟩
          ⟨Q.obj, (d.tensor W).good Q.obj Q.property⟩⟩ ≫
      DerivedCategory.Q.map (tensorReductionStrictMap l E W P.obj Q.obj) ≫
      (pullbackTensorSystemModel l E W _ _
        (pullbackTensorReductionGood l E W ⟨P.obj, (d.tensor W).good P.obj P.property⟩)
        (pullbackTensorReductionGood l E W ⟨Q.obj, (d.tensor W).good Q.obj Q.property⟩)).hom := by
  dsimp only [mu, NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp only [eqToIso.hom, eqToHom_app]
  have ht := d.tensorRepresentative W P.obj Q.obj P.property Q.property
  simp only [eqToIso.hom] at ht
  erw [ht]
  exact tensorReductionStrictMap_derived_square l E W
    ⟨P.obj, (d.tensor W).good P.obj P.property⟩
    ⟨Q.obj, (d.tensor W).good Q.obj Q.property⟩
    (total_good l E W _ _)

theorem sys_naturality (W : Scheme.{u})
    (P Q P' Q' : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients Q)
    (hp' : CochainComplex.IsKFlatIndependentCoefficients P')
    (hq' : CochainComplex.IsKFlatIndependentCoefficients Q') (a : P ⟶ P') (b : Q ⟶ Q') :
    DerivedCategory.Q.map ((sysTotal l E W).map (Prod.mkHom a b)) ≫
        (pullbackTensorSystemModel l E W P' Q' hp' hq').hom =
      (pullbackTensorSystemModel l E W P Q hp hq).hom ≫
        (calculus l E W).systemClosed.tensor.map
          (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) := by
  exact (calculus l E W).systemTensorModel.comparison.hom.naturality
    (Prod.mkHom
      (ObjectProperty.homMk (X := ⟨P, hp⟩) (Y := ⟨P', hp'⟩) a)
      (ObjectProperty.homMk (X := ⟨Q, hq⟩) (Y := ⟨Q', hq'⟩) b))

theorem map_pair_comp {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ D) {A B C' X Y Z : C}
    (a : A ⟶ B) (b : B ⟶ C') (c : X ⟶ Y) (d : Y ⟶ Z) :
    T.map (Prod.mkHom (a ≫ b) (c ≫ d)) =
      T.map (Prod.mkHom a c) ≫ T.map (Prod.mkHom b d) :=
  T.map_comp (Prod.mkHom a c) (Prod.mkHom b d)

-- Paste only in an abstract category, keeping the large coefficient functors folded.
theorem paste_left {C : Type*} [Category C]
    {A B C₀ D E₀ F G H I J K L M N O P : C}
    {v : A ⟶ B} {a : B ⟶ C₀} {b : C₀ ⟶ D} {c : D ⟶ E₀}
    {d : E₀ ⟶ F} {e : F ⟶ G} {a₀ : A ⟶ H} {r : H ⟶ C₀}
    {t : D ⟶ I} {c₀ : I ⟶ F} {x : H ⟶ J} {y : J ⟶ K} {z : K ⟶ I}
    {s₀ : K ⟶ L} {q : L ⟶ M} {w : M ⟶ G} {s₁ : J ⟶ N} {y₀ : N ⟶ L}
    {u₀ : A ⟶ O} {v₀ : O ⟶ P} {w₀ : P ⟶ N}
    (hn : v ≫ a = a₀ ≫ r) (hσ : t ≫ c₀ = c ≫ d)
    (hμ : r ≫ b ≫ t = x ≫ y ≫ z) (hsys : z ≫ c₀ ≫ e = s₀ ≫ q ≫ w)
    (hs : y ≫ s₀ = s₁ ≫ y₀) (hδ : a₀ ≫ x ≫ s₁ = u₀ ≫ v₀ ≫ w₀) :
    v ≫ a ≫ b ≫ c ≫ d ≫ e = u₀ ≫ v₀ ≫ w₀ ≫ y₀ ≫ q ≫ w := by
  rw [reassoc_of% hn, ← reassoc_of% hσ, reassoc_of% hμ,
    hsys, reassoc_of% hs, reassoc_of% hδ]

theorem paste_right {C : Type*} [Category C]
    {A B C₀ D E₀ F G H I J K L M N : C}
    {v : A ⟶ B} {a : B ⟶ C₀} {μ : C₀ ⟶ D} {p : D ⟶ E₀}
    {q : E₀ ⟶ F} {r : F ⟶ G} {t : C₀ ⟶ H} {μ' : H ⟶ E₀}
    {u₀ : A ⟶ I} {b : I ⟶ J} {c : J ⟶ H} {e' : J ⟶ K}
    {ψ : K ⟶ L} {z : L ⟶ F} {e : I ⟶ M} {β : M ⟶ K}
    {n : L ⟶ N} {w : N ⟶ G}
    (hμ : t ≫ μ' = μ ≫ p) (hr : v ≫ a ≫ t = u₀ ≫ b ≫ c)
    (hμ' : c ≫ μ' ≫ q = e' ≫ ψ ≫ z) (he : b ≫ e' = e ≫ β)
    (hz : n ≫ w = z ≫ r) :
    v ≫ a ≫ μ ≫ p ≫ q ≫ r = u₀ ≫ e ≫ β ≫ ψ ≫ n ≫ w := by
  rw [← reassoc_of% hμ, reassoc_of% hr, reassoc_of% hμ',
    reassoc_of% he, ← hz]

-- Keep the fixed normalization maps folded while the kernel checks the pasting.
attribute [local irreducible] mu proEtaleTensorPullbackTotalIso
  pullbackTensorReductionModel pullbackTensorSystemModel

def pre
    (o : Operations l E) (_m : RealizationModel l E o) (d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :=
  (calculus l E U).reduction.map ((ringedPull l E f).map
    ((d.tensor V).ordinary.representative.hom.app
      (⟨P.obj, ⟨P.property.1, P.property.2⟩⟩,
        ⟨Q.obj, ⟨Q.property.1, Q.property.2⟩⟩)))

def post
    (o : Operations l E) (_m : RealizationModel l E o) (_d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :=
  (calculus l E U).systemClosed.tensor.map (Prod.mkHom
    ((pull l E f).map ((pullbackTensorReductionModel l E V).hom.app P) ≫
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)).obj P.obj))
    ((pull l E f).map ((pullbackTensorReductionModel l E V).hom.app Q) ≫
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
        (((pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)).obj Q.obj)))

def leftNormal
    (o : Operations l E) (m : RealizationModel l E o) (_d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :=
  let R' := (calculus l E U).reduction
  let Fc := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
  let RV := (pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)
  let Sc := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let T : (good l E V).FullSubcategory :=
    ⟨(total l E V).obj (P.obj, Q.obj), total_good l E V P Q⟩
  let FT : (good l E U).FullSubcategory := ⟨Fc.obj T.obj, pull_good l E f T⟩
  let eU (X : (good l E U).FullSubcategory) :=
    (pullbackTensorReductionModel l E U).hom.app X
  let p (X : CochainComplex (integralTowerModules l E V) ℤ) :=
    (integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app X
  let δ (X : CochainComplex (integralTowerModules l E V) ℤ) :=
    DerivedCategory.Q.map (m.ordinary.reductionPullComplex l E f X)
  let c := DerivedCategory.Q.map ((pullbackTensorSequenceCochain l E f).hom.app
    (RV.obj P.obj, RV.obj Q.obj))
  let hP := pullbackTensorReductionGood l E V P
  let hQ := pullbackTensorReductionGood l E V Q
  let hSP := pullbackTensorSequenceGood l E f (RV.obj P.obj) hP
  let hSQ := pullbackTensorSequenceGood l E f (RV.obj Q.obj) hQ
  let zS := (pullbackTensorSystemModel l E U _ _ hSP hSQ).hom
  R'.map (p T.obj) ≫ eU FT ≫ δ T.obj ≫
    DerivedCategory.Q.map (Sc.map (tensorReductionStrictMap l E V P.obj Q.obj)) ≫ c ≫ zS

def rightNormal
    (o : Operations l E) (m : RealizationModel l E o) (_d : RingedModels l E)
    {U V : Scheme.{u}} (f : U ⟶ V) (P Q : (good l E V).FullSubcategory) :=
  let R' := (calculus l E U).reduction
  let Fc := (integralOrdinaryPull l E f).mapHomologicalComplex (.up ℤ)
  let RV := (pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)
  let RU := (pullbackTensorOrdinaryReduction l E U).mapHomologicalComplex (.up ℤ)
  let FP : (good l E U).FullSubcategory := ⟨Fc.obj P.obj, pull_good l E f P⟩
  let FQ : (good l E U).FullSubcategory := ⟨Fc.obj Q.obj, pull_good l E f Q⟩
  let T : (good l E V).FullSubcategory :=
    ⟨(total l E V).obj (P.obj, Q.obj), total_good l E V P Q⟩
  let FT : (good l E U).FullSubcategory := ⟨Fc.obj T.obj, pull_good l E f T⟩
  let eU (X : (good l E U).FullSubcategory) :=
    (pullbackTensorReductionModel l E U).hom.app X
  let p (X : CochainComplex (integralTowerModules l E V) ℤ) :=
    (integralOrdinaryPull l E f).mapDerivedCategoryFactors.hom.app X
  let ψU := DerivedCategory.Q.map (tensorReductionStrictMap l E U FP.obj FQ.obj)
  let β := (proEtaleTensorPullbackTotalIso f
    ((PurCompactSupport.completed l E).ring V) ((PurCompactSupport.completed l E).ring U)
    ((PurCompactSupport.completed l E).pull f) P.obj Q.obj).inv
  let hP := pullbackTensorReductionGood l E V P
  let hQ := pullbackTensorReductionGood l E V Q
  let hSP := pullbackTensorSequenceGood l E f (RV.obj P.obj) hP
  let hSQ := pullbackTensorSequenceGood l E f (RV.obj Q.obj) hQ
  let zS := (pullbackTensorSystemModel l E U _ _ hSP hSQ).hom
  R'.map (p T.obj) ≫ eU FT ≫ DerivedCategory.Q.map (RU.map β) ≫ ψU ≫
    DerivedCategory.Q.map ((sysTotal l E U).map
      (Prod.mkHom (m.ordinary.reductionPullComplex l E f P.obj)
        (m.ordinary.reductionPullComplex l E f Q.obj))) ≫ zS

instance pre_isIso (o : Operations l E) (m : RealizationModel l E o)
    (d : RingedModels l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : (good l E V).FullSubcategory) : IsIso (pre l E o m d f P Q) := by
  dsimp only [pre]
  infer_instance

instance post_isIso (o : Operations l E) (m : RealizationModel l E o)
    (d : RingedModels l E) {U V : Scheme.{u}} (f : U ⟶ V)
    (P Q : (good l E V).FullSubcategory) : IsIso (post l E o m d f P Q) := by
  let eP := asIso ((pull l E f).map
    ((pullbackTensorReductionModel l E V).hom.app P) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
      (((pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)).obj P.obj))
  let eQ := asIso ((pull l E f).map
    ((pullbackTensorReductionModel l E V).hom.app Q) ≫
    (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app
      (((pullbackTensorOrdinaryReduction l E V).mapHomologicalComplex (.up ℤ)).obj Q.obj))
  change IsIso (((calculus l E U).systemClosed.tensor.mapIso (eP.prod eQ)).hom)
  infer_instance

end WeilConjectures.IntegralSystemRealization.CanonicalTensorPullProof
