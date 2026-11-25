/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedQuotient.CompletedComparisonQuotientRealizationDefs

/-! # The canonical pullback tensor substitution square

Source: Stacks 07A4 and 0941; the canonical integral comparison realization.
(blueprint: lem-pur-completed-comparison-canonical-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option genInjectivity false
set_option genSizeOfSpec false
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
attribute [instance 4000] SheafOfModules.monoidalCategory
attribute [instance 4000] HomologicalComplex.monoidalCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open MonoidalCategory
namespace WeilConjectures.CompletedQuotient
universe u

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

attribute [local irreducible] tensorSubstitution comparison pullBridge pullSubstitution
  substitution transport strictMap scalarSubstitution scalarBeta scalarTransport
  scalarLeft scalarRight ScalarIdentity ScalarComposition ScalarAssociation NaturalSubstitution
  ScalarGood StrictCoherence ScalarLimitImage reduction scalarQuotients
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  SheafOfModules.monoidalCategory
  pullbackTensorCalculus integralDerivedPullback integralCompletedTensor
  coefficientSequenceLimit Functor.mapDerivedCategory

attribute [local implicit_reducible] coefficientSequenceInternalHom
  pullbackTensorReferenceTensor pullbackTensorReferencePullback
  constructibleIntegralTensor constructibleIntegralPullback scalarReductionSourceDerived
  StrictQuotient.SystemGood coefficientTotalTensor pullbackTensorSequenceDerived
  SheafOfModules.cochainModulesMonoidal HomologicalComplex.monoidalCategory
  value expression IntegralCoherence.value substituteInputs
  pullbackTensorSystemComparison
  pullbackTensorSequenceBase integralComparisonSequenceBaseChange
  pullbackTensorSequenceDirect integralComparisonSequenceDirectImage
  pullbackTensorSequenceInverse pullbackTensorSequenceAdjunction
  integralComparisonSequencePullback IntegralCoherence.generator
  integralComparisonSequenceGenerator sheafCompose Functor.sheafPushforwardContinuous

private local instance (priority := 10000) sequenceMonoidal (V : Scheme.{u}) :
    MonoidalCategory (coefficientSequenceModules l E V) :=
  SheafOfModules.monoidalCategory (coefficientSequenceCommRingSheaf l E V)
private local instance sequencePreadditive (V : Scheme.{u}) :
    MonoidalPreadditive (coefficientSequenceModules l E V) :=
  SheafOfModules.cochainModulesPreadditive (coefficientSequenceCommRingSheaf l E V)
private local instance sequenceColimits (V : Scheme.{u}) :
    HasColimitsOfSize.{0, 0} (coefficientSequenceModules l E V) := by
  with_unfolding_all infer_instance
private local instance sequenceLeftColim (V : Scheme.{u}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
  SheafOfModules.cochainTensorLeftPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
private local instance sequenceRightColim (V : Scheme.{u}) (M : coefficientSequenceModules l E V) :
    PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
  SheafOfModules.cochainTensorRightPreservesColimits (coefficientSequenceCommRingSheaf l E V) M
private local instance sequenceTensor (V : Scheme.{u})
    (X Y : GradedObject ℤ (coefficientSequenceModules l E V)) : X.HasTensor Y := inferInstance
private local instance sequenceFour (V : Scheme.{u})
    (X Y Z U : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasTensor₄ObjExt X Y Z U := inferInstance
private local instance sequenceLeft (V : Scheme.{u})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
private local instance sequenceRight (V : Scheme.{u})
    (X Y Z : GradedObject ℤ (coefficientSequenceModules l E V)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
private local instance (priority := 10000) complexMonoidal (V : Scheme.{u}) :
    MonoidalCategory (StrictQuotient.Complex l E V) := inferInstance

private def strictPullModel {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory.Q ⋙ pullbackTensorSequenceDerived l E f ≅
      IntegralCoherence.pull l E f ⋙ DerivedCategory.Q :=
  (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight (pullBridge l E f) DerivedCategory.Q

private theorem strictPullModel_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : StrictQuotient.Complex l E Y) :
    (strictPullModel l E f).hom.app P =
      (pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((pullBridge l E f).hom.app P) := rfl

-- Paste the two normalization squares before specializing to the derived models.
private theorem tensor_square_paste {C D : Type*} [Category C] [Category D]
    (V : C ⥤ D) (T : D × D ⥤ D) (U : C × C ⥤ C)
    {P₁ P₂ Q₁ Q₂ R S : C} {A B X₁ X₂ : D}
    (m : A ⟶ B) (n : B ⟶ T.obj (X₁, X₂))
    (a₁ : X₁ ⟶ V.obj P₁) (a₂ : X₂ ⟶ V.obj P₂)
    (u : A ⟶ V.obj R) (k : R ⟶ U.obj (P₁, P₂))
    (s : V.obj (U.obj (P₁, P₂)) ⟶ T.obj (V.obj P₁, V.obj P₂))
    (s' : V.obj (U.obj (Q₁, Q₂)) ⟶ T.obj (V.obj Q₁, V.obj Q₂))
    (e : R ≅ S) (b₁ : P₁ ≅ Q₁) (b₂ : P₂ ≅ Q₂)
    (hn : m ≫ n ≫ T.map (Prod.mkHom a₁ a₂) = u ≫ V.map k ≫ s)
    (ht : s ≫ T.map (Prod.mkHom (V.map b₁.hom) (V.map b₂.hom)) =
      V.map (U.map (Prod.mkHom b₁.hom b₂.hom)) ≫ s') :
    m ≫ n ≫ T.map (Prod.mkHom (a₁ ≫ V.map b₁.hom) (a₂ ≫ V.map b₂.hom)) =
      (u ≫ V.map e.hom) ≫ V.map (e.inv ≫ k ≫ U.map (Prod.mkHom b₁.hom b₂.hom)) ≫
        s' := by
  rw [show T.map (Prod.mkHom (a₁ ≫ V.map b₁.hom) (a₂ ≫ V.map b₂.hom)) =
    T.map (Prod.mkHom a₁ a₂) ≫ T.map (Prod.mkHom (V.map b₁.hom) (V.map b₂.hom)) from
      T.map_comp (Prod.mkHom a₁ a₂) (Prod.mkHom (V.map b₁.hom) (V.map b₂.hom))]
  simp only [← Category.assoc] at hn ⊢
  rw [hn]
  simp only [Category.assoc]
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc e.hom e.inv, e.hom_inv_id, V.map_id, Category.id_comp]

private theorem inverse_square_paste {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {A B : C} {U V W Z : D} (sy : A ≅ B) (sx : U ≅ V)
    (c : F.obj B ⟶ W) (t : W ⟶ V) (p : F.obj A ⟶ Z) (k : Z ⟶ U)
    (h : F.map sy.hom ≫ c ≫ t = p ≫ k ≫ sx.hom) :
    F.map sy.inv ≫ p ≫ k = c ≫ t ≫ sx.inv := by
  apply (cancel_epi (F.mapIso sy).hom).1
  apply (cancel_mono sx.hom).1
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  simpa only [Iso.inv_hom_id, Category.comp_id] using h.symm

-- The normalization square compares several large functor models.
private theorem strict_system_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P Q : StrictQuotient.Complex l E Y)
    (hP : StrictQuotient.SystemGood l E P) (hQ : StrictQuotient.SystemGood l E Q)
    (hfP : StrictQuotient.SystemGood l E ((IntegralCoherence.pull l E f).obj P))
    (hfQ : StrictQuotient.SystemGood l E ((IntegralCoherence.pull l E f).obj Q)) :
    (pullbackTensorSequenceDerived l E f).map
        (pullbackTensorSystemModel l E Y P Q hP.1 hQ.1).hom ≫
      (pullbackTensorSystemComparison l E f).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      (pullbackTensorCalculus l E X).systemClosed.tensor.map
        (Prod.mkHom ((strictPullModel l E f).hom.app P)
          ((strictPullModel l E f).hom.app Q)) =
    (strictPullModel l E f).hom.app (StrictQuotient.total l E P Q) ≫
      DerivedCategory.Q.map (comparison l E f P Q).hom ≫
      (pullbackTensorSystemModel l E X _ _ hfP.1 hfQ.1).hom := by
  let F := (pullbackTensorSequenceInverse l E f).mapHomologicalComplex (.up ℤ)
  let TX := (pullbackTensorCalculus l E X).systemClosed.tensor
  let U := coefficientTotalTensor.{u, u+1, u}
    (coefficientSequenceTopology (Scheme.ProEt.topology X))
    (coefficientSequenceCommRingSheaf l E X)
  let b := pullBridge l E f
  have hp := pullbackTensorSequenceGood l E f P hP.1
  have hq := pullbackTensorSequenceGood l E f Q hQ.1
  have hn := (pullbackTensorSystemComparison_existsUnique l E f).exists.choose_spec
    P Q hP.1 hQ.1
  change (pullbackTensorSequenceDerived l E f).map
      (pullbackTensorSystemModel l E Y P Q hP.1 hQ.1).hom ≫
    (pullbackTensorSystemComparison l E f).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
    TX.map (Prod.mkHom
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app P)
      ((pullbackTensorSequenceInverse l E f).mapDerivedCategoryFactors.hom.app Q)) = _ at hn
  have ht : (pullbackTensorSystemModel l E X (F.obj P) (F.obj Q) hp hq).hom ≫
        TX.map (Prod.mkHom (DerivedCategory.Q.map ((pullBridge l E f).hom.app P))
          (DerivedCategory.Q.map ((pullBridge l E f).hom.app Q))) =
      DerivedCategory.Q.map (U.map (Prod.mkHom (b.hom.app P) (b.hom.app Q))) ≫
        (pullbackTensorSystemModel l E X _ _ hfP.1 hfQ.1).hom := by
    exact ((pullbackTensorCalculus l E X).systemTensorModel.comparison.hom.naturality
      (Prod.mkHom
        (ObjectProperty.homMk (X := ⟨F.obj P, hp⟩)
          (Y := ⟨(IntegralCoherence.pull l E f).obj P, hfP.1⟩) (b.hom.app P))
        (ObjectProperty.homMk (X := ⟨F.obj Q, hq⟩)
          (Y := ⟨(IntegralCoherence.pull l E f).obj Q, hfQ.1⟩) (b.hom.app Q)))).symm
  simp only [strictPullModel_hom, comparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Iso.app_inv]
  exact tensor_square_paste DerivedCategory.Q TX U _ _ _ _ _ _ _ _
    (b.app (StrictQuotient.total l E P Q)) (b.app P) (b.app Q) hn ht

private theorem tensor_reduction {W : Scheme.{u}}
    {K H : DerivedCategory (scalarReductionSource l E W)}
    (A B : StrictQuotient.Complex l E W)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (βA : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A))
    (βB : H ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj B)) :
    reduction l E (tensorSubstitution l E A B hA hB βA βB) =
      (pullbackTensorCalculus l E W).reduction.map
        ((pullbackTensorIntegralTensorModel l E W).hom.app (K,H)) ≫
      (pullbackTensorCalculus l E W).adjunction.counit.app
        ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
          ((pullbackTensorCalculus l E W).reduction.obj K,
            (pullbackTensorCalculus l E W).reduction.obj H)) ≫
      (pullbackTensorCalculus l E W).systemClosed.tensor.map
        (Prod.mkHom (reduction l E βA) (reduction l E βB)) ≫
      (pullbackTensorSystemModel l E W A B hA.1 hB.1).inv := by
  let R := (pullbackTensorCalculus l E W).reduction
  let L := coefficientSequenceLimit l E W
  let v := (pullbackTensorCalculus l E W).systemClosed.tensor.map
      (Prod.mkHom (reduction l E βA) (reduction l E βB)) ≫
    (pullbackTensorSystemModel l E W A B hA.1 hB.1).inv
  have hn := (pullbackTensorCalculus l E W).adjunction.counit.naturality v
  conv_lhs => unfold reduction tensorSubstitution
  change R.map ((pullbackTensorIntegralTensorModel l E W).hom.app (K,H) ≫
      L.map _ ≫ L.map _) ≫ _ = _
  rw [R.map_comp]
  simp only [Category.assoc]
  apply congrArg (R.map ((pullbackTensorIntegralTensorModel l E W).hom.app (K,H)) ≫ ·)
  simpa only [v, Functor.comp_map, Functor.id_map, ← L.map_comp] using hn

private theorem pull_reduction {V W : Scheme.{u}} (g : V ⟶ W)
    {K : DerivedCategory (scalarReductionSource l E W)}
    (A : StrictQuotient.Complex l E W)
    (β : K ⟶ (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj A)) :
    reduction l E (pullSubstitution l E g A β) =
      (pullbackTensorCalculus l E V).reduction.map
        ((pullbackTensorIntegralPullbackModel l E g).hom.app K) ≫
      (pullbackTensorCalculus l E V).adjunction.counit.app
        ((pullbackTensorSequenceDerived l E g).obj
          ((pullbackTensorCalculus l E W).reduction.obj K)) ≫
      (pullbackTensorSequenceDerived l E g).map (reduction l E β) ≫
      (strictPullModel l E g).hom.app A := by
  let R := (pullbackTensorCalculus l E V).reduction
  let L := coefficientSequenceLimit l E V
  let v := (pullbackTensorSequenceDerived l E g).map (reduction l E β) ≫
    (strictPullModel l E g).hom.app A
  have hn := (pullbackTensorCalculus l E V).adjunction.counit.naturality v
  conv_lhs => unfold reduction pullSubstitution
  change R.map ((pullbackTensorIntegralPullbackModel l E g).hom.app K ≫
      L.map _ ≫ L.map _) ≫ _ = _
  rw [R.map_comp]
  simp only [Category.assoc]
  apply congrArg (R.map ((pullbackTensorIntegralPullbackModel l E g).hom.app K) ≫ ·)
  simpa only [v, strictPullModel_hom, Functor.comp_map, Functor.id_map,
    ← L.map_comp, R, L, pullbackTensorReferencePullback, Functor.comp_obj] using hn

-- Keep counit cancellation explicit across the derived operation models.
/-- Source: Stacks 07A4, 0941; the integral comparison counit construction.
(blueprint: lem-pur-completed-comparison-canonical-square).
Proof: use the K-flat normalization equation for the system comparison, followed
by tensor-model naturality across the sequence pullback bridge. Counit naturality
computes reduction of each tensor and pullback substitution. Insert these formulas
into the defining canonical comparison; the effective counits and the primitive
realization isomorphisms cancel. The remaining equality is naturality of the
system comparison at the two arbitrary reduction maps. -/
theorem completedComparisonCanonicalSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y)
    (A B : StrictQuotient.Complex l E Y)
    (hA : StrictQuotient.SystemGood l E A) (hB : StrictQuotient.SystemGood l E B)
    (hfA : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f A))
    (hfB : StrictQuotient.SystemGood l E (StrictQuotient.pull l E f B))
    (βA : M.obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj A))
    (βB : N.obj ⟶ (coefficientSequenceLimit l E Y).obj (DerivedCategory.Q.obj B)) :
    pullSubstitution l E f (StrictQuotient.total l E A B)
        (tensorSubstitution l E A B hA hB βA βB) ≫
      (coefficientSequenceLimit l E X).map
        (DerivedCategory.Q.map (comparison l E f A B).hom) =
    (canonicalIntegralPullbackTensor l E f M N).hom.hom ≫
      tensorSubstitution l E (StrictQuotient.pull l E f A) (StrictQuotient.pull l E f B)
        hfA hfB (pullSubstitution l E f A βA) (pullSubstitution l E f B βB) := by
  let F := pullbackTensorSequenceDerived l E f
  let T := (pullbackTensorCalculus l E X).systemClosed.tensor
  let C := pullbackTensorSystemComparison l E f
  let a := reduction l E βA
  let b := reduction l E βB
  let p := (strictPullModel l E f).hom.app A
  let q := (strictPullModel l E f).hom.app B
  let sy := pullbackTensorSystemModel l E Y A B hA.1 hB.1
  let sx := pullbackTensorSystemModel l E X _ _ hfA.1 hfB.1
  have hs : F.map sy.inv ≫ (strictPullModel l E f).hom.app
        (StrictQuotient.total l E A B) ≫
        DerivedCategory.Q.map (comparison l E f A B).hom =
      C.hom.app (DerivedCategory.Q.obj A, DerivedCategory.Q.obj B) ≫
        T.map (Prod.mkHom p q) ≫ sx.inv := by
    exact inverse_square_paste F sy sx _ _ _ _
      (strict_system_square l E f A B hA hB hfA hfB)
  have hn := C.hom.naturality (Prod.mkHom a b)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [pullSubstitution, tensor_reduction]
  unfold tensorSubstitution
  rw [pull_reduction, pull_reduction]
  simp only [canonicalIntegralPullbackTensor, pullbackTensorReferenceComparison,
    ObjectProperty.isoMk, ObjectProperty.homMk, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.prod_hom, asIso_hom, asIso_inv,
    Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv,
    ObjectProperty.ι_obj, constructibleIntegralPullback, Functor.comp_obj,
    pullbackTensorReferencePullback, pullbackTensorReferenceTensor, Functor.prod_map,
    Functor.comp_map, ObjectProperty.lift_obj_obj, Iso.inv_hom_id_app_assoc]
  let LX := coefficientSequenceLimit l E X
  let RX := (pullbackTensorCalculus l E X).reduction
  let am := (pullbackTensorIntegralPullbackModel l E f).app M.obj
  let an := (pullbackTensorIntegralPullbackModel l E f).app N.obj
  let em := (pullbackTensorCalculus l E X).adjunction.counit.app (F.obj
    ((pullbackTensorCalculus l E Y).reduction.obj M.obj))
  let en := (pullbackTensorCalculus l E X).adjunction.counit.app (F.obj
    ((pullbackTensorCalculus l E Y).reduction.obj N.obj))
  let := (pullbackTensorComparisonCounits l E f M N).2.1
  let := (pullbackTensorComparisonCounits l E f M N).2.2
  have ht : T.map (Prod.mkHom (inv em) (inv en)) ≫
      T.map (Prod.mkHom (RX.map am.inv) (RX.map an.inv)) ≫
      T.map (Prod.mkHom (RX.map am.hom ≫ em ≫ F.map a ≫ p)
        (RX.map an.hom ≫ en ≫ F.map b ≫ q)) =
      T.map (Prod.mkHom (F.map a ≫ p) (F.map b ≫ q)) := by
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    ext <;> simp only [prod_comp, Prod.mkHom,
      ← RX.map_comp_assoc, Iso.inv_hom_id, RX.map_id, Category.id_comp,
      IsIso.inv_hom_id_assoc]
  have hs' := hs
  simp only [strictPullModel_hom, Category.assoc, ← DerivedCategory.Q.map_comp] at hs'
  have ht' := congrArg (· ≫ sx.inv) ht
  simp only [Category.assoc] at ht'
  have hn' := congrArg (· ≫ T.map (Prod.mkHom p q) ≫ sx.inv) hn
  simp only [Category.assoc] at hn'
  simp only [← Functor.map_comp]
  rw [hs']
  erw [ht']
  rw [hn']
  have htensor : T.map (Prod.mkHom (F.map a) (F.map b)) ≫
      T.map (Prod.mkHom p q) =
      T.map (Prod.mkHom (F.map a ≫ p) (F.map b ≫ q)) :=
    (T.map_comp _ _).symm
  dsimp only [T, F] at htensor
  have htensor' := congrArg (· ≫ sx.inv) htensor
  simp only [Category.assoc] at htensor'
  erw [htensor']

end WeilConjectures.CompletedQuotient
