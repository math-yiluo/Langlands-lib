/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraints

/-! Uniqueness of the integral unit comparison.

Source: Stacks Project, Tag 07A4, label lemma-pullback-tensor-product; cancellation
with the tensor unitors in the integral constructible category.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-uniqueness)

Applying coherent reduction to either pair of unit equations and cancelling the
invertible comparison and unitor identifies the two candidate unit maps.
Faithfulness of coherent reduction then reflects equality of the original maps.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev integralCoherentReduction (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructibleCategory l E W ⥤ coefficientSequenceDerived l E W :=
  (sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction

private theorem counit_model_naturality_integral
    {C D T : Type*} [Category* C] [Category* D] [Category* T]
    (R : D ⥤ T) (L : T ⥤ D) (adj : R ⊣ L) (F : C ⥤ D) (H : C ⥤ T)
    (a : F ≅ H ⋙ L) {M N : C} (g : M ⟶ N) :
    R.map (F.map g) ≫ R.map (a.hom.app N) ≫ adj.counit.app (H.obj N) =
      R.map (a.hom.app M) ≫ adj.counit.app (H.obj M) ≫ H.map g := by
  rw [← R.map_comp_assoc, a.hom.naturality, R.map_comp]
  simp only [Functor.comp_map, Category.assoc]
  exact congrArg (fun k ↦ R.map (a.hom.app M) ≫ k)
    (adj.counit.naturality (H.map g))

private def integralReductionTensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ integralCoherentReduction l E W ≅
      (integralCoherentReduction l E W).prod (integralCoherentReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents
    (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
      intro MN PQ k
      dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
        Functor.mapIso_hom, asIso_hom]
      simpa only [Category.assoc, Iso.app_hom, integralCoherentReduction,
        constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
        Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
        ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
        counit_model_naturality_integral
          (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
          (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
          (((pullbackTensorCalculus l E W).reduction.prod
            (pullbackTensorCalculus l E W).reduction) ⋙
            (pullbackTensorCalculus l E W).systemClosed.tensor)
          (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

private theorem left_tensor_unit_square_integral {C : Type*} [Category* C]
    (T : C × C ⥤ C) {U V : C} (e : V ⟶ U)
    (r : ∀ M, T.obj (U, M) ⟶ M)
    (hr : ∀ {M N} (g : M ⟶ N),
      T.map (Prod.mkHom (𝟙 U) g) ≫ r N = r M ≫ g)
    {M N : C} (g : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 V) g) ≫ T.map (Prod.mkHom e (𝟙 N)) ≫ r N =
      T.map (Prod.mkHom e (𝟙 M)) ≫ r M ≫ g := by
  have h : Prod.mkHom (𝟙 V) g ≫ Prod.mkHom e (𝟙 N) =
      Prod.mkHom e (𝟙 M) ≫ Prod.mkHom (𝟙 U) g := by
    ext <;> simp
  rw [← T.map_comp_assoc, h, T.map_comp, Category.assoc, hr]

private theorem left_naturality_of_reduction_integral
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory D]
    (T : C × C ⥤ C) (R : C ⥤ D) [R.Faithful]
    (a : T ⋙ R ≅ R.prod R ⋙ MonoidalCategory.tensor D)
    (U : C) (e : R.obj U ≅ MonoidalCategoryStruct.tensorUnit D)
    (r : ∀ M, T.obj (U, M) ≅ M)
    (h : ∀ M, R.map (r M).hom = a.hom.app (U, M) ≫
      (MonoidalCategory.tensor D).map (Prod.mkHom e.hom (𝟙 _)) ≫
      (MonoidalCategoryStruct.leftUnitor (R.obj M)).hom)
    {M N : C} (g : M ⟶ N) :
    T.map (Prod.mkHom (𝟙 U) g) ≫ (r N).hom = (r M).hom ≫ g := by
  apply R.map_injective
  rw [Functor.map_comp, Functor.map_comp, h, h]
  have hn := a.hom.naturality (Prod.mkHom (𝟙 U) g)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  apply congrArg (fun z ↦ a.hom.app (U, M) ≫ z)
  rw [R.map_id]
  apply left_tensor_unit_square_integral (MonoidalCategory.tensor D) e.hom
    (fun K : D ↦ (MonoidalCategoryStruct.leftUnitor K).hom)
  intro A B k
  simpa only [MonoidalCategory.tensor_map, MonoidalCategory.id_tensorHom] using
    MonoidalCategory.leftUnitor_naturality k

private theorem integralLeftUnitor_natural
    {W : Scheme.{u}} [∀ w : W, Invertible (l : W.residueField w)]
    {M N : sfIntegralConstructibleCategory l E W} (g : M ⟶ N) :
    (constructibleIntegralTensor l E W).map (Prod.mkHom (𝟙 _) g) ≫
        (pullbackTensorIntegralLeftUnitor l E W N).hom =
      (pullbackTensorIntegralLeftUnitor l E W M).hom ≫ g := by
  have hfaith : (integralCoherentReduction l E W).Faithful := by
    have h := (integralSystemReduction_fullyFaithful l E W).2
    change (integralCoherentReduction l E W).Faithful at h
    exact h
  let S := (pullbackTensorCalculus l E W).systemClosed
  let _ := S.monoidal
  exact left_naturality_of_reduction_integral
    (constructibleIntegralTensor l E W) (integralCoherentReduction l E W)
    (integralReductionTensor l E W)
    (pullbackTensorIntegralUnit l E W) (pullbackTensorIntegralUnitReduction l E W)
    (fun K ↦ pullbackTensorIntegralLeftUnitor l E W K)
    (fun K ↦ (pullbackTensorIntegralLeftUnitor_existsUnique l E W K).exists.choose_spec) g

private theorem unitIso_unique_integral
    {C : Type*} [Category* C] (T : C × C ⥤ C) (U A : C)
    (lu : ∀ M, T.obj (U, M) ≅ M)
    (hn : ∀ {M N} (g : M ⟶ N),
      T.map (Prod.mkHom (𝟙 U) g) ≫ (lu N).hom = (lu M).hom ≫ g)
    (j k : A ≅ U)
    (h : T.map (Prod.mkHom (𝟙 A) j.hom) =
      T.map (Prod.mkHom (𝟙 A) k.hom)) : j = k := by
  have ht := congrArg (fun z ↦ T.map (Prod.mkHom j.inv (𝟙 A)) ≫ z ≫
    T.map (Prod.mkHom j.hom (𝟙 U))) h
  simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id,
    Iso.inv_hom_id] at ht
  have he := congrArg (fun z ↦ z ≫ (lu U).hom) ht
  rw [hn, hn] at he
  exact Iso.ext ((cancel_epi (lu A).hom).mp he)

/-- The two integral unit equations determine their comparison isomorphism.
Source: Stacks Project, Tag 07A4; unit cancellation after coherent reduction.
(blueprint: lem-pur-pullback-tensor-integral-unit-coherence-uniqueness)
-/
theorem canonicalIntegralPullbackTensor_unit_unique {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (ε δ : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
      ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
        (@pullbackTensorIntegralUnit l _ E _ _ _ X hX))
    (hε : ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom))
    (hδ : ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom δ.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
        ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
          (Prod.mkHom (𝟙 _) δ.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom)) :
    ε = δ := by
  let T := constructibleIntegralTensor l E X
  let UY := pullbackTensorIntegralUnit l E Y
  let UX := pullbackTensorIntegralUnit l E X
  let F := constructibleIntegralPullback l E f
  let A := F.obj UY
  have he := (hε UY).2.trans (hδ UY).2.symm
  have ht : T.map (Prod.mkHom (𝟙 A) ε.hom) =
      T.map (Prod.mkHom (𝟙 A) δ.hom) := by
    apply (cancel_mono (pullbackTensorIntegralRightUnitor l E X A).hom).mp
    apply (cancel_epi (canonicalIntegralPullbackTensor l E f UY UY).hom).mp
    exact he
  exact unitIso_unique_integral T UX A
    (fun M ↦ pullbackTensorIntegralLeftUnitor l E X M)
    (fun g ↦ integralLeftUnitor_natural l E g) ε δ ht

end WeilConjectures
