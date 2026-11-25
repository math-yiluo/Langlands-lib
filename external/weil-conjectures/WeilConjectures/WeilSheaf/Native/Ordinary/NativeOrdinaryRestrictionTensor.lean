/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorComparisonData
public import WeilConjectures.WeilSheaf.Native.Ordinary.NativeOrdinaryClosedTensorModels
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Braided
public import WeilConjectures.WeilSheaf.Native.NativeAdicRestrictionFlat
import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Ordinary restriction for the fixed closed tensor models

Source: Stacks 0E8I and 0GL1; uniqueness of tensor--Hom adjoints.
(blueprint: lem-sf-native-ordinary-restriction-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
attribute [local irreducible]
  AlgebraicGeometry.ProEtaleWeilSheaf.nativeDerivedClosedComparison

set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] CategoryTheory.uniformProd CategoryTheory.prod'
  CategoryTheory.Prod.sectL CategoryTheory.Prod.sectR CoefficientClosedStructure.tensor

private def parameterMap {C : Type v} [Category.{w} C]
    (T : C × C ⥤ C) {K K' : C} (f : K ⟶ K') :
    Prod.sectL C K ⋙ T ⟶ Prod.sectL C K' ⋙ T where
  app A := T.map (X := (A, K)) (Y := (A, K')) (𝟙 A, f)
  naturality {A B} g := by
    change T.map (X := (A, K)) (Y := (B, K)) (g, 𝟙 K) ≫
        T.map (X := (B, K)) (Y := (B, K')) (𝟙 B, f) =
      T.map (X := (A, K)) (Y := (A, K')) (𝟙 A, f) ≫
        T.map (X := (A, K')) (Y := (B, K')) (g, 𝟙 K')
    rw [← T.map_comp, ← T.map_comp]
    congr 1
    exact Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem counit_test {C : Type v} [Category.{w} C]
    {L L' R : C ⥤ C} (b : L' ⊣ R) (x y : L ⟶ L')
    (h : ∀ N, x.app (R.obj N) ≫ b.counit.app N =
      y.app (R.obj N) ≫ b.counit.app N) : x = y := by
  ext A
  have hx : L.map (b.unit.app A) ≫ x.app (R.obj (L'.obj A)) ≫
      b.counit.app (L'.obj A) = x.app A := by
    have hn := x.naturality (b.unit.app A)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, b.left_triangle_components,
      Category.comp_id]
  have hy : L.map (b.unit.app A) ≫ y.app (R.obj (L'.obj A)) ≫
      b.counit.app (L'.obj A) = y.app A := by
    have hn := y.naturality (b.unit.app A)
    dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.id_obj] at hn
    rw [← Category.assoc, hn, Category.assoc, b.left_triangle_components,
      Category.comp_id]
  rw [← hx, ← hy, h]

private def adjointTensorIso {C : Type v} [Category.{w} C]
    (H : Cᵒᵖ × C ⥤ C) (T R : C × C ⥤ C)
    (a : ∀ K, Prod.sectL C K ⋙ T ⊣ Prod.sectR (op K) C ⋙ H)
    (b : ∀ K, Prod.sectL C K ⋙ R ⊣ Prod.sectR (op K) C ⋙ H)
    (ha : ∀ (K K' L : C) (f : K' ⟶ K),
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
        (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
        (a K').counit.app L =
      T.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
        (𝟙 _, f) ≫ (a K).counit.app L)
    (hb : ∀ (K K' L : C) (f : K' ⟶ K),
      R.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K', L), K'))
        (H.map (X := (op K, L)) (Y := (op K', L)) (f.op, 𝟙 L), 𝟙 K') ≫
        (b K').counit.app L =
      R.map (X := (H.obj (op K, L), K')) (Y := (H.obj (op K, L), K))
        (𝟙 _, f) ≫ (b K).counit.app L) : T ≅ R := by
  let e (K : C) := (a K).leftAdjointUniq (b K)
  have ecounit (K N : C) : (e K).hom.app (H.obj (op K, N)) ≫
      (b K).counit.app N = (a K).counit.app N := by
    simpa only [CategoryTheory.Functor.comp_obj, Prod.sectR_obj] using
      Adjunction.leftAdjointUniq_hom_app_counit (a K) (b K) N
  have he {K K' : C} (f : K ⟶ K') :
      parameterMap T f ≫ (e K').hom = (e K).hom ≫ parameterMap R f := by
    apply counit_test (b K')
    intro N
    dsimp only [NatTrans.comp_app, parameterMap, CategoryTheory.Functor.comp_obj, Prod.sectR_obj]
    simp only [Category.assoc]
    change T.map (X := (H.obj (op K', N), K)) (Y := (H.obj (op K', N), K'))
          (𝟙 _, f) ≫ (e K').hom.app _ ≫ (b K').counit.app N =
      (e K).hom.app _ ≫ R.map (X := (H.obj (op K', N), K))
          (Y := (H.obj (op K', N), K')) (𝟙 _, f) ≫ (b K').counit.app N
    rw [ecounit]
    rw [← hb K' K N f, ← Category.assoc]
    have hn := (e K).hom.naturality
      (H.map (X := (op K', N)) (Y := (op K, N)) (f.op, 𝟙 N))
    dsimp only [CategoryTheory.Functor.comp_map, Prod.sectL_map] at hn
    rw [← hn]
    rw [Category.assoc, ecounit]
    exact (ha K' K N f).symm
  refine NatIso.ofComponents (fun P ↦ (e P.2).app P.1) ?_
  intro P Q f
  have ht : T.map f = T.map (X := P) (Y := (Q.1, P.2)) (f.1, 𝟙 _) ≫
      T.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2) := by
    rw [← T.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm (Category.id_comp _).symm
  have hr : R.map f = R.map (X := P) (Y := (Q.1, P.2)) (f.1, 𝟙 _) ≫
      R.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2) := by
    rw [← R.map_comp]
    congr 1
    exact Prod.ext (Category.comp_id _).symm (Category.id_comp _).symm
  rw [ht, hr, Category.assoc]
  have hh := NatTrans.congr_app (he f.2) Q.1
  dsimp only [NatTrans.comp_app, parameterMap] at hh
  change T.map _ ≫ (T.map _ ≫ (e Q.2).hom.app Q.1) = _
  rw [hh, ← Category.assoc]
  have hn := (e P.2).hom.naturality f.1
  dsimp only [CategoryTheory.Functor.comp_map, Prod.sectL_map] at hn
  simpa only [Category.assoc, Iso.app_hom] using
    congrArg (fun z ↦ z ≫ R.map (X := (Q.1, P.2)) (Y := Q) (𝟙 _, f.2)) hn

/-- Identity comparison of the sliced tensor bifunctor with right tensoring.
Source: definition of tensorRight
(blueprint: lem-sf-native-ordinary-restriction-tensor). -/
def nativeOrdinaryTensorSliceIso {C : Type v} [Category.{w} C]
    (m : MonoidalCategory C) (K : C) :
    Prod.sectL C K ⋙ @MonoidalCategory.tensor C _ m ≅
      @MonoidalCategory.tensorRight C _ m K := by
  let := m
  exact NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro A B f
    change (f ⊗ₘ 𝟙 K) ≫ 𝟙 _ = 𝟙 _ ≫ (f ▷ K)
    simp only [tensorHom_id, Category.comp_id, Category.id_comp])

private def closedTensorIsoAux {C : Type v} [Category.{w} C]
    {H : Cᵒᵖ × C ⥤ C} (S T : CoefficientClosedStructure H) : S.tensor ≅ T.tensor := by
  let a (K : C) := (S.adjunction K).ofNatIsoLeft (nativeOrdinaryTensorSliceIso S.monoidal K).symm
  let b (K : C) := (T.adjunction K).ofNatIsoLeft (nativeOrdinaryTensorSliceIso T.monoidal K).symm
  have ha (K L : C) : (a K).counit.app L = (S.adjunction K).counit.app L := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  have hb (K L : C) : (b K).counit.app L = (T.adjunction K).counit.app L := by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  apply adjointTensorIso H S.tensor T.tensor a b
  · intro K K' L f
    rw [ha, ha]
    let := S.monoidal
    have hn := S.evaluation_naturality K K' L f
    dsimp only [tensorRight, tensorLeft, MonoidalCategory.curriedTensor,
      CategoryTheory.Functor.flip] at hn
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensor_obj, tensorHom_id, id_tensorHom] using hn
  · intro K K' L f
    rw [hb, hb]
    let := T.monoidal
    have hn := T.evaluation_naturality K K' L f
    dsimp only [tensorRight, tensorLeft, MonoidalCategory.curriedTensor,
      CategoryTheory.Functor.flip] at hn
    simpa only [CoefficientClosedStructure.tensor, MonoidalCategory.tensor_map,
      MonoidalCategory.tensor_obj, tensorHom_id, id_tensorHom] using hn

/-- The tensor comparison determined by uniqueness of left adjoints with fixed counit.
Source: uniqueness of tensor--Hom adjoints, Stacks 08J9
(blueprint: lem-sf-native-ordinary-restriction-tensor). -/
def nativeOrdinaryClosedTensorIso {C : Type v} [Category.{w} C]
    {H : Cᵒᵖ × C ⥤ C} (S T : CoefficientClosedStructure H) : S.tensor ≅ T.tensor :=
  NatIso.ofComponents (fun P ↦
    (((S.adjunction P.2).ofNatIsoLeft
      (nativeOrdinaryTensorSliceIso S.monoidal P.2).symm).leftAdjointUniq
      ((T.adjunction P.2).ofNatIsoLeft
        (nativeOrdinaryTensorSliceIso T.monoidal P.2).symm)).app P.1)
    (by intro P Q f; exact (closedTensorIsoAux S T).hom.naturality f)

namespace AlgebraicGeometry.ProEtaleWeilSheaf
variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]

/-- A normalization against the standard ordinary tensor, with the adjunction fixed
by the existing product-total Hom representatives. No existence witness is selected
by this definition. Source: Stacks 08J9 and the ordinary native tensor construction.
(blueprint: lem-sf-native-ordinary-restriction-tensor). -/
structure NativeOrdinaryTensorIdentification (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))] where
  standard : CoefficientClosedStructure
    (nativeDerivedClosedComparison k₀ l X).homModels.ordinaryHom
  symmetry : @SymmetricCategory _ _ standard.monoidal
  monoidal_eq : standard.monoidal = (inferInstance : MonoidalCategory
    (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)))
  models : NativeOrdinaryTensorModels l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber
    (nativeDerivedClosedComparison k₀ l X).homModels.ordinaryHom
    (nativeDerivedClosedComparison k₀ l X).homModels.ordinaryRepresentatives standard symmetry

/-- The adjunction-determined identification with the standard ordinary tensor.
Source: uniqueness of left adjoints, Stacks 08J9.
(blueprint: lem-sf-native-ordinary-restriction-tensor). -/
def NativeOrdinaryTensorIdentification.tensorIso {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (d : NativeOrdinaryTensorIdentification k₀ l X) :
    (nativeDerivedClosedComparison k₀ l X).ordinaryClosed.tensor ≅
      MonoidalCategory.tensor
        (DerivedCategory (ProEtale.AdicSheaf l (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)) :=
  nativeOrdinaryClosedTensorIso _ d.standard ≪≫
    eqToIso (congrArg (fun m ↦ @MonoidalCategory.tensor _ _ m) d.monoidal_eq)

variable {U Z : Scheme.{u}} [U.Over (Spec (CommRingCat.of k₀))]
  [Z.Over (Spec (CommRingCat.of k₀))] (j : U ⟶ Z) [IsOpenImmersion j]
  [j.IsOver (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (U ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (U ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (U ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]

/-- Restriction/tensor for the fixed ordinary models, transported from the exact
strong monoidal pullback using the adjunction-determined identifications.
Source: Stacks 0E8I, 0GL1 and 015F.
(blueprint: lem-sf-native-ordinary-restriction-tensor). -/
def nativeOrdinaryRestrictionTensor
    (dU : NativeOrdinaryTensorIdentification k₀ l U)
    (dZ : NativeOrdinaryTensorIdentification k₀ l Z) :
    (nativeDerivedClosedComparison k₀ l Z).ordinaryClosed.tensor ⋙
        (ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory ≅
      ((ProEtale.adicUpperStar l
        (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory).prod
        ((ProEtale.adicUpperStar l
          (Scheme.Hom.geometricFiberMap j
            (comp_over j (Spec (CommRingCat.of k₀))))).mapDerivedCategory) ⋙
        (nativeDerivedClosedComparison k₀ l U).ordinaryClosed.tensor := by
  let R := ProEtale.adicUpperStar l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  let G := ProEtale.upperStar (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  letI : G.Braided :=
    { toMonoidal := inferInstance
      braided X Y := Functor.LaxBraided.braided (F := G) X Y }
  letI : R.Monoidal := by
    dsimp only [R, ProEtale.adicUpperStar, Adjunction.modLeft]
    infer_instance
  letI : R.PreservesFlat := native_adic_restriction_flat l
    (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))
  letI : R.IsLeftAdjoint :=
    (ProEtale.adicUpperStarLowerStarAdjunction l
      (Scheme.Hom.geometricFiberMap j (comp_over j (Spec (CommRingCat.of k₀))))).isLeftAdjoint
  letI := R.exactClosedDerivedMonoidal
  exact Functor.isoWhiskerRight (dZ.tensorIso k₀ l) R.mapDerivedCategory ≪≫
    (Functor.Monoidal.μNatIso R.mapDerivedCategory).symm ≪≫
    Functor.isoWhiskerLeft (R.mapDerivedCategory.prod R.mapDerivedCategory)
      (dU.tensorIso k₀ l).symm

/-- The ordinary comparison can be constructed independently of the native open
presentation. Source: Stacks 0E8I and 0GL1, ordinary restriction/tensor.
(blueprint: lem-sf-native-ordinary-restriction-tensor).

Proof: apply the existing normalized ordinary closed tensor theorem to the fixed
product-total Hom representatives on each scheme. It constructs closed structures
whose monoidal structures are the standard ones. Left-adjoint uniqueness identifies
their tensors with the fixed ordinary tensors; counit naturality makes these
identifications natural in both tensor variables. Exact pullback has its canonical
strong monoidal derived structure. Transport its invertible tensorator along these
two identifications, as in nativeOrdinaryRestrictionTensor. This construction also
covers empty opens and zero complexes and uses no native open comparison. -/
theorem native_ordinary_tensor_identifications :
    Nonempty (NativeOrdinaryTensorIdentification k₀ l U) ∧
      Nonempty (NativeOrdinaryTensorIdentification k₀ l Z) := by
  constructor
  · obtain ⟨S, β, hm, hS⟩ := native_ordinary_closed_tensor_models l
      (U ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (nativeDerivedClosedComparison k₀ l U).homModels.ordinaryHom
      (nativeDerivedClosedComparison k₀ l U).homModels.ordinaryRepresentatives
    exact ⟨⟨S, β, hm, hS⟩⟩
  · obtain ⟨S, β, hm, hS⟩ := native_ordinary_closed_tensor_models l
      (Z ↘ Spec (CommRingCat.of k₀)).geometricFiber
      (nativeDerivedClosedComparison k₀ l Z).homModels.ordinaryHom
      (nativeDerivedClosedComparison k₀ l Z).homModels.ordinaryRepresentatives
    exact ⟨⟨S, β, hm, hS⟩⟩
end AlgebraicGeometry.ProEtaleWeilSheaf
