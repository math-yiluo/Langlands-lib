/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels

import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Proved calculations for tensor-shift path normalization

Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-naturality-t5).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.integralCompletedTensor WeilConjectures.sfIntegralConstructible
  WeilConjectures.podReindexCalculus

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodTensorShiftNormalization

attribute [local irreducible] integralOperationsTensorTowerFunctor
attribute [local implicit_reducible] podShiftTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The projection-defined product shift is natural. Test each product projection.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-naturality-t5). -/
private theorem product_shift_naturality
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ C') (r : ℤ) :
    Limits.Pi.map (fun n : ℕ ↦ (f.app (op n))⟦r⟧') ≫ podShiftProduct C' r =
      podShiftProduct C r ≫ (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)))⟦r⟧' := by
  apply (cancel_mono (piComparison (shiftFunctor (CochainComplex A ℤ) r)
    (fun n : ℕ ↦ C'.obj (op n)))).mp
  apply Limits.Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  change _ ≫ inv (piComparison _ _) ≫ _ = inv (piComparison _ _) ≫ _ ≫ _
  rw [inv_piComparison_comp_map_π, Limits.Pi.map_π]
  rw [← Functor.map_comp, Limits.Pi.map_π, Functor.map_comp]
  rw [← Category.assoc, inv_piComparison_comp_map_π]

private theorem two_coordinate_ext
    {A : Type*} [Category A] [Preadditive A] {U V B C : A}
    (p : V ⟶ B) (q : V ⟶ C) (x : B ⟶ V) (y : C ⟶ V)
    (h : p ≫ x + q ≫ y = 𝟙 V) {f g : U ⟶ V}
    (hf : f ≫ p = g ≫ p) (hg : f ≫ q = g ≫ q) : f = g := by
  calc
    f = f ≫ (p ≫ x + q ≫ y) := by rw [h, Category.comp_id]
    _ = (f ≫ p) ≫ x + (f ≫ q) ≫ y := by
      simp only [Preadditive.comp_add, Category.assoc]
    _ = (g ≫ p) ≫ x + (g ≫ q) ≫ y := by rw [hf, hg]
    _ = g ≫ (p ≫ x + q ≫ y) := by
      simp only [Preadditive.comp_add, Category.assoc]
    _ = g := by rw [h, Category.comp_id]

section RoosNaturality
attribute [local implicit_reducible] integralOperationsRoos

/-- The signed Roos shift is natural. Use product naturality in both cocone coordinates,
with the same sign in the second coordinate, then the cocone coordinate identity.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-naturality-t5). -/
theorem signed_roos_naturality
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (S : PodSignedRoosShift A) (hS : S.Laws)
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (f : C ⟶ C') (r : ℤ) :
    integralOperationsRoosMap (whiskerRight f (shiftFunctor _ r)) ≫
        (S.comparison C' r).hom =
      (S.comparison C r).hom ≫ (integralOperationsRoosMap f)⟦r⟧' := by
  let fs := whiskerRight f (shiftFunctor _ r)
  let L := integralOperationsRoosMap fs ≫ (S.comparison C' r).hom
  let R := (S.comparison C r).hom ≫ (integralOperationsRoosMap f)⟦r⟧'
  have hp := product_shift_naturality f r
  have hf : L ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C'))⟦r⟧' =
      R ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C'))⟦r⟧' := by
    dsimp only [L, R]
    simp only [Category.assoc]
    erw [hS.1 C' r]
    erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates fs).1, Category.assoc]
    change _ ≫ (Limits.Pi.map (fun n : ℕ ↦ (f.app (op n))⟦r⟧') ≫ _) = _
    erw [hp, ← Category.assoc, ← hS.1 C r]
    simp only [Category.assoc, ← Functor.map_comp]
    erw [(IntegralAmbient.roosMap_coordinates f).1]
  have hs (i : ℤ) : L.f i ≫
      (CochainComplex.mappingCocone.snd (podRoosBoundary C')).v
        (i + r) (i - 1 + r) (by omega) =
      R.f i ≫ (CochainComplex.mappingCocone.snd (podRoosBoundary C')).v
        (i + r) (i - 1 + r) (by omega) := by
    have hpi := congrArg (fun a ↦ a.f (i - 1)) hp
    simp only [HomologicalComplex.comp_f] at hpi
    dsimp only [L, R]
    simp only [HomologicalComplex.comp_f]
    erw [Category.assoc, Category.assoc, hS.2 C' r i, Linear.comp_units_smul]
    erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates fs).2 i (i - 1)
      (by omega), Category.assoc]
    change r.negOnePow • (_ ≫
      ((Limits.Pi.map (fun n : ℕ ↦ (f.app (op n))⟦r⟧')).f (i - 1) ≫ _)) = _
    erw [hpi, ← Category.assoc, ← Linear.units_smul_comp, ← hS.2 C r i]
    simp only [CochainComplex.shiftFunctor_map_f']
    erw [(IntegralAmbient.roosMap_coordinates f).2 (i + r) (i - 1 + r) (by omega)]
    erw [Category.assoc]
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun a ↦ a.f i) hf
  have hid := CochainComplex.mappingCocone.id_X (podRoosBoundary C')
    (i + r) (i - 1 + r) (by omega)
  have hfi' : L.f i ≫
      (CochainComplex.mappingCocone.fst (podRoosBoundary C')).f (i + r) =
      R.f i ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C')).f (i + r) := by
    exact hfi
  exact two_coordinate_ext _ _ _ _ hid hfi' (hs i)

end RoosNaturality
attribute [local irreducible] integralOperationsRoos

/-- Reindexing a compatible shifted presentation gives the canonical target presentation.
Cancel the target shift identification and use naturality and CommShift of the comparison.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 011G, 07A4, 0941
(blueprint: lem-pod-tensor-shift-naturality-t5). -/
theorem reindexed_shift_presentation
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (QY : A ⥤ B) (QX : C ⥤ D) (H : A ⥤ C) (F : B ⥤ D)
    [QY.CommShift ℤ] [QX.CommShift ℤ] [H.CommShift ℤ] [F.CommShift ℤ]
    (φ : QY ⋙ F ≅ H ⋙ QX) [NatTrans.CommShift φ.inv ℤ]
    (U : A) {M M' : B} (r : ℤ)
    (e : QY.obj U ≅ M) (e' : QY.obj (U⟦r⟧) ≅ M') (a : M' ≅ M⟦r⟧)
    (ha : e'.hom ≫ a.hom = (QY.commShiftIso r).hom.app U ≫ e.hom⟦r⟧') :
    let eX := φ.symm.app U ≪≫ F.mapIso e
    let aX := F.mapIso a ≪≫ (F.commShiftIso r).app M
    let eX' := (QX.commShiftIso r).app (H.obj U) ≪≫
      (shiftFunctor _ r).mapIso eX ≪≫ aX.symm
    φ.inv.app (U⟦r⟧) ≫ F.map e'.hom =
      QX.map ((H.commShiftIso r).hom.app U) ≫ eX'.hom := by
  dsimp only
  apply (cancel_mono (F.map a.hom ≫ (F.commShiftIso r).hom.app M)).mp
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc,
    ← F.map_comp_assoc, Iso.inv_hom_id, F.map_id,
    Category.id_comp]
  rw [ha, F.map_comp, Category.assoc, F.commShiftIso_hom_naturality]
  have h := NatTrans.shift_app_comm φ.inv r U
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  simp only [Iso.inv_hom_id_app, Category.comp_id, Functor.comp_obj]
  simpa only [Functor.map_comp, Category.assoc, Functor.comp_obj]
    using congrArg (fun k ↦ k ≫ (F.map e.hom)⟦r⟧') h.symm

end WeilConjectures.PodTensorShiftNormalization
