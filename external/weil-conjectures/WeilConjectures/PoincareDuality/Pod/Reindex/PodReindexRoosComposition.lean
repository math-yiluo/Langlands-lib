/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodReindexFamily.PodCompletionReindexCoherence
import Mathlib.Tactic.CategoryTheory.Slice
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Composition of normalized Roos reindexing comparisons

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 07A4 and 0941 (blueprint: lem-pod-reindex-roos-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
-- Preserve sharing of the dependent functor and representative aliases.
set_option cleanup.letToHave false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
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
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard integralCompletedTensor
  completedIntegralCoefficientSheafUnrestricted Scheme.residueField
  sfIntegralConstructible podReindexCalculus isoReductionCompletedMap
  integralOperationsTensorTowerFunctor
  integralCompletedTensorComparison
attribute [local implicit_reducible] podGoodReindex
  integralOperationsTensorComplexFunctor

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section RoosCoordinates
attribute [local implicit_reducible] integralOperationsRoos

private theorem roos_hom_ext
    {C : Type*} [Category C] [Abelian C] [HasCountableProducts C]
    {T : ℕᵒᵖ ⥤ CochainComplex C ℤ} {K : CochainComplex C ℤ}
    {a b : K ⟶ integralOperationsRoos T}
    (hf : a ≫ CochainComplex.mappingCocone.fst (podRoosBoundary T) =
      b ≫ CochainComplex.mappingCocone.fst (podRoosBoundary T))
    (hs : ∀ i : ℤ, a.f i ≫ (CochainComplex.mappingCocone.snd (podRoosBoundary T)).v
        i (i - 1) (by omega) =
      b.f i ≫ (CochainComplex.mappingCocone.snd (podRoosBoundary T)).v
        i (i - 1) (by omega)) : a = b := by
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun z ↦ z.f i) hf
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X (podRoosBoundary T)
    i (i - 1) (by omega)
  have hl := congrArg (fun z ↦ a.f i ≫ z) hid
  have hr := congrArg (fun z ↦ b.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hl hr
  rw [hfi, hs i] at hl
  exact (Category.comp_id _).symm.trans
    (hl.symm.trans (hr.trans (Category.comp_id _)))

private theorem roos_composition
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Abelian C₀] [Abelian C₁] [Abelian C₂]
    [HasCountableProducts C₀] [HasCountableProducts C₁] [HasCountableProducts C₂]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    [F.Additive] [G.Additive] [H.Additive] (a : H ≅ F ⋙ G)
    (C : ℕᵒᵖ ⥤ CochainComplex C₀ ℤ)
    (rF : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ)))
    (rG : (G.mapHomologicalComplex (.up ℤ)).obj
        (integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ))) ⟶
      integralOperationsRoos ((C ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙
        G.mapHomologicalComplex (.up ℤ)))
    (rH : (H.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ H.mapHomologicalComplex (.up ℤ)))
    (hfF : rF ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫
          piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)))
    (hsF : ∀ i : ℤ, rF.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i (i - 1) (by omega) =
      F.map ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
        i (i - 1) (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n))).f (i - 1))
    (hfG : rG ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary ((C ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙
          G.mapHomologicalComplex (.up ℤ))) =
      (G.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst
          (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))) ≫
        piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n)))
    (hsG : ∀ i : ℤ, rG.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary ((C ⋙ F.mapHomologicalComplex (.up ℤ)) ⋙
          G.mapHomologicalComplex (.up ℤ)))).v i (i - 1) (by omega) =
      G.map ((CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v
          i (i - 1) (by omega)) ≫
        (piComparison (G.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ (C ⋙ F.mapHomologicalComplex (.up ℤ)).obj (op n))).f (i - 1))
    (hfH : rH ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary (C ⋙ H.mapHomologicalComplex (.up ℤ))) =
      (H.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫
          piComparison (H.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)))
    (hsH : ∀ i : ℤ, rH.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ H.mapHomologicalComplex (.up ℤ)))).v i (i - 1) (by omega) =
      H.map ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
        i (i - 1) (by omega)) ≫
        (piComparison (H.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n))).f (i - 1)) :
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm
    α.hom.app (integralOperationsRoos C) ≫
        (G.mapHomologicalComplex (.up ℤ)).map rF ≫ rG =
      rH ≫ integralOperationsRoosMap (whiskerLeft C α.hom) := by
  dsimp only
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let HC := H.mapHomologicalComplex (.up ℤ)
  let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).symm
  let τ := whiskerLeft C α.hom
  let pcF := piComparison FC (fun n : ℕ ↦ C.obj (op n))
  let pcG := piComparison GC (fun n : ℕ ↦ FC.obj (C.obj (op n)))
  let pcH := piComparison HC (fun n : ℕ ↦ C.obj (op n))
  let t := CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ τ.app (op n))
  have hp : α.hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ≫ GC.map pcF ≫ pcG = pcH ≫ t := by
    apply Pi.hom_ext
    intro n
    calc
      _ = α.hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ≫
          GC.map (FC.map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)) := by
        simp only [Category.assoc]
        slice_lhs 3 4 => exact piComparison_comp_π GC _ n
        slice_lhs 2 3 => rw [← GC.map_comp, piComparison_comp_π FC _ n]
      _ = HC.map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n) ≫
          α.hom.app (C.obj (op n)) :=
        (α.hom.naturality (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)).symm
      _ = _ := by
        change _ = (pcH ≫ CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ τ.app (op n))) ≫ _
        erw [Category.assoc, CategoryTheory.Limits.Pi.map_π]
        change HC.map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n) ≫
          α.hom.app (C.obj (op n)) =
          pcH ≫ Pi.π (fun n : ℕ ↦ HC.obj (C.obj (op n))) n ≫ α.hom.app (C.obj (op n))
        slice_rhs 1 2 => exact piComparison_comp_π HC _ n
  have hα (K : CochainComplex C₀ ℤ) (i : ℤ) :
      (α.hom.app K).f i = a.hom.app (K.X i) := by
    change a.hom.app (K.X i) ≫ 𝟙 _ = _
    exact Category.comp_id _
  obtain ⟨htf, hts⟩ := IntegralAmbient.roosMap_coordinates τ
  apply roos_hom_ext
  · simp only [Category.assoc]
    rw [hfG]
    slice_lhs 2 3 => rw [← GC.map_comp, hfF, GC.map_comp]
    simp only [Category.assoc]
    slice_lhs 1 2 => exact (α.hom.naturality _).symm
    simp only [Category.assoc]
    change HC.map (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫
      α.hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ≫ GC.map pcF ≫ pcG =
      rH ≫ integralOperationsRoosMap τ ≫ _
    rw [hp]
    erw [htf]
    simp only [← Category.assoc]
    rw [hfH]
  · intro i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [hsG i]
    change (α.hom.app _).f i ≫ G.map (rF.f i) ≫
      G.map ((CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ FC))).v i (i - 1) (by omega)) ≫ pcG.f (i - 1) = _
    slice_lhs 2 3 => rw [← G.map_comp, hsF i, G.map_comp]
    simp only [Category.assoc]
    rw [hα]
    slice_lhs 1 2 => exact (a.hom.naturality _).symm
    simp only [Category.assoc]
    have hpi := congrArg (fun z ↦ z.f (i - 1)) hp
    change (α.hom.app _).f (i - 1) ≫ G.map (pcF.f (i - 1)) ≫ pcG.f (i - 1) =
      pcH.f (i - 1) ≫ t.f (i - 1) at hpi
    rw [← hα (∏ᶜ fun n : ℕ ↦ C.obj (op n)) (i - 1)]
    rw [hpi]
    erw [hts i (i - 1) (by omega)]
    simp only [← Category.assoc]
    erw [hsH i]

end RoosCoordinates

attribute [local irreducible] integralOperationsRoos isoSectionwiseModuleInverseImage
attribute [local implicit_reducible] podReindexProduct integralOperationsRoosFunctor

/-- The normalized Roos reindexing comparisons compose on an arbitrary strict tower.
Source: blueprint Steps 1 and 5; Stacks 07A4, 0941
(blueprint: lem-pod-reindex-roos-composition).
Proof: apply all product projections and naturality of the ordinary compositor.
The composite product comparison is the single product comparison followed by
the product of compositor components. The RoosFst and RoosSnd formulas identify
both coordinates of the corresponding cone maps. The mapping-cocone identity
decomposition detects the full chain map, including the shifted coordinate.
No tensor or localization is involved. -/
theorem podReindexRoosComposition
    (A : PodReindexFamily l E)
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (f : W ⟶ V) [IsIso h] [IsIso f]
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (hf : PodCompletionReindex.Laws l E f (A.completion f))
    (hh : PodCompletionReindex.Laws l E h (A.completion h))
    (hhf : PodCompletionReindex.Laws l E (h ≫ f) (A.completion (h ≫ f)))
    (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E V) ℤ) :
    let α := NatIso.mapHomologicalComplex (A.composition h f) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (isoReductionIntegralInverse l E f ⋙ isoReductionIntegralInverse l E h))
        (.up ℤ)).symm
    α.hom.app (integralOperationsRoos C) ≫
      (isoReductionIntegralComplex l E h).map ((A.completion f).roos C).hom ≫
      ((A.completion h).roos ((podReindexTower l E f).obj C)).hom =
    ((A.completion (h ≫ f)).roos C).hom ≫
      integralOperationsRoosFunctor.map (whiskerLeft C α.hom) := by
  intro α
  exact roos_composition (isoReductionIntegralInverse l E f)
    (isoReductionIntegralInverse l E h) (isoReductionIntegralInverse l E (h ≫ f))
    (A.composition h f) C ((A.completion f).roos C).hom
    ((A.completion h).roos ((podReindexTower l E f).obj C)).hom
    ((A.completion (h ≫ f)).roos C).hom
    (hf.2.2.2.2.2.2.2.2.2.2.1 _) (hf.2.2.2.2.2.2.2.2.2.2.2.1 _)
    (hh.2.2.2.2.2.2.2.2.2.2.1 _) (hh.2.2.2.2.2.2.2.2.2.2.2.1 _)
    (hhf.2.2.2.2.2.2.2.2.2.2.1 _) (hhf.2.2.2.2.2.2.2.2.2.2.2.1 _)

end WeilConjectures
