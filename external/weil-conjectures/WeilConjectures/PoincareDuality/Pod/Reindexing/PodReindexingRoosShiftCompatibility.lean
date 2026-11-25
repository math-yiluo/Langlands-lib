/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # The diagonal Roos map respects signed shifts

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4, 0941 (blueprint: lem-pod-reindexing-roos-shift-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]

private def genericTowerShift
    {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type*} [Category* B] [Abelian B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    podShiftTower C r ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      podShiftTower (C ⋙ F.mapHomologicalComplex (.up ℤ)) r :=
  Functor.associator C _ _ ≪≫
    isoWhiskerLeft C ((F.mapHomologicalComplex (.up ℤ)).commShiftIso r) ≪≫
      (Functor.associator C _ _).symm

private theorem genericProduct_shift
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    let G := F.mapHomologicalComplex (.up ℤ)
    let σ := shiftFunctor (CochainComplex B ℤ) r
    piComparison G (fun n : ℕ ↦ (C.obj (op n))⟦r⟧) ≫
      CategoryTheory.Limits.Pi.map
        (fun n : ℕ ↦ (G.commShiftIso r).hom.app (C.obj (op n))) ≫
        inv (piComparison σ (fun n : ℕ ↦ G.obj (C.obj (op n)))) =
    G.map (podShiftProduct C r) ≫
      (G.commShiftIso r).hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ≫
        σ.map (piComparison G (fun n : ℕ ↦ C.obj (op n))) := by
  dsimp only
  let G := F.mapHomologicalComplex (.up ℤ)
  let σ := shiftFunctor (CochainComplex B ℤ) r
  change piComparison G _ ≫ _ ≫ inv (piComparison σ _) =
    G.map _ ≫ (G.commShiftIso r).hom.app _ ≫ σ.map _
  apply (cancel_mono (piComparison σ (fun n : ℕ ↦ G.obj (C.obj (op n))))).mp
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, piComparison_comp_π]
  rw [← σ.map_comp, piComparison_comp_π]
  rw [← G.commShiftIso_hom_naturality]
  change _ = G.map (podShiftProduct C r) ≫ G.map _ ≫ _
  rw [← G.map_comp_assoc]
  simp only [podShiftProduct, inv_piComparison_comp_map_π]
  dsimp only [G, σ]
  rw [inv_piComparison_comp_map_π]
  erw [Pi.map_π, piComparison_comp_π_assoc]

private theorem genericRoosSnd
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (i j : ℤ) (h : i + -1 = j) :
    (scalarRoosMap F C).f i ≫
      (CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v i j h =
    F.map ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v i j h) ≫
      (piComparison (F.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ C.obj (op n))).f j := by
  have hj : j = i - 1 := by omega
  cases hj
  exact (podReindexingRoosCoordinates F C).2 i

private theorem genericRoosShift
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type*} [Category* B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive]
    (SY : PodSignedRoosShift A) (SX : PodSignedRoosShift B)
    (hSY : SY.Laws) (hSX : SX.Laws)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (r : ℤ) :
    (scalarRoosMap F (podShiftTower C r) ≫
      integralOperationsRoosMap (genericTowerShift F C r).hom ≫
      (SX.comparison (C ⋙ F.mapHomologicalComplex (.up ℤ)) r).hom) =
    ((F.mapHomologicalComplex (.up ℤ)).map (SY.comparison C r).hom ≫
      ((F.mapHomologicalComplex (.up ℤ)).commShiftIso r).hom.app
        (integralOperationsRoos C) ≫ (scalarRoosMap F C)⟦r⟧') := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let C' := C ⋙ G
  let a := (genericTowerShift F C r).hom
  let α := scalarRoosMap F (podShiftTower C r)
  let β := scalarRoosMap F C
  let L := α ≫ integralOperationsRoosMap a ≫ (SX.comparison C' r).hom
  let R := G.map (SY.comparison C r).hom ≫
    (G.commShiftIso r).hom.app (integralOperationsRoos C) ≫ β⟦r⟧'
  have ha (n : ℕ) : a.app (op n) = (G.commShiftIso r).hom.app (C.obj (op n)) := by
    change (𝟙 _ ≫ _ ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  have hp := genericProduct_shift F C r
  have hf : L ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C'))⟦r⟧' =
      R ≫ (CochainComplex.mappingCocone.fst (podRoosBoundary C'))⟦r⟧' := by
    dsimp only [L, R, α, β]
    simp only [Category.assoc]
    have hx := hSX.1 C' r
    dsimp only [podShiftTower, Functor.comp_obj] at hx
    erw [hx]
    dsimp only [podShiftTower, Functor.comp_obj, C']
    erw [reassoc_of% (IntegralAmbient.roosMap_coordinates a).1]
    erw [reassoc_of% (podReindexingRoosCoordinates F (podShiftTower C r)).1]
    simp only [ha]
    dsimp only [podShiftTower, Functor.comp_obj, podShiftProduct, G]
    change G.map _ ≫ (piComparison G _ ≫ _ ≫ _) = _
    rw [hp, ← Category.assoc, ← G.map_comp]
    erw [← hSY.1 C r]
    rw [G.map_comp]
    simp only [Category.assoc]
    erw [G.commShiftIso_hom_naturality_assoc]
    rw [← Functor.map_comp, ← (podReindexingRoosCoordinates F C).1,
      Functor.map_comp]
  have hs (i : ℤ) : L.f i ≫
      (CochainComplex.mappingCocone.snd (podRoosBoundary C')).v
        (i + r) (i - 1 + r) (by omega) =
    R.f i ≫ (CochainComplex.mappingCocone.snd (podRoosBoundary C')).v
        (i + r) (i - 1 + r) (by omega) := by
    have hpi := congrArg (fun f ↦ f.f (i - 1)) hp
    simp only [HomologicalComplex.comp_f] at hpi
    dsimp only [L, R, α, β]
    simp only [HomologicalComplex.comp_f, Category.assoc]
    have hx := hSX.2 C' r i
    dsimp only [podShiftTower, Functor.comp_obj] at hx
    erw [hx]
    simp only [Linear.comp_units_smul]
    dsimp only [podShiftTower, Functor.comp_obj, C']
    erw [reassoc_of% (IntegralAmbient.roosMap_coordinates a).2 i (i - 1) (by omega)]
    erw [reassoc_of% (podReindexingRoosCoordinates F (podShiftTower C r)).2 i]
    simp only [ha]
    dsimp only [podShiftTower, Functor.comp_obj, podShiftProduct, G]
    change r.negOnePow • (F.map _ ≫ _) = _
    erw [hpi]
    simp only [Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      CochainComplex.shiftFunctor_map_f']
    dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_map_f]
    erw [Category.id_comp, Category.id_comp]
    change r.negOnePow •
        (F.map ((CochainComplex.mappingCocone.snd
          (podRoosBoundary (podShiftTower C r))).v i (i - 1) (by omega)) ≫
          F.map ((podShiftProduct C r).f (i - 1)) ≫
          (piComparison G (fun n : ℕ ↦ C.obj (op n))).f (i - 1 + r)) =
      F.map ((SY.comparison C r).hom.f i) ≫ (scalarRoosMap F C).f (i + r) ≫
        (CochainComplex.mappingCocone.snd (podRoosBoundary C')).v
          (i + r) (i - 1 + r) (by omega)
    rw [← F.map_comp_assoc, ← Linear.units_smul_comp, ← F.map_units_smul]
    erw [← hSY.2 C r i]
    rw [F.map_comp, Category.assoc]
    have hc := genericRoosSnd F C (i + r) (i - 1 + r) (by omega)
    exact congrArg (F.map ((SY.comparison C r).hom.f i) ≫ ·) hc.symm
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun f ↦ f.f i) hf
  simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f'] at hfi
  have hid := CochainComplex.mappingCocone.id_X (podRoosBoundary C')
    (i + r) (i - 1 + r) (by omega)
  have hleft := congrArg (fun z ↦ L.f i ≫ z) hid
  have hright := congrArg (fun z ↦ R.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hfi, hs i] at hleft
  exact (Category.comp_id _).symm.trans
    (hleft.symm.trans (hright.trans (Category.comp_id _)))

/-- The projection-normalized diagonal Roos map commutes with the signed cocone shift.
Source: Stacks 011G, 0941, blueprint Steps 1 and 5
(blueprint: lem-pod-reindexing-roos-shift-compatibility).

Proof: compose each side with the shifted first cocone coordinate and with the
second cocone coordinate in every degree. For the first coordinate, the diagonal
Roos equations and the two prescribed shift equations reduce the assertion to
naturality of the product comparison with shift. Verify that equality after each
product projection, where the termwise shift comparison has identity components.
For the second coordinate the same calculation has the scalar (-1)^r on both
sides. Additivity transports this scalar, and the identity components of the
termwise shift comparison leave it unchanged. The two coordinates jointly
identify each component of the proposed chain maps. No boundedness is used. -/
theorem podReindexingRoosShiftCompatibility
    (SY : PodSignedRoosShift (scalarReductionSource l E Y))
    (SX : PodSignedRoosShift (scalarReductionSource l E X))
    (hSY : SY.Laws) (hSX : SX.Laws) :
    ∀ (C : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (r : ℤ),
    (scalarRoosMap (isoReductionIntegralInverse l E g) (podShiftTower C r) ≫
      integralOperationsRoosMap (podTowerShift l E g C r).hom ≫
      (SX.comparison ((podReindexTower l E g).obj C) r).hom) =
    ((isoReductionIntegralComplex l E g).map (SY.comparison C r).hom ≫
      ((isoReductionIntegralComplex l E g).commShiftIso r).hom.app
        (integralOperationsRoos C) ≫
      (scalarRoosMap (isoReductionIntegralInverse l E g) C)⟦r⟧') := by
  intro C r
  exact genericRoosShift (isoReductionIntegralInverse l E g) SY SX hSY hSX C r
end WeilConjectures
