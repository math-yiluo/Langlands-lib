/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement

/-! # The coordinate-normalized additive Roos comparison

Source: Stacks 08TC and 0941.
(blueprint: def-sf-additive-roos-map).

This file retains the original additive Roos construction and its unique
coordinate characterization, together with proved naturality and strict tower
assembly helpers. No coefficient-specific definitions or instances are needed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe a b a' b'
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

/-- The boundary of the actual Roos cocone, for use in both coordinate formulas.
Source: Stacks 08TC (blueprint: def-sf-additive-roos-map). -/
abbrev scalarRoosBoundary {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :=
  towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
    (integralOperationsTowerStep C)

section ScalarRoos

open CochainComplex CochainComplex.HomComplex

private theorem scalarCocone_relation
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    δ (-1) 0 (mappingCocone.snd φ) + Cochain.ofHom (mappingCocone.fst φ ≫ φ) = 0 := by
  dsimp only [mappingCocone.snd]
  erw [Cochain.δ_leftShift (mappingCone.snd φ) (-1) (-1) 0 rfl 1 rfl]
  rw [mappingCone.δ_snd]
  dsimp only [mappingCocone.fst]
  simp only [Int.reduceNeg, Int.negOnePow_neg, Int.negOnePow_one, Cochain.leftShift_neg,
    Cochain.leftShift_comp_zero_cochain, smul_neg, Units.neg_smul, one_smul, neg_neg]
  erw [Preadditive.neg_comp, Cochain.ofHom_neg, Cochain.ofHom_comp,
    Cocycle.cochain_ofHom_homOf_eq_coe]
  dsimp only [Cocycle.leftShift]
  with_unfolding_all exact (add_neg_cancel _)

private def scalarAdditiveCoconeMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {B : Type a'} [Category.{b'} B] [Abelian B]
    (F : A ⥤ B) [F.Additive] {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (mappingCocone φ) ⟶
      mappingCocone ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  refine mappingCocone.lift (G.map φ) (G.map (mappingCocone.fst φ))
    ((mappingCocone.snd φ).map F) ?_
  have h := congrArg (fun z ↦ z.map F) (scalarCocone_relation φ)
  simpa only [Cochain.map_add, Cochain.map_zero, Cochain.map_ofHom, ← δ_map,
    Functor.map_comp] using h

private def scalarCoconeSquareMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {K L K' L' : CochainComplex A ℤ} (φ : K ⟶ L) (ψ : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (w : φ ≫ b = a ≫ ψ) :
    mappingCocone φ ⟶ mappingCocone ψ := by
  refine mappingCocone.lift ψ (mappingCocone.fst φ ≫ a)
    ((mappingCocone.snd φ).comp (Cochain.ofHom b) (add_zero _)) ?_
  have hδ : δ (-1) 0 (mappingCocone.snd φ) =
      -Cochain.ofHom (mappingCocone.fst φ ≫ φ) := eq_neg_of_add_eq_zero_left
        (scalarCocone_relation φ)
  rw [δ_comp_ofHom, hδ]
  simp only [Cochain.neg_comp, ← Cochain.ofHom_comp]
  rw [Category.assoc, w, ← Category.assoc, neg_add_cancel]

/-- An additive functor maps the Roos cocone to the Roos cocone of its tower.
Both coordinates, including the shifted coordinate, are prescribed, so no cone
completion is chosen. Source: Stacks 08TC
(blueprint: def-sf-additive-roos-map).
Proof: apply the functor to the two cone coordinates. The universal property of each
product gives the specified maps to the target products. Additivity preserves 1-s and
the signed cocone differential, so these coordinates define a chain map. The cocone's
biproduct coordinates and joint monicity of the product projections give uniqueness. -/
theorem scalarRoosMap_existsUnique
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    ∃! α : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)),
      (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
          Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj (op n))) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
            Pi.π (fun n ↦ C.obj (op n)) n)) ∧
      (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ), α.f i ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)))).v i j h ≫
          (Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (C.obj (op n))) n).f j =
        F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j h ≫
          (Pi.π (fun n ↦ C.obj (op n)) n).f j)) := by
  dsimp only [integralOperationsRoos]
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let pc : G.obj (∏ᶜ (fun n ↦ C.obj (op n))) ⟶
      ∏ᶜ (fun n ↦ G.obj (C.obj (op n))) :=
    Pi.lift (fun n ↦ G.map (Pi.π (fun n ↦ C.obj (op n)) n))
  have w : G.map (scalarRoosBoundary C) ≫ pc =
      pc ≫ scalarRoosBoundary (C ⋙ G) := by
    apply Pi.hom_ext
    intro n
    have hC := (towerTransitionEndomorphism_eq_iff
      (integralOperationsTowerStep C) (scalarRoosBoundary C)).mp rfl n
    have hG := (towerTransitionEndomorphism_eq_iff
      (integralOperationsTowerStep (C ⋙ G)) (scalarRoosBoundary (C ⋙ G))).mp rfl n
    simp only [Category.assoc]
    rw [show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_comp_π _ n,
      ← G.map_comp, hC, G.map_sub, G.map_comp]
    dsimp only [Functor.comp_obj] at hG
    erw [hG]
    simp only [Preadditive.comp_sub, ← Category.assoc, pc, Pi.lift_comp_π]
    rfl
  let α := scalarAdditiveCoconeMap F (scalarRoosBoundary C) ≫
    scalarCoconeSquareMap (G.map (scalarRoosBoundary C)) (scalarRoosBoundary (C ⋙ G)) pc pc w
  have hα : (∀ n : ℕ, α ≫ CochainComplex.mappingCocone.fst
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ))) ≫
          Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (C.obj (op n))) n =
        (F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
            Pi.π (fun n ↦ C.obj (op n)) n)) ∧
      (∀ (i j : ℤ) (h : i + -1 = j) (n : ℕ), α.f i ≫
          (CochainComplex.mappingCocone.snd
            (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (ComplexShape.up ℤ)))).v i j h ≫
          (Pi.π (fun n ↦ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (C.obj (op n))) n).f j =
        F.map ((CochainComplex.mappingCocone.snd (scalarRoosBoundary C)).v i j h ≫
          (Pi.π (fun n ↦ C.obj (op n)) n).f j)) := by
    constructor
    · intro n
      dsimp only [α, scalarAdditiveCoconeMap, scalarCoconeSquareMap, G]
      simp only [Category.assoc, mappingCocone.lift_fst_assoc]
      change _ ≫ pc ≫ Pi.π _ n = _
      rw [show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_comp_π _ n]
      exact (G.map_comp _ _).symm
    · intro i j h n
      dsimp only [α, scalarAdditiveCoconeMap, scalarCoconeSquareMap, G]
      simp only [HomologicalComplex.comp_f, Category.assoc,
        mappingCocone.lift_f_snd_v_assoc]
      rw [Cochain.comp_v _ _ (add_zero (-1)) i j j h (add_zero j)]
      simp only [Cochain.ofHom_v, Category.assoc]
      rw [mappingCocone.lift_f_snd_v_assoc]
      simp only [Cochain.map_v]
      have hpc := congrArg (fun z ↦ z.f j)
        (show pc ≫ Pi.π _ n = G.map (Pi.π _ n) from Pi.lift_comp_π _ n)
      change pc.f j ≫ (Pi.π (fun n ↦ G.obj (C.obj (op n))) n).f j =
          F.map ((Pi.π (fun n ↦ C.obj (op n)) n).f j) at hpc
      rw [hpc]
      erw [← F.map_comp]
  refine ⟨α, hα, ?_⟩
  intro β hβ
  have hf : β ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) =
      α ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) := by
    apply Pi.hom_ext
    intro n
    simpa only [Category.assoc] using! (hβ.1 n).trans (hα.1 n).symm
  have hs (i j : ℤ) (h : i + -1 = j) :
      β.f i ≫ (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j h =
        α.f i ≫ (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i j h := by
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (ComplexShape.up ℤ) j)
      (fun n ↦ G.obj (C.obj (op n)))).hom_ext
    rintro ⟨n⟩
    simp only [Fan.mk_π_app, HomologicalComplex.eval_map]
    erw [Category.assoc, Category.assoc]
    simpa only [G] using! (hβ.2 i j h n).trans (hα.2 i j h n).symm
  ext i
  have hfi := congrArg (fun z ↦ z.f i) hf
  change β.f i ≫ _ = α.f i ≫ _ at hfi
  have hid := mappingCocone.id_X (scalarRoosBoundary (C ⋙ G)) i (i - 1) (by omega)
  have hβid := congrArg (fun z ↦ β.f i ≫ z) hid
  have hαid := congrArg (fun z ↦ α.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc, Category.comp_id] at hβid hαid
  rw [hfi, hs i (i - 1) (by omega)] at hβid
  exact (Category.comp_id (β.f i)).symm.trans (hβid.symm.trans hαid)

end ScalarRoos

/-- The Roos map with its two prescribed coordinates.
Source: Stacks 08TC (blueprint: def-sf-additive-roos-map). -/
def scalarRoosMap
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ)) :=
  (scalarRoosMap_existsUnique F C).exists.choose

section ScalarRoosNaturality
attribute [local implicit_reducible] integralOperationsRoos
  CochainComplex.mappingCocone
open CochainComplex CochainComplex.HomComplex
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]

/-- Coordinates of a strict tower map, computed directly on the shifted cone.
Source: Stacks 08TC; the elementary calculation in IntegralAmbientOperationModels.
Proof: rewrite the homotopy cofiber map as the usual cone map and evaluate its
first and second summands after shifting by minus one. -/
private theorem scalarRoosTowerCoordinates
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    integralOperationsRoosMap a ≫ mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')) =
      mappingCocone.fst (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)) ≫
        Limits.Pi.map (fun n : ℕ ↦ a.app (op n)) ∧
    ∀ (p q : ℤ) (h : p + -1 = q),
      (integralOperationsRoosMap a).f p ≫
          (mappingCocone.snd
            (towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C'))).v p q h =
        (mappingCocone.snd
          (towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C))).v p q h ≫
            (Limits.Pi.map (fun n : ℕ ↦ a.app (op n))).f q := by
  unfold integralOperationsRoosMap
  rw [cofiberMap_eq_coneMap _ _ _ _ (integralOperationsRoos_square a)]
  let φ := towerTransitionEndomorphism (K := fun n ↦ C.obj (op n))
        (integralOperationsTowerStep C)
  let ψ := towerTransitionEndomorphism (K := fun n ↦ C'.obj (op n))
        (integralOperationsTowerStep C')
  let b := Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  let c := mappingCone.map φ ψ b b (integralOperationsRoos_square a)
  constructor
  · apply HomologicalComplex.hom_ext
    intro p
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫ (mappingCocone.fst ψ).f p =
      (mappingCocone.fst φ).f p ≫ b.f p
    simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_map_f', mappingCocone.fst,
      HomologicalComplex.neg_f_apply, Cocycle.homOf_f, Cocycle.leftShift_coe,
      Cochain.leftShift_v (mappingCone.fst ψ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega),
      mul_zero, Int.reduceSub, mul_neg, neg_mul, one_mul, neg_neg, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self, zero_add,
      Int.negOnePow_one, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, Units.neg_smul, one_smul,
      Cochain.leftShift_v (mappingCone.fst φ).1 (-1) 0 (by omega) p p
        (add_zero p) (p + -1) (by omega)]
    erw [Category.id_comp, Category.id_comp]
    apply mappingCone.ext_from φ p (p + -1) (by omega)
    · simp only [Int.reduceNeg, mappingCone.map, mappingCone.inl_v_desc_f_assoc,
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc,
        mappingCone.inl_v_fst_v, Category.comp_id, c]
      have e := mappingCone.inl_v_fst_v φ p (p + -1) (by omega)
      with_unfolding_all simpa only [Category.assoc, Category.id_comp] using!
        (congrArg (fun z ↦ z ≫ b.f p) e).symm
    · simp only [Int.reduceNeg, mappingCone.map, mappingCone.inr_f_desc_f_assoc,
        HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_fst_v, comp_zero, c]
      have e := mappingCone.inr_f_fst_v φ (p + -1) p (by omega)
      with_unfolding_all simpa only [Category.assoc, zero_comp] using!
        (congrArg (fun z ↦ z ≫ b.f p) e).symm
  · intro p q h
    obtain rfl : q = p + -1 := h.symm
    change ((CategoryTheory.shiftFunctor _ (-1 : ℤ)).map c).f p ≫
      (mappingCocone.snd ψ).v p (p + -1) h =
        (mappingCocone.snd φ).v p (p + -1) h ≫ b.f (p + -1)
    simp only [Int.reduceNeg, shiftFunctor_obj_X', shiftFunctor_map_f', mappingCocone.snd,
      Cochain.leftShift_v (mappingCone.snd ψ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega),
      mul_neg, mul_one, neg_neg, Int.reduceSub, neg_mul, one_mul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, EuclideanDomain.div_self,
      Int.reduceAdd, Int.negOnePow_even 2 ⟨1, rfl⟩, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, one_smul,
      Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by omega)
        p (p + -1) rfl (p + -1) (by omega)]
    erw [Category.id_comp, Category.id_comp]
    apply mappingCone.ext_from φ p (p + -1) (by omega)
    · simp only [Int.reduceNeg, mappingCone.map, mappingCone.inl_v_desc_f_assoc,
        Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Category.assoc,
        mappingCone.inl_v_snd_v, comp_zero, c]
      have e := mappingCone.inl_v_snd_v φ p (p + -1) rfl
      with_unfolding_all simpa only [Category.assoc, zero_comp] using!
        (congrArg (fun z ↦ z ≫ b.f (p + -1)) e).symm
    · simp only [Int.reduceNeg, mappingCone.map, mappingCone.inr_f_desc_f_assoc,
        HomologicalComplex.comp_f, Category.assoc, mappingCone.inr_f_snd_v,
        Category.comp_id, c]
      have e := mappingCone.inr_f_snd_v φ (p + -1)
      with_unfolding_all simpa only [Category.assoc, Category.id_comp] using!
        (congrArg (fun z ↦ z ≫ b.f (p + -1)) e).symm

private theorem scalarRoosCoordinates (F : A ⥤ B) [F.Additive]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    scalarRoosMap F C ≫ mappingCocone.fst
        (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map
          (mappingCocone.fst (scalarRoosBoundary C)) ≫
        piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)) ∧
    ∀ i : ℤ, (scalarRoosMap F C).f i ≫
        (mappingCocone.snd
          (scalarRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v
            i (i - 1) (by omega) =
      F.map ((mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ C.obj (op n))).f (i - 1) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hf : scalarRoosMap F C ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) =
      G.map (mappingCocone.fst (scalarRoosBoundary C)) ≫ pc := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc]
    have h := (scalarRoosMap_existsUnique F C).exists.choose_spec.1 n
    change scalarRoosMap F C ≫ mappingCocone.fst (scalarRoosBoundary (C ⋙ G)) ≫
      Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n =
      G.map (mappingCocone.fst (scalarRoosBoundary C) ≫ Pi.π _ n) at h
    exact h.trans ((G.map_comp _ _).trans
      (congrArg (G.map (mappingCocone.fst (scalarRoosBoundary C)) ≫ ·)
        (piComparison_comp_π G (fun n : ℕ ↦ C.obj (op n)) n).symm))
  have hs (i : ℤ) : (scalarRoosMap F C).f i ≫
      (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i (i - 1) (by omega) =
    F.map ((mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega)) ≫
      pc.f (i - 1) := by
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval B (.up ℤ) (i - 1))
      (fun n : ℕ ↦ G.obj (C.obj (op n)))).hom_ext
    rintro ⟨n⟩
    change ((scalarRoosMap F C).f i ≫
        (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i (i - 1) (by omega)) ≫
          (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f (i - 1) = _
    simp only [Category.assoc]
    have h := (scalarRoosMap_existsUnique F C).exists.choose_spec.2
      i (i - 1) (by omega) n
    change (scalarRoosMap F C).f i ≫
        (mappingCocone.snd (scalarRoosBoundary (C ⋙ G))).v i (i - 1) (by omega) ≫
          (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f (i - 1) = _ at h
    rw [h]
    have hp := congrArg (fun f ↦ f.f (i - 1))
      (piComparison_comp_π G (fun n : ℕ ↦ C.obj (op n)) n)
    change pc.f (i - 1) ≫
      (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f (i - 1) =
        F.map ((Pi.π (fun n : ℕ ↦ C.obj (op n)) n).f (i - 1)) at hp
    change F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
        i (i - 1) (by omega) ≫ (Pi.π (fun n : ℕ ↦ C.obj (op n)) n).f (i - 1)) =
      F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
        i (i - 1) (by omega)) ≫ pc.f (i - 1) ≫
          (Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n).f (i - 1)
    rw [hp, ← F.map_comp]
  exact ⟨hf, hs⟩

/-- Naturality of the diagonal Roos comparison on arbitrary strict towers.
Source: Stacks 0941 (blueprint: def-sf-additive-roos-map).

Proof: naturality of the product comparison follows after every product projection.
Compose both proposed maps with the first and second cocone coordinates. The defining
coordinate equations for the diagonal map and for the tower map reduce both equations
to this product naturality. The two coordinates jointly determine each degree. -/
private theorem scalarRoosNaturality (F : A ⥤ B) [F.Additive]
    {C C' : ℕᵒᵖ ⥤ CochainComplex A ℤ} (a : C ⟶ C') :
    (F.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosMap a) ≫
        scalarRoosMap F C' =
      scalarRoosMap F C ≫ integralOperationsRoosMap
        (Functor.whiskerRight a (F.mapHomologicalComplex (.up ℤ))) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let b := CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ a.app (op n))
  let b' := CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ G.map (a.app (op n)))
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  let pc' := piComparison G (fun n : ℕ ↦ C'.obj (op n))
  have hp : G.map b ≫ pc' = pc ≫ b' := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, pc, pc', b, b', piComparison_comp_π, Pi.map_π]
    rw [← G.map_comp, Pi.map_π, G.map_comp]
    rw [← Category.assoc, piComparison_comp_π]
  obtain ⟨hCf, hCs⟩ := scalarRoosCoordinates F C
  obtain ⟨hC'f, hC's⟩ := scalarRoosCoordinates F C'
  obtain ⟨haf, has⟩ := scalarRoosTowerCoordinates a
  obtain ⟨ha'f, ha's⟩ := scalarRoosTowerCoordinates (Functor.whiskerRight a G)
  have hf : (G.map (integralOperationsRoosMap a) ≫ scalarRoosMap F C') ≫
        mappingCocone.fst (scalarRoosBoundary (C' ⋙ G)) =
      (scalarRoosMap F C ≫ integralOperationsRoosMap (Functor.whiskerRight a G)) ≫
        mappingCocone.fst (scalarRoosBoundary (C' ⋙ G)) := by
    simp only [Category.assoc]
    rw [hC'f, ← Category.assoc, ← G.map_comp, haf, G.map_comp]
    rw [Category.assoc, hp, ← Category.assoc, ← hCf]
    erw [Category.assoc, ← ha'f]
  have hs (i : ℤ) :
      ((G.map (integralOperationsRoosMap a) ≫ scalarRoosMap F C').f i) ≫
        (mappingCocone.snd (scalarRoosBoundary (C' ⋙ G))).v i (i - 1) (by omega) =
      ((scalarRoosMap F C ≫ integralOperationsRoosMap (Functor.whiskerRight a G)).f i) ≫
        (mappingCocone.snd (scalarRoosBoundary (C' ⋙ G))).v i (i - 1) (by omega) := by
    have hpi := congrArg (fun f ↦ f.f (i - 1)) hp
    change F.map (b.f (i - 1)) ≫ pc'.f (i - 1) =
      pc.f (i - 1) ≫ b'.f (i - 1) at hpi
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [hC's i, ← Category.assoc, ← F.map_comp, has i (i - 1) (by omega),
      F.map_comp, Category.assoc, hpi, ← Category.assoc, ← hCs i]
    erw [Category.assoc, ← ha's i (i - 1) (by omega)]
  ext i
  have hfi := congrArg (fun f ↦ f.f i) hf
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := mappingCocone.id_X (scalarRoosBoundary (C' ⋙ G)) i (i - 1) (by omega)
  have hleft := congrArg
    (fun z ↦ ((G.map (integralOperationsRoosMap a) ≫ scalarRoosMap F C').f i) ≫ z) hid
  have hright := congrArg
    (fun z ↦ ((scalarRoosMap F C ≫ integralOperationsRoosMap
      (Functor.whiskerRight a G)).f i) ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hfi, hs i] at hleft
  exact (Category.comp_id _).symm.trans
    (hleft.symm.trans (hright.trans (Category.comp_id _)))

end ScalarRoosNaturality

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

private def scalarRoosTransformation
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A] [Abelian A] [HasCountableProducts A]
    {B : Type u₄} [Category.{v₄} B] [Abelian B] [HasCountableProducts B]
    (T : C ⥤ (ℕᵒᵖ ⥤ CochainComplex A ℤ))
    (U : D ⥤ (ℕᵒᵖ ⥤ CochainComplex B ℤ)) (G : C ⥤ D)
    (F : A ⥤ B) [F.Additive]
    (α : T ⋙ (Functor.whiskeringRight ℕᵒᵖ _ _).obj
        (F.mapHomologicalComplex (.up ℤ)) ⟶ G ⋙ U) :
    T ⋙ integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ⟶
      G ⋙ U ⋙ integralOperationsRoosFunctor where
  app P := scalarRoosMap F (T.obj P) ≫ integralOperationsRoosMap (α.app P)
  naturality {P Q} a := by
    dsimp only [Functor.comp_map, integralOperationsRoosFunctor]
    rw [← Category.assoc, scalarRoosNaturality, Category.assoc,
      ← integralOperationsRoosMap_comp]
    rw [Category.assoc, ← integralOperationsRoosMap_comp]
    exact congrArg (fun z ↦ scalarRoosMap F (T.obj P) ≫ integralOperationsRoosMap z)
      (α.naturality a)

set_option backward.defeqAttrib.useBackward true in
private theorem scalarTowerAssembly
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {A : Type u₃} [Category.{v₃} A] {B : Type u₄} [Category.{v₄} B]
    (T : ℕ → C ⥤ A) (U : ℕ → D ⥤ B)
    (s : ∀ n, T (n + 1) ⟶ T n) (t : ∀ n, U (n + 1) ⟶ U n)
    (F : A ⥤ B) (G : C ⥤ D) (α : ∀ n, T n ⋙ F ⟶ G ⋙ U n)
    (h : ∀ n, Functor.whiskerRight (s n) F ≫ α n =
      α (n + 1) ≫ Functor.whiskerLeft G (t n)) :
    ∃! β : (Functor.ofOpSequence s).flip ⋙ (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⟶
        G ⋙ (Functor.ofOpSequence t).flip,
      ∀ X n, (β.app X).app (op n) = (α n).app X := by
  let β : (Functor.ofOpSequence s).flip ⋙ (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⟶
      G ⋙ (Functor.ofOpSequence t).flip :=
    { app := fun X ↦ NatTrans.ofOpSequence (fun n ↦ (α n).app X) (by
        intro n
        change F.map (((Functor.ofOpSequence s).map
            (homOfLE (n.le_add_right 1)).op).app X) ≫ (α n).app X =
          (α (n + 1)).app X ≫ ((Functor.ofOpSequence t).map
            (homOfLE (n.le_add_right 1)).op).app (G.obj X)
        dsimp only [Functor.ofOpSequence_obj, Functor.comp_obj]
        simpa only [Functor.ofOpSequence_map_homOfLE_succ, NatTrans.comp_app,
          Functor.whiskerRight_app, Functor.whiskerLeft_app] using congr_app (h n) X)
      naturality := by
        intro X Y f
        apply NatTrans.ext
        funext n
        exact (α n.unop).naturality f }
  refine ⟨β, fun _ _ ↦ rfl, ?_⟩
  intro γ hγ
  apply NatTrans.ext
  funext X
  apply NatTrans.ext
  funext n
  exact hγ X n.unop

end WeilConjectures
