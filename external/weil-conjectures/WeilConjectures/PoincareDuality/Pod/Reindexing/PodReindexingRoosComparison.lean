/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # The diagonal Roos comparison of an exact equivalence

Source: Stacks 0941 (blueprint: lem-pod-reindexing-roos-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex
universe a b c d
namespace WeilConjectures

variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasCountableProducts B]

private def coconeCoordinates {K L : CochainComplex A ℤ} (φ : K ⟶ L) (i : ℤ) :
    (mappingCocone φ).X i ≅ K.X i ⊞ L.X (i - 1) where
  hom := biprod.lift ((mappingCocone.fst φ).f i)
    ((mappingCocone.snd φ).v i (i - 1) (by omega))
  inv := biprod.desc ((mappingCocone.inl φ).v i i (by omega))
    ((mappingCocone.inr φ).1.v (i - 1) i (by omega))
  hom_inv_id := by simpa using mappingCocone.id_X φ i (i - 1) (by omega)
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

/-- Both coordinates of the additive Roos map, expressed through the product comparison.
Source: Stacks 0941 (blueprint: lem-pod-reindexing-roos-comparison).

Proof: compose the defining equations of scalarRoosMap with every product projection.
The product comparison has exactly the images of those projections. Their joint
monicity identifies the first coordinate and every degree of the second coordinate. -/
theorem podReindexingRoosCoordinates (F : A ⥤ B) [F.Additive]
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
    exact (F.map_comp _ _).trans
      (congrArg (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
        i (i - 1) (by omega)) ≫ ·) hp.symm)
  exact ⟨hf, hs⟩

/-- Naturality of the diagonal Roos comparison on arbitrary strict towers.
Source: Stacks 0941 (blueprint: lem-pod-reindexing-roos-comparison).

Proof: naturality of the product comparison follows after every product projection.
Compose both proposed maps with the first and second cocone coordinates. The defining
coordinate equations for the diagonal map and for the tower map reduce both equations
to this product naturality. The two coordinates jointly determine each degree. -/
theorem podReindexingRoosNaturality (F : A ⥤ B) [F.Additive]
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
  obtain ⟨hCf, hCs⟩ := podReindexingRoosCoordinates F C
  obtain ⟨hC'f, hC's⟩ := podReindexingRoosCoordinates F C'
  obtain ⟨haf, has⟩ := IntegralAmbient.roosMap_coordinates a
  obtain ⟨ha'f, ha's⟩ := IntegralAmbient.roosMap_coordinates (Functor.whiskerRight a G)
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

/-- The projection-normalized Roos map of an additive product-preserving equivalence
is an isomorphism on arbitrary strict towers.
Source: Stacks 0941, blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5
(blueprint: lem-pod-reindexing-roos-comparison).

Proof: use scalarRoosMap, which is uniquely specified by both cocone coordinates
and every product projection. Its degree-i coordinate matrix is the direct sum
of the product comparisons in degrees i and i-1. Those comparisons are invertible
because an equivalence preserves products. The additive functor preserves the
biproduct decomposition of the source cocone, so the displayed matrix proves
invertibility in every degree. A chain map invertible in every degree is an
isomorphism of complexes. No acyclicity, boundedness, or completeness is needed. -/
theorem podReindexingRoosComparison (F : A ⥤ B) [F.Additive] [F.IsEquivalence]
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) : IsIso (scalarRoosMap F C) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  let : G.IsEquivalence := (F.asEquivalence.mapHomologicalComplex (.up ℤ)).isEquivalence_functor
  let pc : G.obj (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ⟶
      ∏ᶜ fun n : ℕ ↦ G.obj (C.obj (op n)) :=
    piComparison G (fun n : ℕ ↦ C.obj (op n))
  have hpc : IsIso pc := by dsimp only [pc]; infer_instance
  obtain ⟨hf, hs⟩ := podReindexingRoosCoordinates F C
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBiproducts F
  have hpcf (i : ℤ) : IsIso (pc.f i) := inferInstance
  have hi (i : ℤ) : IsIso ((scalarRoosMap F C).f i) := by
    let eY := coconeCoordinates (scalarRoosBoundary C) i
    let eX := coconeCoordinates (scalarRoosBoundary (C ⋙ G)) i
    have he : F.map eY.hom ≫
        (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom =
        biprod.lift (F.map ((mappingCocone.fst (scalarRoosBoundary C)).f i))
          (F.map ((mappingCocone.snd (scalarRoosBoundary C)).v
            i (i - 1) (by omega))) :=
      biprod.map_lift_mapBiprod F _ _ _ _
    have hm : (scalarRoosMap F C).f i ≫ eX.hom =
        F.map eY.hom ≫ (F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
            ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1))).hom ≫
          biprod.map (pc.f i) (pc.f (i - 1)) := by
      rw [← Category.assoc, he]
      apply biprod.hom_ext
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc]
        exact congrArg (fun f ↦ f.f i) hf
      · dsimp only [eX, coconeCoordinates]
        simp only [Category.assoc]
        erw [biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc]
        exact hs i
    have : IsIso ((scalarRoosMap F C).f i ≫ eX.hom) := by
      rw [hm]
      change IsIso (((F.mapIso eY) ≪≫
        F.mapBiprod ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X i)
          ((∏ᶜ fun n : ℕ ↦ C.obj (op n)).X (i - 1)) ≪≫
        biprod.mapIso (asIso (pc.f i)) (asIso (pc.f (i - 1)))).hom)
      infer_instance
    exact IsIso.of_isIso_comp_right _ eX.hom
  exact HomologicalComplex.Hom.isIso_of_components _

end WeilConjectures
