/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.PodCompletionReindex.PodCompletionReindexModels
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Compatibility of normalized ordinary reindexing

Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5;
Stacks 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures

/-- Naturality of the projection-normalized Roos map with an ordinary identity relabelling.
Source: blueprint theorem-poincare-duality-frobenius--2, Steps 1 and 5; Stacks 0941
(blueprint: lem-pod-identity-roos-map).

Proof: the product comparison followed by the product of the identity components
is the identity component on the product, by each product projection and naturality.
Apply the two coordinate equations of the Roos comparison and of RoosMap. Both
coordinates become those of the identity component, by naturality in each degree.
The mapping-cocone decomposition of the identity makes the coordinates jointly monic. -/
theorem podIdentityRoosMap
    {A : Type*} [Category A] [Abelian A] [HasCountableProducts A]
    (F : A ⥤ A) [F.Additive] (a : F ≅ 𝟭 A)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (r : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ)))
    (hf : r ≫ CochainComplex.mappingCocone.fst
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ))) =
      (F.mapHomologicalComplex (.up ℤ)).map
        (CochainComplex.mappingCocone.fst (podRoosBoundary C)) ≫
          piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)))
    (hs : ∀ i : ℤ, r.f i ≫ (CochainComplex.mappingCocone.snd
        (podRoosBoundary (C ⋙ F.mapHomologicalComplex (.up ℤ)))).v
          i (i - 1) (by omega) =
      F.map ((CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
        i (i - 1) (by omega)) ≫
        (piComparison (F.mapHomologicalComplex (.up ℤ))
          (fun n : ℕ ↦ C.obj (op n))).f (i - 1)) :
    let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
      Functor.mapHomologicalComplexIdIso _ (.up ℤ)
    r ≫ integralOperationsRoosMap
        (isoWhiskerLeft C α ≪≫ C.rightUnitor).hom =
      α.hom.app (integralOperationsRoos C) := by
  dsimp only
  let G := F.mapHomologicalComplex (.up ℤ)
  let α := NatIso.mapHomologicalComplex a (.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)
  let τ := (isoWhiskerLeft C α ≪≫ C.rightUnitor).hom
  let pc := piComparison G (fun n : ℕ ↦ C.obj (op n))
  let t := CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ τ.app (op n))
  have hτ (n : ℕᵒᵖ) : τ.app n = α.hom.app (C.obj n) := by
    simp only [τ, Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
      whiskerLeft_app, rightUnitor_hom_app]
    exact Category.comp_id _
  have hα (K : CochainComplex A ℤ) (i : ℤ) :
      (α.hom.app K).f i = a.hom.app (K.X i) := by
    change a.hom.app (K.X i) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have hp : pc ≫ t = α.hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, t, Pi.map_π, hτ]
    change pc ≫ Pi.π _ n ≫ α.hom.app (C.obj (op n)) = _
    rw [← Category.assoc]
    rw [show pc ≫ Pi.π (fun n : ℕ ↦ G.obj (C.obj (op n))) n =
      G.map (Pi.π (fun n : ℕ ↦ C.obj (op n)) n) from piComparison_comp_π _ _ _]
    exact α.hom.naturality (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)
  obtain ⟨htf, hts⟩ := IntegralAmbient.roosMap_coordinates τ
  have hfirst : (r ≫ integralOperationsRoosMap τ) ≫
      CochainComplex.mappingCocone.fst (podRoosBoundary C) =
    α.hom.app (integralOperationsRoos C) ≫
      CochainComplex.mappingCocone.fst (podRoosBoundary C) := by
    rw [Category.assoc, htf, ← Category.assoc, hf]
    rw [Category.assoc, hp]
    exact α.hom.naturality _
  have hsecond (i : ℤ) :
      (r ≫ integralOperationsRoosMap τ).f i ≫
        (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          i (i - 1) (by omega) =
      (α.hom.app (integralOperationsRoos C)).f i ≫
        (CochainComplex.mappingCocone.snd (podRoosBoundary C)).v
          i (i - 1) (by omega) := by
    have hpi := congrArg (fun z ↦ z.f (i - 1)) hp
    change pc.f (i - 1) ≫ t.f (i - 1) =
      (α.hom.app (∏ᶜ fun n : ℕ ↦ C.obj (op n))).f (i - 1) at hpi
    simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [hts i (i - 1) (by omega), ← Category.assoc, hs i]
    rw [Category.assoc, hpi]
    rw [hα, hα]
    exact a.hom.naturality _
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun z ↦ z.f i) hfirst
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X (podRoosBoundary C)
    i (i - 1) (by omega)
  have hl := congrArg
    (fun z ↦ (r ≫ integralOperationsRoosMap τ).f i ≫ z) hid
  have hr := congrArg
    (fun z ↦ (α.hom.app (integralOperationsRoos C)).f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hl hr
  rw [hfi, hsecond i] at hl
  exact (Category.comp_id _).symm.trans
    (hl.symm.trans (hr.trans (Category.comp_id _)))

end WeilConjectures
