/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Composition of projection-normalized Roos maps -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures

attribute [local implicit_reducible] integralOperationsRoos
  CochainComplex.mappingCocone

/-- A normalized additive Roos comparison respects any compositor of additive functors.
Source: Stacks 0941; blueprint dual-Tate compatibility, Steps 1 and 5
(blueprint: lem-pod-composition-roos-map).

Proof: project the product comparison to every tower level. Naturality of the
compositor makes its product component followed by the two successive product maps
equal the single product map followed by the levelwise compositor. The first and
second Roos coordinates reduce the desired equality to this product identity and
naturality of the compositor at each coordinate. The mapping-cocone identity
expresses every degree as the sum of the two coordinate inclusions, so equality of
both coordinates gives equality of the entire cochain maps. This works for arbitrary
towers, including zero towers, and requires no preservation or derived hypotheses. -/
theorem podCompositionRoosMap
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasCountableProducts A] [HasCountableProducts B] [HasCountableProducts D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] (a : H ≅ F ⋙ G)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app (integralOperationsRoos C) ≫
        (G.mapHomologicalComplex (.up ℤ)).map (scalarRoosMap F C) ≫
        scalarRoosMap G (C ⋙ F.mapHomologicalComplex (.up ℤ)) =
      scalarRoosMap H C ≫ integralOperationsRoosMap
        (whiskerLeft C (NatTrans.mapHomologicalComplex a.hom (.up ℤ))) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let HC := H.mapHomologicalComplex (.up ℤ)
  let α : HC ⟶ FC ⋙ GC := NatTrans.mapHomologicalComplex a.hom (.up ℤ)
  let τ := whiskerLeft C α
  let pF := piComparison FC (fun n : ℕ ↦ C.obj (op n))
  let pG := piComparison GC (fun n : ℕ ↦ FC.obj (C.obj (op n)))
  let pH := piComparison HC (fun n : ℕ ↦ C.obj (op n))
  let t := Limits.Pi.map (fun n : ℕ ↦ τ.app (op n))
  have hp : α.app (∏ᶜ fun n : ℕ ↦ C.obj (op n)) ≫ GC.map pF ≫ pG = pH ≫ t := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc]
    erw [piComparison_comp_π, ← GC.map_comp, piComparison_comp_π]
    erw [Pi.map_π, ← Category.assoc, piComparison_comp_π]
    exact (α.naturality (Pi.π (fun n : ℕ ↦ C.obj (op n)) n)).symm
  have hn {X Y : CochainComplex A ℤ} (q : X ⟶ Y) :
      α.app X ≫ GC.map (FC.map q) = HC.map q ≫ α.app Y :=
    (α.naturality q).symm
  obtain ⟨hFf, hFs⟩ := podReindexingRoosCoordinates F C
  obtain ⟨hGf, hGs⟩ := podReindexingRoosCoordinates G (C ⋙ FC)
  obtain ⟨hHf, hHs⟩ := podReindexingRoosCoordinates H C
  obtain ⟨hτf, hτs⟩ := IntegralAmbient.roosMap_coordinates τ
  let lhs := α.app (integralOperationsRoos C) ≫ GC.map (scalarRoosMap F C) ≫
    scalarRoosMap G (C ⋙ FC)
  let rhs := scalarRoosMap H C ≫ integralOperationsRoosMap τ
  have hf : lhs ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((C ⋙ FC) ⋙ GC)) =
    rhs ≫ CochainComplex.mappingCocone.fst
      (scalarRoosBoundary ((C ⋙ FC) ⋙ GC)) := by
    dsimp only [lhs, rhs]
    rw [Category.assoc, Category.assoc, hGf, ← Category.assoc (GC.map _),
      ← GC.map_comp, hFf, GC.map_comp]
    rw [← Category.assoc, ← Category.assoc, hn]
    erw [Category.assoc, Category.assoc, hp]
    erw [Category.assoc, hτf]
    simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ t) hHf.symm
  have hs (i : ℤ) : lhs.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((C ⋙ FC) ⋙ GC))).v i (i - 1) (by omega) =
    rhs.f i ≫ (CochainComplex.mappingCocone.snd
      (scalarRoosBoundary ((C ⋙ FC) ⋙ GC))).v i (i - 1) (by omega) := by
    have hpi := congrArg (fun q ↦ q.f (i - 1)) hp
    change a.hom.app _ ≫ G.map (pF.f (i - 1)) ≫ pG.f (i - 1) =
      pH.f (i - 1) ≫ t.f (i - 1) at hpi
    dsimp only [lhs, rhs]
    simp only [HomologicalComplex.comp_f, α, NatTrans.mapHomologicalComplex_app_f,
      Category.assoc]
    erw [hGs i, ← Category.assoc (G.map _), ← G.map_comp, hFs i, G.map_comp]
    erw [← Category.assoc, ← Category.assoc, ← a.hom.naturality]
    erw [Category.assoc, Category.assoc, hpi]
    erw [hτs i (i - 1) (by omega)]
    change _ = (scalarRoosMap H C).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary (C ⋙ HC))).v
        i (i - 1) (by omega) ≫ t.f (i - 1)
    simpa only [Category.assoc] using
      congrArg (fun q ↦ q ≫ t.f (i - 1)) (hHs i).symm
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun q ↦ q.f i) hf
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X
    (scalarRoosBoundary ((C ⋙ FC) ⋙ GC)) i (i - 1) (by omega)
  have hl := congrArg (fun z ↦ lhs.f i ≫ z) hid
  have hr := congrArg (fun z ↦ rhs.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hl hr
  rw [hfi, hs i] at hl
  exact (Category.comp_id _).symm.trans
    (hl.symm.trans (hr.trans (Category.comp_id _)))

end WeilConjectures
