/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import WeilConjectures.PoincareDuality.Pod.Composition.PodCompositionRoosMap
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison

/-! # Pasting additive Roos comparisons with tower maps -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
namespace WeilConjectures
attribute [local implicit_reducible] integralOperationsRoos
  CochainComplex.mappingCocone integralOperationsRoosFunctor

/-- Tower-map composition transports through the normalized additive Roos maps.
Source: blueprint dual-Tate compatibility, Steps 1 and 5; Stacks 0941
(blueprint: lem-pod-composition-roos-pasting).

Proof: replace the three comparison maps by their canonical values. Naturality
moves the first tower map past the second Roos comparison. The additive Roos
composition identity combines the three leading factors. Functoriality of Roos
then sends the assumed tower identity to equality of all remaining factors. -/
theorem podCompositionRoosPasting
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasCountableProducts A] [HasCountableProducts B] [HasCountableProducts D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive] (a : H ≅ F ⋙ G)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (Cf : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (Cc Chf : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (fRoos : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ F.mapHomologicalComplex (.up ℤ)))
    (gRoos : (G.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos Cf) ⟶
      integralOperationsRoos (Cf ⋙ G.mapHomologicalComplex (.up ℤ)))
    (hRoos : (H.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos C) ⟶
      integralOperationsRoos (C ⋙ H.mapHomologicalComplex (.up ℤ)))
    (rF : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ Cf)
    (rG : Cf ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ Chf)
    (rH : C ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ Cc) (σ : Cc ⟶ Chf)
    (hf : fRoos = scalarRoosMap F C) (hg : gRoos = scalarRoosMap G Cf)
    (hh : hRoos = scalarRoosMap H C) :
    let α : H.mapHomologicalComplex (.up ℤ) ⟶
        F.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ) :=
      NatTrans.mapHomologicalComplex a.hom (.up ℤ)
    rH ≫ σ = whiskerLeft C α ≫
        whiskerRight rF (G.mapHomologicalComplex (.up ℤ)) ≫ rG →
    α.app (integralOperationsRoos C) ≫
        (G.mapHomologicalComplex (.up ℤ)).map fRoos ≫
        (G.mapHomologicalComplex (.up ℤ)).map (integralOperationsRoosFunctor.map rF) ≫
        gRoos ≫ integralOperationsRoosFunctor.map rG =
      hRoos ≫ integralOperationsRoosFunctor.map rH ≫
        integralOperationsRoosFunctor.map σ := by
  dsimp only
  intro ht
  subst fRoos gRoos hRoos
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let HC := H.mapHomologicalComplex (.up ℤ)
  let α : HC ⟶ FC ⋙ GC := NatTrans.mapHomologicalComplex a.hom (.up ℤ)
  let τ := whiskerLeft C α
  let b := whiskerRight rF GC
  have hn : GC.map (integralOperationsRoosFunctor.map rF) ≫ scalarRoosMap G Cf =
      scalarRoosMap G (C ⋙ FC) ≫ integralOperationsRoosFunctor.map b :=
    podReindexingRoosNaturality G rF
  have hp : α.app (integralOperationsRoos C) ≫ GC.map (scalarRoosMap F C) ≫
      scalarRoosMap G (C ⋙ FC) = scalarRoosMap H C ≫
        integralOperationsRoosFunctor.map τ := podCompositionRoosMap F G H a C
  calc
    _ = α.app (integralOperationsRoos C) ≫ GC.map (scalarRoosMap F C) ≫
        scalarRoosMap G (C ⋙ FC) ≫ integralOperationsRoosFunctor.map b ≫
          integralOperationsRoosFunctor.map rG := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ α.app (integralOperationsRoos C) ≫ GC.map (scalarRoosMap F C) ≫
          q ≫ integralOperationsRoosFunctor.map rG) hn
    _ = scalarRoosMap H C ≫ integralOperationsRoosFunctor.map τ ≫
        integralOperationsRoosFunctor.map b ≫ integralOperationsRoosFunctor.map rG := by
      simpa only [Category.assoc] using congrArg
        (fun q ↦ q ≫ integralOperationsRoosFunctor.map b ≫
          integralOperationsRoosFunctor.map rG) hp
    _ = _ := by
      simpa only [Functor.map_comp, Category.assoc] using congrArg
        (fun q ↦ scalarRoosMap H C ≫ integralOperationsRoosFunctor.map q) ht.symm

end WeilConjectures
