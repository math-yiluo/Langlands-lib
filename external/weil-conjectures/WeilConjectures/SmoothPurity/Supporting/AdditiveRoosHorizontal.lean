/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison

/-! # Horizontal coherence of additive Roos comparisons
(blueprint: lem-pur-additive-roos-horizontal). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe a b a' b' v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

section RoosCoherence
attribute [local implicit_reducible] integralOperationsRoos
  CochainComplex.mappingCocone

open CochainComplex CochainComplex.HomComplex
variable {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
  {B : Type a'} [Category.{b'} B] [Abelian B] [HasCountableProducts B]
  {D : Type v} [Category.{w} D] [Abelian D] [HasCountableProducts D]

omit [HasCountableProducts A] [HasCountableProducts B] in
private theorem map_complex_iso_hom
    (F G : A ⥤ B) [F.Additive] [G.Additive] (η : F ≅ G) :
    (NatIso.mapHomologicalComplex η (.up ℤ)).hom =
      NatTrans.mapHomologicalComplex η.hom (.up ℤ) := rfl

private theorem roos_ext {C : ℕᵒᵖ ⥤ CochainComplex D ℤ}
    {K : CochainComplex D ℤ} (f g : K ⟶ integralOperationsRoos C)
    (hf : f ≫ mappingCocone.fst (scalarRoosBoundary C) =
      g ≫ mappingCocone.fst (scalarRoosBoundary C))
    (hs : ∀ i : ℤ, f.f i ≫
        (mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega) =
      g.f i ≫ (mappingCocone.snd (scalarRoosBoundary C)).v i (i - 1) (by omega)) :
    f = g := by
  ext i
  have hfi := congrArg (fun z ↦ z.f i) hf
  change f.f i ≫ _ = g.f i ≫ _ at hfi
  have hid := mappingCocone.id_X (scalarRoosBoundary C) i (i - 1) (by omega)
  have hl := congrArg (fun z ↦ f.f i ≫ z) hid
  have hr := congrArg (fun z ↦ g.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hl hr
  rw [hfi, hs i] at hl
  exact (Category.comp_id _).symm.trans
    (hl.symm.trans (hr.trans (Category.comp_id _)))

private theorem roos_product_horizontal
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (η : F ⋙ G ⟶ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (piComparison (F.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n))) ≫
      piComparison (G.mapHomologicalComplex (.up ℤ))
        (fun n : ℕ ↦ (F.mapHomologicalComplex (.up ℤ)).obj (C.obj (op n))) ≫
      Limits.Pi.map (fun n : ℕ ↦ (NatTrans.mapHomologicalComplex η (.up ℤ)).app
        (C.obj (op n))) =
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app (∏ᶜ (fun n : ℕ ↦ C.obj (op n))) ≫
      piComparison (H.mapHomologicalComplex (.up ℤ)) (fun n : ℕ ↦ C.obj (op n)) := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.map_π]
  rw [piComparison_comp_π_assoc, ← Functor.map_comp_assoc, piComparison_comp_π,
    piComparison_comp_π]
  ext i
  exact η.naturality ((Pi.π (fun n : ℕ ↦ C.obj (op n)) n).f i)

private theorem roos_horizontal
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (η : F ⋙ G ⟶ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) :
    (G.mapHomologicalComplex (.up ℤ)).map (scalarRoosMap F C) ≫
      scalarRoosMap G (C ⋙ F.mapHomologicalComplex (.up ℤ)) ≫
      integralOperationsRoosMap
        (Functor.whiskerLeft C (NatTrans.mapHomologicalComplex η (.up ℤ))) =
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app (integralOperationsRoos C) ≫
      scalarRoosMap H C := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let HC := H.mapHomologicalComplex (.up ℤ)
  let ηC := NatTrans.mapHomologicalComplex η (.up ℤ)
  let a := Functor.whiskerLeft C ηC
  obtain ⟨hFf, hFs⟩ := scalarRoosCoordinates F C
  obtain ⟨hGf, hGs⟩ := scalarRoosCoordinates G (C ⋙ FC)
  obtain ⟨hHf, hHs⟩ := scalarRoosCoordinates H C
  obtain ⟨haf, has⟩ := scalarRoosTowerCoordinates a
  dsimp only [a, Functor.whiskerLeft_app] at haf has
  have hp := roos_product_horizontal F G H η C
  apply roos_ext
  · simp only [Category.assoc]
    erw [haf, reassoc_of% hGf]
    rw [← GC.map_comp_assoc, hFf, GC.map_comp, Category.assoc, hp, hHf]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ piComparison HC (fun n : ℕ ↦ C.obj (op n)))
      (ηC.naturality (mappingCocone.fst (scalarRoosBoundary C)))
  · intro i
    have hpi := congrArg (fun z ↦ z.f (i - 1)) hp
    change G.map ((piComparison FC (fun n : ℕ ↦ C.obj (op n))).f (i - 1)) ≫
        (piComparison GC (fun n : ℕ ↦ FC.obj (C.obj (op n)))).f (i - 1) ≫
        (Limits.Pi.map (fun n : ℕ ↦ ηC.app (C.obj (op n)))).f (i - 1) =
      (ηC.app (∏ᶜ (fun n : ℕ ↦ C.obj (op n)))).f (i - 1) ≫
        (piComparison HC (fun n : ℕ ↦ C.obj (op n))).f (i - 1) at hpi
    simp only [HomologicalComplex.comp_f, Category.assoc,
      Functor.mapHomologicalComplex_map_f]
    erw [has i (i - 1) (by omega), reassoc_of% hGs i]
    rw [← G.map_comp_assoc, hFs i, G.map_comp, Category.assoc, hpi]
    erw [hHs i]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ (piComparison HC (fun n : ℕ ↦ C.obj (op n))).f (i - 1))
      (η.naturality ((mappingCocone.snd (scalarRoosBoundary C)).v
        i (i - 1) (by omega)))

private theorem roos_composite
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (η : F ⋙ G ⟶ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C' : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C'' : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C')
    (b : C' ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ C'')
    (c : C ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ C'')
    (h : Functor.whiskerRight a (G.mapHomologicalComplex (.up ℤ)) ≫ b =
      Functor.whiskerLeft C (NatTrans.mapHomologicalComplex η (.up ℤ)) ≫ c) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (scalarRoosMap F C ≫ integralOperationsRoosMap a) ≫
      scalarRoosMap G C' ≫ integralOperationsRoosMap b =
    (NatTrans.mapHomologicalComplex η (.up ℤ)).app (integralOperationsRoos C) ≫
      scalarRoosMap H C ≫ integralOperationsRoosMap c := by
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% scalarRoosNaturality G a, ← integralOperationsRoosMap_comp,
    h, integralOperationsRoosMap_comp]
  simpa only [Category.assoc] using
    congrArg (· ≫ integralOperationsRoosMap c) (roos_horizontal F G H η C)

/-- Compatible composites of strict tower comparisons give compatible Roos maps.
Source: Stacks Tag 08TC, functoriality of the explicit homotopy inverse limit.
(blueprint: lem-pur-additive-roos-horizontal).
Proof: product projections identify the horizontal composite of canonical product
comparisons with the comparison for the composite functor. Naturality of eta at
the two cocone coordinates and the mapping cocone identity decomposition give
horizontal coherence. Apply this, naturality, and functoriality of the Roos map
to the assumed equation of tower transformations. -/
theorem additiveRoosComposite
    (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive]
    (H : A ⥤ D) [H.Additive] (η : F ⋙ G ≅ H)
    (C : ℕᵒᵖ ⥤ CochainComplex A ℤ) (C' : ℕᵒᵖ ⥤ CochainComplex B ℤ)
    (C'' : ℕᵒᵖ ⥤ CochainComplex D ℤ)
    (a : C ⋙ F.mapHomologicalComplex (.up ℤ) ⟶ C')
    (b : C' ⋙ G.mapHomologicalComplex (.up ℤ) ⟶ C'')
    (c : C ⋙ H.mapHomologicalComplex (.up ℤ) ⟶ C'')
    (h : Functor.whiskerRight a (G.mapHomologicalComplex (.up ℤ)) ≫ b =
      Functor.whiskerLeft C (NatIso.mapHomologicalComplex η (.up ℤ)).hom ≫ c) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (scalarRoosMap F C ≫ integralOperationsRoosMap a) ≫
      scalarRoosMap G C' ≫ integralOperationsRoosMap b =
    (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app (integralOperationsRoos C) ≫
      scalarRoosMap H C ≫ integralOperationsRoosMap c := by
  rw [map_complex_iso_hom] at h ⊢
  exact roos_composite F G H η.hom C C' C'' a b c h

end RoosCoherence

end WeilConjectures
