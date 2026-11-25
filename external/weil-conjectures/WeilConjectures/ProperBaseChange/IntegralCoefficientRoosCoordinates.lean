/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.ProperIntegralOrdinaryData
import WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRoosComparison
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Normalized coefficient comparison of Roos complexes

Source: Stacks 0941 and 08TC; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-weil-pbc-integral-coefficient-roos-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] pbcIntegralDatum integralDetailedCoefficientComparison

section Generic
attribute [local implicit_reducible] integralOperationsRoos integralOperationsRoosFunctor
  integralOperationsTowerStep CochainComplex.mappingCone CochainComplex.mappingCocone

private def coefficientRoosIso
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence] :
    integralOperationsRoosFunctor ⋙ F.mapHomologicalComplex (.up ℤ) ≅
      (Functor.whiskeringRight ℕᵒᵖ _ _).obj (F.mapHomologicalComplex (.up ℤ)) ⋙
        integralOperationsRoosFunctor :=
  NatIso.ofComponents (fun C ↦
    @asIso _ _ _ _ (scalarRoosMap F C) (podReindexingRoosComparison F C))
    (by intro C D f; exact podReindexingRoosNaturality F f)

private theorem coefficientRoos_coordinates
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasCountableProducts A] [HasCountableProducts B]
    (F : A ⥤ B) [F.Additive] [F.IsEquivalence]
    (C : ℕᵒᵖ ⥤ CochainComplex B ℤ) (D : ℕᵒᵖ ⥤ CochainComplex A ℤ)
    (t : C ≅ D ⋙ F.mapHomologicalComplex (.up ℤ))
    (z : (F.mapHomologicalComplex (.up ℤ)).obj (integralOperationsRoos D) ≅
      integralOperationsRoos C)
    (hz : z.hom = (coefficientRoosIso F).hom.app D ≫
      integralOperationsRoosFunctor.map t.inv) :
    (∀ (n : ℕ) (i : ℤ),
      z.hom.f i ≫ (CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
          (integralOperationsTowerStep C))).f i ≫
          (Pi.π (fun m : ℕ ↦ C.obj (op m)) n).f i =
        F.map ((CochainComplex.mappingCocone.fst
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
          (integralOperationsTowerStep D))).f i ≫
          (Pi.π (fun m : ℕ ↦ D.obj (op m)) n).f i) ≫ (t.inv.app (op n)).f i) ∧
    (∀ (n : ℕ) (i j : ℤ) (hij : i + -1 = j),
      z.hom.f i ≫ (CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ C.obj (op n))
          (integralOperationsTowerStep C))).v i j hij ≫
          (Pi.π (fun m : ℕ ↦ C.obj (op m)) n).f j =
        F.map ((CochainComplex.mappingCocone.snd
        (towerTransitionEndomorphism (K := fun n : ℕ ↦ D.obj (op n))
          (integralOperationsTowerStep D))).v i j hij ≫
          (Pi.π (fun m : ℕ ↦ D.obj (op m)) n).f j) ≫ (t.inv.app (op n)).f j) := by
  let G := F.mapHomologicalComplex (.up ℤ)
  have hs := (scalarRoosMap_existsUnique F D).exists.choose_spec
  obtain ⟨hm₁, hm₂⟩ := IntegralAmbient.roosMap_coordinates t.inv
  constructor
  · intro n i
    have hh : z.hom ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary C) ≫
        Pi.π (fun m : ℕ ↦ C.obj (op m)) n =
        G.map (CochainComplex.mappingCocone.fst (scalarRoosBoundary D) ≫
          Pi.π (fun m : ℕ ↦ D.obj (op m)) n) ≫ t.inv.app (op n) := by
      rw [hz]
      change (scalarRoosMap F D ≫ integralOperationsRoosMap t.inv) ≫ _ ≫ _ = _
      rw [Category.assoc, ← Category.assoc (integralOperationsRoosMap t.inv),
        hm₁, Category.assoc, Pi.map_π]
      have h := hs.1 n
      change scalarRoosMap F D ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary (D ⋙ G)) ≫
          Pi.π (fun m : ℕ ↦ G.obj (D.obj (op m))) n =
        G.map (CochainComplex.mappingCocone.fst (scalarRoosBoundary D) ≫ Pi.π _ n) at h
      change scalarRoosMap F D ≫
        CochainComplex.mappingCocone.fst (scalarRoosBoundary (D ⋙ G)) ≫
          Pi.π (fun m : ℕ ↦ G.obj (D.obj (op m))) n ≫ t.inv.app (op n) = _
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ t.inv.app (op n)) h
    simpa only [G, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      Category.assoc] using congrArg (fun f ↦ f.f i) hh
  · intro n i j hij
    rw [hz]
    change (scalarRoosMap F D ≫ integralOperationsRoosMap t.inv).f i ≫ _ ≫ _ = _
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [← Category.assoc ((integralOperationsRoosMap t.inv).f i), hm₂ i j hij]
    have hp := congrArg (fun f ↦ f.f j)
      (Pi.map_π (fun m : ℕ ↦ t.inv.app (op m)) n)
    simp only [HomologicalComplex.comp_f] at hp
    rw [Category.assoc, hp]
    have h := hs.2 i j hij n
    change (scalarRoosMap F D).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary (D ⋙ G))).v i j hij ≫
        (Pi.π (fun m : ℕ ↦ G.obj (D.obj (op m))) n).f j = _ at h
    change (scalarRoosMap F D).f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary (D ⋙ G))).v i j hij ≫
        (Pi.π (fun m : ℕ ↦ G.obj (D.obj (op m))) n).f j ≫ (t.inv.app (op n)).f j = _
    simpa only [Category.assoc] using
      congrArg (fun f ↦ f ≫ (t.inv.app (op n)).f j) h

end Generic

attribute [local irreducible] integralOperationsRoos coefficientRoosIso

private theorem coefficientRoosCoordinatesNative
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : Scheme.{u})
    [(pbcIntegralTransportModules U l E).IsEquivalence]
    (C : ℕᵒᵖ ⥤ CochainComplex
      (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
    (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E U) ℤ)
    (t : C ≅ D ⋙ pbcIntegralTransportComplex U l E)
    (z : (pbcIntegralTransportComplex U l E).obj (integralOperationsRoos D) ≅
      integralOperationsRoos C)
    (hz : z.hom = (coefficientRoosIso (A := integralTowerModules l E U)
        (B := pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))
        (pbcIntegralTransportModules U l E)).hom.app D ≫
      integralOperationsRoosFunctor.map t.inv) :
    PbcIntegralRoosTransportCoordinates U l E C D t z := by
  exact coefficientRoos_coordinates
    (A := integralTowerModules l E U)
    (B := pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))
    (pbcIntegralTransportModules U l E) C D t z hz

/-- Coefficient restriction transports the Roos complex naturally, with both
coordinates normalized after every strict tower isomorphism.

Source: Stacks 0941 and 08TC; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-weil-pbc-integral-coefficient-roos-coordinates).

Proof: the scalar comparison of products is invertible because restriction is an
equivalence. Transporting the mapping cocone of one minus transition gives the
natural isomorphism gamma. Compose gamma with Roos of the inverse strict tower
map. Naturality of the first and shifted coordinates, followed by the product
projection identities of scalarRoosMap, gives the two displayed coordinate laws.
Any z with that same hom has those laws as well. -/
theorem pbc_integral_coefficient_roos_coordinates
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] (U : Scheme.{u})
    [(pbcIntegralTransportModules U l E).IsEquivalence] :
    ∃ γ : integralOperationsRoosFunctor (A := integralTowerModules l E U) ⋙
          pbcIntegralTransportComplex U l E ≅
        (Functor.whiskeringRight ℕᵒᵖ _ _).obj (pbcIntegralTransportComplex U l E) ⋙
          integralOperationsRoosFunctor
            (A := pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))),
      ∀ (C : ℕᵒᵖ ⥤ CochainComplex
          (pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E))) ℤ)
        (D : ℕᵒᵖ ⥤ CochainComplex (integralTowerModules l E U) ℤ)
        (t : C ≅ D ⋙ pbcIntegralTransportComplex U l E)
        (z : (pbcIntegralTransportComplex U l E).obj (integralOperationsRoos D) ≅
          integralOperationsRoos C),
        z.hom = γ.hom.app D ≫ integralOperationsRoosFunctor.map t.inv →
          PbcIntegralRoosTransportCoordinates U l E C D t z := by
  refine ⟨coefficientRoosIso (A := integralTowerModules l E U)
      (B := pbcModules U (pbcAdicCompletion U (pbcIntegralDatum l E)))
      (pbcIntegralTransportModules U l E), ?_⟩
  intro C D t z hz
  exact coefficientRoosCoordinatesNative l E U C D t z hz

end WeilConjectures
