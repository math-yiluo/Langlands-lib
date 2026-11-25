/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SixFunctors.Scalar.ScalarRoosComparison
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Functor naturality of the diagonal Roos comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures

attribute [local implicit_reducible] integralOperationsRoos scalarRoosMap

section FunctorNaturality
universe a b c d
variable {𝒜 : Type a} [Category.{b} 𝒜] [Abelian 𝒜] [HasCountableProducts 𝒜]
  {ℬ : Type c} [Category.{d} ℬ] [Abelian ℬ] [HasCountableProducts ℬ]

/-- The diagonal Roos comparison is natural in the additive functor.
Source: Stacks 0941, the two product coordinates of the Roos complex.
(blueprint: lem-pur-scalar-roos-functor-naturality).

Proof: compose with each projection of the first product. The defining scalar
Roos formulas and the strict tower-map formula give exactly the naturality
square of the functor transformation. The shifted product gives the same square
in degree i-1. Product projections are jointly monic, and the two cocone
coordinates sum to the identity, so these equations determine the chain map. -/
theorem scalarRoos_functor_naturality (F G : 𝒜 ⥤ ℬ) [F.Additive] [G.Additive]
    (α : F ⟶ G) (C : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) :
    (NatTrans.mapHomologicalComplex α (.up ℤ)).app (integralOperationsRoos C) ≫
        scalarRoosMap G C =
      scalarRoosMap F C ≫ integralOperationsRoosMap
        (Functor.whiskerLeft C (NatTrans.mapHomologicalComplex α (.up ℤ))) := by
  let FC := F.mapHomologicalComplex (.up ℤ)
  let GC := G.mapHomologicalComplex (.up ℤ)
  let αC := NatTrans.mapHomologicalComplex α (.up ℤ)
  let a := Functor.whiskerLeft C αC
  let lhs := αC.app (integralOperationsRoos C) ≫ scalarRoosMap G C
  let rhs := scalarRoosMap F C ≫ integralOperationsRoosMap a
  have hf : lhs ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary (C ⋙ GC)) =
      rhs ≫ CochainComplex.mappingCocone.fst (scalarRoosBoundary (C ⋙ GC)) := by
    apply Pi.hom_ext
    intro n
    dsimp only [lhs, rhs]
    simp only [Category.assoc]
    erw [(scalarRoosMap_existsUnique G C).exists.choose_spec.1 n]
    rw [reassoc_of% (scalarRoosTowerCoordinates a).1]
    erw [Pi.map_π]
    erw [reassoc_of% (scalarRoosMap_existsUnique F C).exists.choose_spec.1 n]
    exact (αC.naturality _).symm
  have hs (i : ℤ) : lhs.f i ≫
      (CochainComplex.mappingCocone.snd (scalarRoosBoundary (C ⋙ GC))).v
        i (i - 1) (by omega) =
      rhs.f i ≫
        (CochainComplex.mappingCocone.snd (scalarRoosBoundary (C ⋙ GC))).v
          i (i - 1) (by omega) := by
    apply (isLimitOfHasProductOfPreservesLimit
      (HomologicalComplex.eval ℬ (.up ℤ) (i - 1))
      (fun n : ℕ ↦ GC.obj (C.obj (op n)))).hom_ext
    rintro ⟨n⟩
    dsimp only [lhs, rhs, HomologicalComplex.comp_f]
    simp only [Category.assoc]
    change _ ≫ _ ≫ _ ≫ (Pi.π (fun n : ℕ ↦ GC.obj (C.obj (op n))) n).f (i - 1) = _
    erw [(scalarRoosMap_existsUnique G C).exists.choose_spec.2 i (i - 1) (by omega) n]
    rw [reassoc_of% (scalarRoosTowerCoordinates a).2 i (i - 1) (by omega)]
    have hp := congrArg (fun f ↦ f.f (i - 1))
      (Pi.map_π (fun n : ℕ ↦ a.app (op n)) n)
    simp only [HomologicalComplex.comp_f] at hp
    change (α.app ((integralOperationsRoos C).X i)) ≫ G.map _ =
      (scalarRoosMap F C).f i ≫ _ ≫
        (Limits.Pi.map (fun n : ℕ ↦ a.app (op n))).f (i - 1) ≫
        (Pi.π (fun n : ℕ ↦ GC.obj (C.obj (op n))) n).f (i - 1)
    erw [hp]
    erw [reassoc_of% (scalarRoosMap_existsUnique F C).exists.choose_spec.2
      i (i - 1) (by omega) n]
    exact (α.naturality _).symm
  change lhs = rhs
  apply HomologicalComplex.hom_ext
  intro i
  have hfi := congrArg (fun f ↦ f.f i) hf
  change _ ≫ _ = _ ≫ _ at hfi
  have hid := CochainComplex.mappingCocone.id_X (scalarRoosBoundary (C ⋙ GC))
    i (i - 1) (by omega)
  have hleft := congrArg (fun z ↦ lhs.f i ≫ z) hid
  have hright := congrArg (fun z ↦ rhs.f i ≫ z) hid
  simp only [Preadditive.comp_add, ← Category.assoc] at hleft hright
  rw [hfi, hs i] at hleft
  exact (Category.comp_id _).symm.trans
    (hleft.symm.trans (hright.trans (Category.comp_id _)))

end FunctorNaturality

end WeilConjectures
