/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Category.Ring.Colimits
import WeilConjectures.RingTheory.FinitePresentationComparisonSystem
import WeilConjectures.RingTheory.FilteredPushoutBijectiveStage

/-! # A finitely presented comparison model reaches a stage -/

@[expose] public section

open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

universe v w x y

namespace RingHom

/-- Descend a finitely presented model and its comparison isomorphism to a stage.
(blueprint: lem-weil-pbc-finite-presentation-model-stage)

Source: Stacks Project, Algebra, Tag 02JO (3), proof after the application of (1);
Tags 00QO and 05N9 (2), (3) supply factorization and eventual equality.

Proof: restrict to the indices above i₀. Tensor products commute with these
filtered colimits, so the systems Aᵢ ⊗ B₀ and Aᵢ ⊗ C₀ have colimits A ⊗ B₀ and
A ⊗ C₀. Factor the map P → A ⊗ B₀ through a stage using the finite presentation
of P over the integers. Above that stage use this factorization to make both
systems P-algebras. The map Q → A ⊗ C₀ induced by the given isomorphism factors
through a later stage, since Q is finitely presented over P. The resulting map
from (Aᵢ ⊗ B₀) ⊗[P] Q to Aᵢ ⊗ C₀ becomes the given isomorphism at the limit.
Its source is finitely presented by base change; its target is finitely
presented over Aᵢ ⊗ B₀ by tensor cancellation and the finite presentation of φ₀.
Factor the inverse isomorphism through a later stage using Tag 05N9 (2).
The two inverse identities hold at the limit, so each holds at a later stage
by Tag 05N9 (3). Take a common upper bound. The descended maps are inverse ring
homomorphisms there, giving eᵢ. Compatibility with the stage map holds by the
construction of the comparison on pure tensors. This argument uses no
flatness of P → Q and applies also to zero rings and empty presentations.
-/
theorem exists_finitePresentation_model_stage
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ CommRingCat.{v}) [HasColimit F]
    (i₀ : I) (B₀ : Type w) (C₀ : Type x) [CommRing B₀] [CommRing C₀]
    [Algebra (F.obj i₀) B₀] [Algebra (F.obj i₀) C₀]
    (φ₀ : B₀ →ₐ[F.obj i₀] C₀) (hfp : φ₀.toRingHom.FinitePresentation)
    (P Q : Type y) [CommRing P] [CommRing Q] [Algebra P Q]
    [Algebra.FinitePresentation ℤ P] [Algebra.FinitePresentation P Q]
    (aP : letI := (colimit.ι F i₀).hom.toAlgebra
      Algebra P (↥(colimit F) ⊗[F.obj i₀] B₀))
    (e : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      (↥(colimit F) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(colimit F) ⊗[F.obj i₀] C₀))
    (he : letI := (colimit.ι F i₀).hom.toAlgebra
      letI := aP
      e.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := P)
          (A := ↥(colimit F) ⊗[F.obj i₀] B₀) (B := Q)) =
        (Algebra.TensorProduct.map (Algebra.ofId ↥(colimit F) ↥(colimit F)) φ₀).toRingHom) :
    ∃ (i : I) (hi : i₀ ≤ i), letI := (F.map (homOfLE hi)).hom.toAlgebra
      ∃ (aPi : Algebra P (↥(F.obj i) ⊗[F.obj i₀] B₀)), letI := aPi
        ∃ eᵢ : (↥(F.obj i) ⊗[F.obj i₀] B₀) ⊗[P] Q ≃+* (↥(F.obj i) ⊗[F.obj i₀] C₀),
          eᵢ.toRingHom.comp
            (Algebra.TensorProduct.includeLeftRingHom (R := P)
              (A := ↥(F.obj i) ⊗[F.obj i₀] B₀) (B := Q)) =
            (Algebra.TensorProduct.map (Algebra.ofId (F.obj i) (F.obj i)) φ₀).toRingHom := by
  classical
  obtain ⟨i, hi, aPs, D, E, α, d, c, cD, cE, f, hD, hE,
      hfilt, hcomm, hbij, hfpα, hpush, hcompat⟩ :=
    exists_finitePresentation_comparison_system F i₀ B₀ C₀ φ₀ hfp P Q aP e he
  let := hfilt
  obtain ⟨j, hj⟩ := CommRingCat.exists_bijective_stage_of_filtered_pushouts
    D E α cD cE hD hE f hcomm hbij hfpα hpush
  refine ⟨j.val, hi.trans j.property, aPs j, ?_⟩
  let eᵢ := (d j).symm.trans ((RingEquiv.ofBijective (α.app j).hom hj).trans (c j))
  exact ⟨eᵢ, hcompat j⟩

end RingHom
