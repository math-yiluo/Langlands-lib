/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Composing localization comparisons in a ring tower

Source: Stacks Project, Algebra, Tag 00R7, second paragraph of the proof;
localization base change and composition.
(blueprint: lem-weil-pbc-tensor-localization-tower-transition).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Module

/-- Two successive transition localization comparisons give the composite comparison.
Source: Stacks Project, Algebra, proof of Tag 00R7, second paragraph, using localization
base change (Tag 00DK) and composition of localizations.
(blueprint: lem-weil-pbc-tensor-localization-tower-transition).

Proof: put P = B tensor over A A'. Base-change the localization P → B' along
P → C tensor over B P. Its target is C tensor over B B'. The canonical associativity
and cancellation isomorphism identifies its source with C tensor over A A'. Compose
this localization with the supplied localization C tensor over B B' → C'. A composite
of localizations is a localization at the submonoid consisting of numerators of elements
inverted at the second step. The pure-tensor formulas ensure that the resulting ring map
sends c tensor a' to t(c) times the image of a' in C'. This calculation can be checked
on pure tensors; these generate the tensor product additively. -/
theorem tensorLocalization_tower_transition
    (A B C A' B' C' : Type u)
    [CommRing A] [CommRing B] [CommRing C]
    [CommRing A'] [CommRing B'] [CommRing C']
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra A' B'] [Algebra B' C'] [Algebra A' C'] [IsScalarTower A' B' C']
    (r : A →+* A') (s : B →+* B') (t : C →+* C')
    (hB :
      letI := r.toAlgebra
      ∃ φ : B ⊗[A] A' →+* B',
        (∀ (b : B) (a : A'), φ (b ⊗ₜ[A] a) = s b * algebraMap A' B' a) ∧
        (letI := φ.toAlgebra; ∃ U : Submonoid (B ⊗[A] A'), IsLocalization U B'))
    (hC :
      letI := s.toAlgebra
      ∃ φ : C ⊗[B] B' →+* C',
        (∀ (c : C) (b : B'), φ (c ⊗ₜ[B] b) = t c * algebraMap B' C' b) ∧
        (letI := φ.toAlgebra; ∃ U : Submonoid (C ⊗[B] B'), IsLocalization U C')) :
    letI := r.toAlgebra
    ∃ (f : C ⊗[A] A' →+* C') (U : Submonoid (C ⊗[A] A')),
      (∀ (c : C) (a : A'), f (c ⊗ₜ[A] a) = t c * algebraMap A' C' a) ∧
      (letI := f.toAlgebra; IsLocalization U C')  := by
  let : Algebra A A' := r.toAlgebra
  obtain ⟨φB, hφB, U, hU⟩ := hB
  let : Algebra B B' := s.toAlgebra
  obtain ⟨φC, hφC, V, hV⟩ := hC
  let P := B ⊗[A] A'
  let Q := C ⊗[B] P
  let L := C ⊗[B] B'
  let fB : P →ₐ[B] B' :=
    { φB with
      commutes' := by
        intro b
        change φB (b ⊗ₜ[A] 1) = s b
        rw [hφB, map_one, mul_one] }
  let g : Q →ₐ[C] L := Algebra.TensorProduct.map (AlgHom.id C C) fB
  let : Algebra P B' := φB.toAlgebra
  have : IsScalarTower B P B' := by
    apply IsScalarTower.of_algebraMap_eq
    intro b
    exact (fB.commutes b).symm
  have : IsLocalization U B' := hU
  let : Algebra Q L := g.toAlgebra
  have : IsScalarTower C Q L := by
    apply IsScalarTower.of_algebraMap_eq
    intro c
    exact (g.commutes c).symm
  have hQL : IsLocalization
      (U.map (Algebra.TensorProduct.includeRight (R := B) (A := C))) L := by
    apply IsLocalization.tensorProduct_tensorProduct_right B C U B'
    apply RingHom.ext
    intro x
    change g (1 ⊗ₜ[B] x) = 1 ⊗ₜ[B] φB x
    rfl
  let : Algebra L C' := φC.toAlgebra
  have : IsLocalization V C' := hV
  let : Algebra Q C' := (φC.comp g.toRingHom).toAlgebra
  have : IsScalarTower Q L C' := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  let W := IsLocalization.localizationLocalizationSubmodule
    (U.map (Algebra.TensorProduct.includeRight (R := B) (A := C))) V
  have hQC : IsLocalization W C' :=
    IsLocalization.localization_localization_isLocalization _ V C'
  let e : Q ≃ₐ[C] C ⊗[A] A' := Algebra.TensorProduct.cancelBaseChange A B C C A'
  let f : C ⊗[A] A' →+* C' := (φC.comp g.toRingHom).comp e.symm.toRingHom
  refine ⟨f, W.map e, ?_, ?_⟩
  · intro c a
    dsimp [f]
    change φC (c ⊗ₜ[B] φB (1 ⊗ₜ[A] a)) = _
    rw [hφB, map_one, one_mul, hφC, ← IsScalarTower.algebraMap_apply A' B' C']
  · exact IsLocalization.isLocalization_of_base_ringEquiv W C' e.toRingEquiv


end Module
