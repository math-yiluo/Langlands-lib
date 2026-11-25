/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # A simultaneous finite free splitting extension

Source: Stacks Project, Morphisms, Tag 03HW, proof of lemma-massage-finite; Algebra,
lemma-adjoin-roots. Split equations successively and compose their finite free bases
(blueprint: lem-weil-pbc-finite-monic-simultaneous-splitting).
-/

@[expose] public section

universe u

open Polynomial

/-- Successively split a finite family over nonzero finite free extensions. -/
private theorem exists_nontrivial_splitting (n : ℕ) (R : Type u) [CommRing R]
    [Nontrivial R] (P : Fin n → R[X]) (hP : ∀ i, (P i).Monic) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : Nontrivial S),
      ∀ i, ((P i).map (algebraMap R S)).Splits := by
  induction n generalizing R with
  | zero =>
    exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨T, _, _, _, _, _, hT⟩ := (hP 0).exists_splits_map
    obtain ⟨S, _, _, _, _, _, hS⟩ := ih T
      (fun i ↦ (P i.succ).map (algebraMap R T)) (fun i ↦ (hP i.succ).map _)
    algebraize [(algebraMap T S).comp (algebraMap R T)]
    refine ⟨S, inferInstance, inferInstance, Module.Finite.trans T S,
      Module.Free.trans (R := R) (S := T), inferInstance, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [IsScalarTower.algebraMap_eq R T S, ← Polynomial.map_map]
      exact hT.map _
    · rw [IsScalarTower.algebraMap_eq R T S, ← Polynomial.map_map]
      exact hS j

/-- A finite family of monic equations splits over one faithful finite free algebra.
Source: Stacks Project, Tag 03HW, proof of lemma-massage-finite, and Algebra,
lemma-adjoin-roots. Split each equation by `Polynomial.Monic.exists_splits_map`, preserving
previous factorizations by mapping them into the next extension. Transitivity of finite free
modules supplies the final basis. Nontriviality and freeness imply faithfulness.
For the zero base ring the identity extension suffices.
(blueprint: lem-weil-pbc-finite-monic-simultaneous-splitting). -/
theorem exists_faithful_finite_free_splitting (R : Type u) [CommRing R]
    (n : ℕ) (P : Fin n → R[X]) (hP : ∀ i, (P i).Monic) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S)
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : FaithfulSMul R S),
      ∀ i, ((P i).map (algebraMap R S)).Splits := by
  classical
  cases subsingleton_or_nontrivial R
  · refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
    intro i
    have hz : (P i).map (algebraMap R R) = 0 := Subsingleton.elim _ _
    rw [hz]
    exact Polynomial.Splits.zero
  · obtain ⟨S, _, _, _, _, _, hs⟩ := exists_nontrivial_splitting n R P hP
    exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hs⟩
